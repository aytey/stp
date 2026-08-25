/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#include "stp/ToSat/BVExactEncoder.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BitBlaster.h"
#include "stp/ToSat/ToCNFAIG.h"

#include <cassert>

namespace stp
{

namespace
{

// The abstraction, off for the length of one encoding.
//
// The blast below runs the ordinary BitBlaster, and the ordinary BitBlaster
// abstracts every wide multiplication it is handed. Left on, the circuit
// this is here to build would come back as another set of free bits and
// another record -- and the record would be minted against an AIG that is
// thrown away at the end of this function, so nothing could ever refine it.
// The refinement that reaches this point has already decided the
// abstraction is not paying; this is the encoding it decided in favour of.
struct AbstractionOff
{
  UserDefinedFlags& uf;
  const bool term;
  const bool eq;

  explicit AbstractionOff(UserDefinedFlags& uf_)
      : uf(uf_), term(uf_.bv_term_abstraction), eq(uf_.bv_eq_abstraction)
  {
    uf.bv_term_abstraction = false;
    uf.bv_eq_abstraction = false;
  }

  ~AbstractionOff()
  {
    uf.bv_term_abstraction = term;
    uf.bv_eq_abstraction = eq;
  }
};

// x <-> y
void addEquiv(SATSolver& solver, unsigned x, unsigned y)
{
  SATSolver::vec_literals cl;
  cl.clear();
  cl.push(SATSolver::mkLit(x, true));
  cl.push(SATSolver::mkLit(y, false));
  solver.addClause(cl);
  cl.clear();
  cl.push(SATSolver::mkLit(x, false));
  cl.push(SATSolver::mkLit(y, true));
  solver.addClause(cl);
}

// The same rewriting ToCNFAIG runs before its own CNF conversion, and under
// the same flag: an encoding that is meant to be the one the query would
// have had is not that if it is optimised differently. Off by default,
// which is why the mapping below is where the size actually comes from.
void rewrite(BBNodeManagerAIG& mgr, int64_t iterations)
{
  if (iterations <= 0)
    return;

  Dar_LibStart();
  Dar_RwrPar_t Pars;
  Dar_ManDefaultRwrParams(&Pars);

  for (int64_t i = 0; i < iterations; i++)
  {
    const int before = mgr.aigMgr->nObjs[AIG_OBJ_AND];

    Aig_Man_t* pTemp;
    mgr.aigMgr = Aig_ManDupDfs(pTemp = mgr.aigMgr);
    Aig_ManStop(pTemp);
    Dar_ManRewrite(mgr.aigMgr, &Pars);

    // Rewriting can leave an unreferenced AND node behind, which
    // Aig_ManDupDfs asserts about rather than copies; see the same call in
    // ToCNFAIG for the whole story.
    Aig_ManCleanup(mgr.aigMgr);
    mgr.aigMgr = Aig_ManDupDfs(pTemp = mgr.aigMgr);
    Aig_ManStop(pTemp);

    if (before == mgr.aigMgr->nObjs[AIG_OBJ_AND])
      break;
  }
}

} // namespace

// ---------------------------------------------------------------------------
// The facts, as values.
//
// Written over unsigned arithmetic on the bit vectors rather than over the
// circuits below, so that the test which checks the two against each other
// is checking two things and not one.
// ---------------------------------------------------------------------------

namespace
{

bool allZero(const std::vector<bool>& v)
{
  for (bool b : v)
    if (b)
      return false;
  return true;
}

bool allOnes(const std::vector<bool>& v)
{
  for (bool b : v)
    if (!b)
      return false;
  return true;
}

bool ule(const std::vector<bool>& a, const std::vector<bool>& b)
{
  for (int i = (int)a.size() - 1; i >= 0; --i)
    if (a[i] != b[i])
      return b[i];
  return true;
}

std::vector<bool> notOf(const std::vector<bool>& v)
{
  std::vector<bool> r(v.size());
  for (unsigned i = 0; i < v.size(); ++i)
    r[i] = !v[i];
  return r;
}

// Two's complement negation: the bitwise complement plus one.
std::vector<bool> negOf(const std::vector<bool>& v)
{
  std::vector<bool> r = notOf(v);
  bool carry = true;
  for (unsigned i = 0; i < r.size() && carry; ++i)
  {
    const bool sum = r[i] ^ carry;
    carry = r[i] && carry;
    r[i] = sum;
  }
  return r;
}

std::vector<bool> decOf(const std::vector<bool>& v)
{
  // v - 1, which is v + ~0.
  std::vector<bool> r(v.size());
  bool borrow = true;
  for (unsigned i = 0; i < v.size(); ++i)
  {
    r[i] = v[i] ^ borrow;
    borrow = !v[i] && borrow;
  }
  return r;
}

std::vector<bool> andOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  std::vector<bool> r(a.size());
  for (unsigned i = 0; i < a.size(); ++i)
    r[i] = a[i] && b[i];
  return r;
}

std::vector<bool> orOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  std::vector<bool> r(a.size());
  for (unsigned i = 0; i < a.size(); ++i)
    r[i] = a[i] || b[i];
  return r;
}

std::vector<bool> xorOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  std::vector<bool> r(a.size());
  for (unsigned i = 0; i < a.size(); ++i)
    r[i] = (a[i] != b[i]);
  return r;
}

std::vector<bool> addOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  std::vector<bool> r(a.size());
  bool carry = false;
  for (unsigned i = 0; i < a.size(); ++i)
  {
    r[i] = (a[i] != b[i]) != carry;
    carry = (a[i] && b[i]) || (carry && (a[i] || b[i]));
  }
  return r;
}

// The truncated product, as the abstraction's own result would hold it.
std::vector<bool> mulOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  const unsigned W = (unsigned)a.size();
  std::vector<bool> r(W, false);
  for (unsigned i = 0; i < W; ++i)
  {
    if (!a[i])
      continue;
    bool carry = false;
    for (unsigned j = 0; i + j < W; ++j)
    {
      const bool add = b[j];
      const bool sum = (r[i + j] != add) != carry;
      carry = (r[i + j] && add) || (carry && (r[i + j] || add));
      r[i + j] = sum;
    }
  }
  return r;
}

// How far a shift by the value `amt` actually moves, saturated at the width.
// Anything at or above the width clears the vector, which is what SMT-LIB
// says of both bvlshr and bvshl and what the circuits are built to match, so
// saturating is not an approximation -- it is the answer.
unsigned shiftBy(const std::vector<bool>& amt, unsigned W)
{
  unsigned long long by = 0;
  for (unsigned i = 0; i < W; ++i)
    if (amt[i])
    {
      if (i >= 64 || by > W)
        return W; // saturate rather than overflow
      by += (1ull << i);
      if (by > W)
        return W;
    }
  return (unsigned)by;
}

std::vector<bool> shrOf(const std::vector<bool>& v, const std::vector<bool>& amt)
{
  const unsigned W = (unsigned)v.size();
  const unsigned by = shiftBy(amt, W);

  std::vector<bool> r(W, false);
  for (unsigned i = 0; i + by < W; ++i)
    r[i] = v[i + by];
  return r;
}

std::vector<bool> shlOf(const std::vector<bool>& v, const std::vector<bool>& amt)
{
  const unsigned W = (unsigned)v.size();
  const unsigned by = shiftBy(amt, W);

  std::vector<bool> r(W, false);
  for (unsigned i = by; i < W; ++i)
    r[i] = v[i - by];
  return r;
}

} // namespace

// `s <=u x <u 2s`, with the doubling read in the integers rather than in the
// bit vector: a divisor whose top bit is set doubles past the width, so
// nothing can reach 2s and the second half of the premise is free.
//
// The premise carries `s != 0` inside it -- a zero divisor cannot be at most
// x and strictly above it at the same time -- so neither fact needs to say so.
static bool fitsExactlyOnce(const std::vector<bool>& x,
                            const std::vector<bool>& s)
{
  const unsigned W = (unsigned)x.size();
  std::vector<bool> one(W, false);
  one[0] = true;
  return ule(s, x) && (s[W - 1] || !ule(shlOf(s, one), x));
}

bool divLemmaHolds(DivLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  const unsigned W = (unsigned)x.size();
  const std::vector<bool> zero(W, false);
  std::vector<bool> one(W, false);
  one[0] = true;

  switch (lemma)
  {
    case DivLemma::DividendZero:
      return !(allZero(x) && !allZero(s)) || allZero(t);

    case DivLemma::DivisorEqualsDividend:
      return !(s == x && !allZero(s)) || t == one;

    case DivLemma::DivisorAllOnes:
      return !(allOnes(s) && !allOnes(x)) || allZero(t);

    case DivLemma::QuotientBelowNegatedDivisor:
    {
      std::vector<bool> sOr1 = s;
      sOr1[0] = true;
      return ule(t, negOf(sOr1));
    }

    case DivLemma::DividendAboveNegatedAnd:
      return ule(negOf(andOf(negOf(s), negOf(t))), x);

    case DivLemma::DivisorAboveShiftedDividend:
      return ule(shrOf(x, t), s);

    case DivLemma::DivisorLessOneAboveShiftedDividend:
      return ule(shrOf(x, t), decOf(s));

    case DivLemma::DividendAboveShiftedDoubleQuotient:
      // x >=u ((t << 1) >> (t << s))
      return ule(shrOf(shlOf(t, one), shlOf(t, s)), x);

    case DivLemma::QuotientNotNegatedAnd:
      // t != -(s & ~x)
      return t != negOf(andOf(s, notOf(x)));

    case DivLemma::DividendAboveDoubledShiftedDivisor:
      // x >=u ((s >> (s << t)) << 1)
      return ule(shlOf(shrOf(s, shlOf(s, t)), one), x);

    case DivLemma::DividendNotTwiceQuotientPlusOr:
      // x != t + t + (x | s)
      return x != addOf(t, addOf(t, orOf(x, s)));

    case DivLemma::QuotientAboveDoubledShiftedDividend:
      // t >=u ((x >> s) << 1)
      return ule(shlOf(shrOf(x, s), one), t);

    case DivLemma::DividendAboveOrAndDoubledDivisor:
      // x >=u ((x | t) & (s << 1))
      return ule(andOf(orOf(x, t), shlOf(s, one)), x);

    case DivLemma::MaskedDividendAboveDivisorAndQuotient:
      // (x & -t) >=u (s & t)
      return ule(andOf(s, t), andOf(x, negOf(t)));

    case DivLemma::DividendAboveQuotientXorShifted:
      // x >=u (t ^ (t >> (s >> 1)))
      return ule(xorOf(t, shrOf(t, shrOf(s, one))), x);

    case DivLemma::ShiftedDividendNotOr:
      // (x >> t) != (s | t)
      return shrOf(x, t) != orOf(s, t);

    case DivLemma::DividendAboveOrAndDoubledQuotient:
      // x >=u ((x | s) & (t << 1))
      return ule(andOf(orOf(x, s), shlOf(t, one)), x);

    case DivLemma::DividendAboveDivisorXorShifted:
      // x >=u (s ^ (s >> (t >> 1)))
      return ule(xorOf(s, shrOf(s, shrOf(t, one))), x);
  }
  return true;
}

unsigned divLemmaMinWidth(DivLemma lemma)
{
  // `x != t + t + (x | s)` is false at one bit: x = 1, s = 0 gives the
  // totalised quotient t = 1, and 1 + 1 + (1 | 0) is 1. Everything else here
  // is true at every width, checked exhaustively to eight bits.
  return (lemma == DivLemma::DividendNotTwiceQuotientPlusOr) ? 2 : 1;
}

const char* divLemmaName(DivLemma lemma)
{
  switch (lemma)
  {
    case DivLemma::DividendZero: return "dividend-zero";
    case DivLemma::DivisorEqualsDividend: return "divisor-equals-dividend";
    case DivLemma::DivisorAllOnes: return "divisor-all-ones";
    case DivLemma::QuotientBelowNegatedDivisor:
      return "quotient-below-negated-divisor";
    case DivLemma::DividendAboveNegatedAnd:
      return "dividend-above-negated-and";
    case DivLemma::DivisorAboveShiftedDividend:
      return "divisor-above-shifted-dividend";
    case DivLemma::DivisorLessOneAboveShiftedDividend:
      return "divisor-less-one-above-shifted-dividend";
    case DivLemma::DividendAboveShiftedDoubleQuotient:
      return "dividend-above-shifted-double-quotient";
    case DivLemma::QuotientNotNegatedAnd:
      return "quotient-not-negated-and";
    case DivLemma::DividendAboveDoubledShiftedDivisor:
      return "dividend-above-doubled-shifted-divisor";
    case DivLemma::DividendNotTwiceQuotientPlusOr:
      return "dividend-not-twice-quotient-plus-or";
    case DivLemma::QuotientAboveDoubledShiftedDividend:
      return "quotient-above-doubled-shifted-dividend";
    case DivLemma::DividendAboveOrAndDoubledDivisor:
      return "dividend-above-or-and-doubled-divisor";
    case DivLemma::MaskedDividendAboveDivisorAndQuotient:
      return "masked-dividend-above-divisor-and-quotient";
    case DivLemma::DividendAboveQuotientXorShifted:
      return "dividend-above-quotient-xor-shifted";
    case DivLemma::ShiftedDividendNotOr:
      return "shifted-dividend-not-or";
    case DivLemma::DividendAboveOrAndDoubledQuotient:
      return "dividend-above-or-and-doubled-quotient";
    case DivLemma::DividendAboveDivisorXorShifted:
      return "dividend-above-divisor-xor-shifted";
  }
  return "unknown";
}

bool remLemmaHolds(RemLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  const unsigned W = (unsigned)x.size();
  const std::vector<bool> zero(W, false);
  std::vector<bool> one(W, false);
  one[0] = true;

  switch (lemma)
  {
    case RemLemma::DividendZero:
      // x = 0 -> t = 0
      return !allZero(x) || allZero(t);

    case RemLemma::DivisorEqualsDividend:
      // s = x -> t = 0
      return s != x || allZero(t);

    case RemLemma::DividendBelowDivisor:
      // x <u s -> t = x
      return ule(s, x) || t == x;

    case RemLemma::DividendWithinDivisorOrRemainder:
      // x = x & (s | t | -s)
      return x == andOf(x, orOf(s, orOf(t, negOf(s))));

    case RemLemma::DividendAboveRemainderOrAnd:
      // x >=u (t | (x & s))
      return ule(orOf(t, andOf(x, s)), x);

    case RemLemma::RemainderOutsideOperandsNotOne:
      // (t & ~(x | s)) != 1
      return andOf(t, notOf(orOf(x, s))) != one;

    case RemLemma::RemainderNotOrOfComplements:
      // t != (~x | -s)
      return t != orOf(notOf(x), negOf(s));

    case RemLemma::RemainderInOperandsAboveLowBit:
      // (t & (x | s)) >=u (t & 1)
      return ule(andOf(t, one), andOf(t, orOf(x, s)));

    case RemLemma::DividendNotOrOfNegations:
      // x != (-x | -(~t))
      return x != orOf(negOf(x), negOf(notOf(t)));

    case RemLemma::DifferenceAboveRemainder:
      // (x - s) >=u t
      return ule(t, addOf(x, negOf(s)));

    case RemLemma::XorAboveRemainder:
      // ((-s) ^ (x | s)) >=u t
      return ule(t, xorOf(negOf(s), orOf(x, s)));

    case RemLemma::RemainderIsDifference:
      // s <=u x <u 2s -> t = x - s
      return !fitsExactlyOnce(x, s) || t == addOf(x, negOf(s));
  }
  return true;
}

unsigned remLemmaMinWidth(RemLemma lemma)
{
  // `x != (-x | -(~t))` is false at one and two bits -- at two, x = 2 over
  // s = 3 leaves the remainder t = 2, and -2 | -(~2) is 2. Everything else
  // here is true at every width, checked exhaustively to eight bits.
  return (lemma == RemLemma::DividendNotOrOfNegations) ? 3 : 1;
}

const char* remLemmaName(RemLemma lemma)
{
  switch (lemma)
  {
    case RemLemma::DividendZero: return "dividend-zero";
    case RemLemma::DivisorEqualsDividend: return "divisor-equals-dividend";
    case RemLemma::DividendBelowDivisor: return "dividend-below-divisor";
    case RemLemma::DividendWithinDivisorOrRemainder:
      return "dividend-within-divisor-or-remainder";
    case RemLemma::DividendAboveRemainderOrAnd:
      return "dividend-above-remainder-or-and";
    case RemLemma::RemainderOutsideOperandsNotOne:
      return "remainder-outside-operands-not-one";
    case RemLemma::RemainderNotOrOfComplements:
      return "remainder-not-or-of-complements";
    case RemLemma::RemainderInOperandsAboveLowBit:
      return "remainder-in-operands-above-low-bit";
    case RemLemma::DividendNotOrOfNegations:
      return "dividend-not-or-of-negations";
    case RemLemma::DifferenceAboveRemainder:
      return "difference-above-remainder";
    case RemLemma::XorAboveRemainder: return "xor-above-remainder";
    case RemLemma::RemainderIsDifference: return "remainder-is-difference";
  }
  return "unknown";
}

bool mulLemmaHolds(MulLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  const unsigned W = (unsigned)x.size();
  std::vector<bool> one(W, false);
  one[0] = true;

  switch (lemma)
  {
    case MulLemma::FactorUnchangedByMaskedShift:
      // s = s << (x & (1 >> t))
      return s == shlOf(s, andOf(x, shrOf(one, t)));

    case MulLemma::FactorAndProductNotOr:
      // (x & t) != (s | ~t)
      return andOf(x, t) != orOf(s, notOf(t));
  }
  return true;
}

unsigned mulLemmaMinWidth(MulLemma lemma)
{
  // `(x & t) != (s | ~t)` is false at one bit, where the product is the
  // conjunction and x = s = t = 1 satisfies both sides. It is true at every
  // width above, checked exhaustively to eight bits.
  return (lemma == MulLemma::FactorAndProductNotOr) ? 2 : 1;
}

bool divModIdentityHolds(const std::vector<bool>& x,
                         const std::vector<bool>& s,
                         const std::vector<bool>& t,
                         const std::vector<bool>& r)
{
  // x = t*s + r
  return x == addOf(mulOf(t, s), r);
}

const char* mulLemmaName(MulLemma lemma)
{
  switch (lemma)
  {
    case MulLemma::FactorUnchangedByMaskedShift:
      return "factor-unchanged-by-masked-shift";
    case MulLemma::FactorAndProductNotOr:
      return "factor-and-product-not-or";
  }
  return "unknown";
}

namespace
{

// The splice, which is the same for every fact there is: build the circuit
// over three vectors of free inputs, hand the AIG to the CNF conversion the
// query itself uses, and rename the CNF's variables to the ones the operands
// and the abstraction's result are already carried by. What differs between
// one fact and the next is `build`, and only that.
template <typename Build>
void spliceLemma(STPMgr* bm, SATSolver& solver, unsigned width,
                 const std::vector<const std::vector<unsigned>*>& groups,
                 Build build)
{
  for (const std::vector<unsigned>* g : groups)
  {
    (void)g;
    assert(g->size() >= width);
  }

  AbstractionOff scope(bm->UserFlags);

  BBNodeManagerAIG mgr;
  mgr.nodeBudget = bm->UserFlags.aig_node_budget;
  SubstitutionMap sm(bm);
  Simplifier simp(bm, &sm);
  BitBlaster bb(&mgr, &simp, bm->defaultNodeFactory, &bm->UserFlags);

  // The input vectors, in the order the splice reads them back: the two
  // operands, then whichever abstracted results the fact is about. A result
  // is an input here and not an output -- the fact constrains it without
  // defining it, which is the whole difference from `encode`.
  std::vector<BBNodeVec> ins(groups.size(), BBNodeVec(width));
  for (unsigned v = 0; v < ins.size(); v++)
    for (unsigned i = 0; i < width; i++)
    {
      ins[v][i] = BBNodeAIG(Aig_ObjCreateCi(mgr.aigMgr));
      ins[v][i].symbol_index = mgr.aigMgr->vCis->nSize - 1;
    }

  BBNodeSet support;
  const BBNodeAIG claim = build(bb, ins, support);

  Aig_ObjCreateCo(mgr.aigMgr, claim.n);
  for (const BBNodeAIG& c : support)
    Aig_ObjCreateCo(mgr.aigMgr, c.n);

  const unsigned outputs = 1 + (unsigned)support.size();

  rewrite(mgr, bm->UserFlags.AIG_rewrites_iterations);
  assert(Aig_ManCheck(mgr.aigMgr));
  assert((unsigned)Aig_ManCoNum(mgr.aigMgr) == outputs);

  Cnf_Dat_t* cnf = ToCNFAIG(bm->UserFlags).derive_cnf(mgr, outputs);
  assert(cnf != NULL);

  std::vector<unsigned> cnfToSolver(cnf->nVars, ~((unsigned)0));
  for (unsigned i = 0; i < groups.size() * width; i++)
  {
    const int var = cnf->pVarNums[Aig_ManCi(mgr.aigMgr, (int)i)->Id];
    // An input the circuit never reads is given no variable, and needs
    // none: nothing the CNF says mentions it.
    if (var < 0)
      continue;
    cnfToSolver[var] = (*groups[i / width])[i % width];
  }

  for (int var = 0; var < cnf->nVars; var++)
    if (cnfToSolver[var] == ~((unsigned)0))
    {
      const unsigned fresh = solver.newVar();
      solver.setFrozen(fresh);
      cnfToSolver[var] = fresh;
    }

  SATSolver::vec_literals cl;
  for (int i = 0; i < cnf->nClauses; i++)
  {
    cl.clear();
    for (int *pLit = cnf->pClauses[i], *pStop = cnf->pClauses[i + 1];
         pLit < pStop; pLit++)
      cl.push(SATSolver::mkLit(cnfToSolver[(*pLit) >> 1], ((*pLit) & 1) != 0));
    solver.addClause(cl);
  }

  // Every output is asserted: the claim itself, and whatever the circuit
  // wanted conjoined to it.
  for (unsigned i = 0; i < outputs; i++)
  {
    const unsigned var =
        cnfToSolver[cnf->pVarNums[Aig_ManCo(mgr.aigMgr, (int)i)->Id]];
    cl.clear();
    cl.push(SATSolver::mkLit(var, false));
    solver.addClause(cl);
  }

  Cnf_DataFree(cnf);
}

} // namespace

void BVExactEncoder::encodeDivLemma(SATSolver& solver, DivLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& dividendVars,
                                    const std::vector<unsigned>& divisorVars,
                                    const std::vector<unsigned>& resultVars)
{
  spliceLemma(bm, solver, width, {&dividendVars, &divisorVars, &resultVars},
              [lemma](BitBlaster& bb, const std::vector<BBNodeVec>& in,
                      BBNodeSet& support) {
                return bb.BBDivLemma(lemma, in[0], in[1], in[2], support);
              });
}

void BVExactEncoder::encodeRemLemma(SATSolver& solver, RemLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& dividendVars,
                                    const std::vector<unsigned>& divisorVars,
                                    const std::vector<unsigned>& resultVars)
{
  spliceLemma(bm, solver, width, {&dividendVars, &divisorVars, &resultVars},
              [lemma](BitBlaster& bb, const std::vector<BBNodeVec>& in,
                      BBNodeSet& support) {
                return bb.BBRemLemma(lemma, in[0], in[1], in[2], support);
              });
}

void BVExactEncoder::encodeMulLemma(SATSolver& solver, MulLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& xVars,
                                    const std::vector<unsigned>& sVars,
                                    const std::vector<unsigned>& resultVars)
{
  spliceLemma(bm, solver, width, {&xVars, &sVars, &resultVars},
              [lemma](BitBlaster& bb, const std::vector<BBNodeVec>& in,
                      BBNodeSet& support) {
                return bb.BBMulLemma(lemma, in[0], in[1], in[2], support);
              });
}

void BVExactEncoder::encodeDivModIdentity(
    SATSolver& solver, const ASTNode& product, unsigned width,
    const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& divisorVars,
    const std::vector<unsigned>& quotientVars,
    const std::vector<unsigned>& remainderVars)
{
  spliceLemma(bm, solver, width,
              {&dividendVars, &divisorVars, &quotientVars, &remainderVars},
              [&product](BitBlaster& bb, const std::vector<BBNodeVec>& in,
                         BBNodeSet& support) {
                return bb.BBDivModIdentity(product, in[0], in[1], in[2], in[3],
                                           support);
              });
}

void BVExactEncoder::encode(SATSolver& solver, const ASTNode& term,
                            unsigned width,
                            const std::vector<unsigned>& aVars,
                            const std::vector<unsigned>& bVars,
                            const std::vector<unsigned>& resultVars)
{
  assert(aVars.size() >= width);
  assert(bVars.size() >= width);
  assert(resultVars.size() >= width);

  AbstractionOff scope(bm->UserFlags);

  BBNodeManagerAIG mgr;
  mgr.nodeBudget = bm->UserFlags.aig_node_budget;
  SubstitutionMap sm(bm);
  Simplifier simp(bm, &sm);
  // No constant-bit propagation: its results belong to the blast that ran
  // over the whole query, and this one is a fragment of it. The multiplier
  // asks for them only through statsFound(), which answers no without it.
  BitBlaster bb(&mgr, &simp, bm->defaultNodeFactory, &bm->UserFlags);

  // The operand bits, as combinational inputs, in the order the splice
  // below reads them back: the first operand's `width` bits, then the
  // second's. Nothing else creates an input, so their positions are their
  // indices for the whole of this function -- which is what makes them
  // findable after ABC has renumbered every object in the manager.
  BBNodeVec x(width), y(width);
  for (unsigned i = 0; i < width; i++)
  {
    x[i] = BBNodeAIG(Aig_ObjCreateCi(mgr.aigMgr));
    x[i].symbol_index = mgr.aigMgr->vCis->nSize - 1;
  }
  for (unsigned i = 0; i < width; i++)
  {
    y[i] = BBNodeAIG(Aig_ObjCreateCi(mgr.aigMgr));
    y[i].symbol_index = mgr.aigMgr->vCis->nSize - 1;
  }

  BBNodeSet support;
  const BBNodeVec result = bb.BBExactBinaryOp(term, x, y, support);
  assert(result.size() == width);

  // Outputs, then whatever the circuit wants conjoined to the top. Both are
  // combinational outputs and all of them are given CNF variables -- ABC's
  // generator asserts every output it is not asked to name, and it can only
  // be asked for all of them or none -- so the support is asserted below by
  // a unit clause over the variable it comes back with.
  for (unsigned i = 0; i < width; i++)
    Aig_ObjCreateCo(mgr.aigMgr, result[i].n);
  for (const BBNodeAIG& s : support)
    Aig_ObjCreateCo(mgr.aigMgr, s.n);

  const unsigned outputs = width + (unsigned)support.size();

  rewrite(mgr, bm->UserFlags.AIG_rewrites_iterations);
  assert(Aig_ManCheck(mgr.aigMgr));
  assert((unsigned)Aig_ManCoNum(mgr.aigMgr) == outputs);
  assert((unsigned)Aig_ManCiNum(mgr.aigMgr) == 2 * width);

  // Use the query's selected CNF strategy. All outputs are named rather than
  // asserted because the splice below connects each result bit explicitly
  // and asserts only the side constraints.
  Cnf_Dat_t* cnf = ToCNFAIG(bm->UserFlags, /*allowAuto=*/false).derive_cnf(mgr, outputs);
  assert(cnf != NULL);

  // The splice. Every variable of the derived CNF becomes a variable of the
  // live solver: the inputs become the ones the operands are already
  // carried by, and everything else becomes a fresh one. Reusing the
  // operands' own variables rather than minting a copy and equating it is
  // the whole point -- the clauses have to talk about the bits the rest of
  // the query talks about.
  std::vector<unsigned> cnfToSolver(cnf->nVars, ~((unsigned)0));

  for (unsigned i = 0; i < 2 * width; i++)
  {
    const int var = cnf->pVarNums[Aig_ManCi(mgr.aigMgr, (int)i)->Id];
    // An input the circuit never reads is given no variable, and needs
    // none: nothing the CNF says mentions it.
    if (var < 0)
      continue;
    cnfToSolver[var] = (i < width) ? aVars[i] : bVars[i - width];
  }

  for (int var = 0; var < cnf->nVars; var++)
    if (cnfToSolver[var] == ~((unsigned)0))
    {
      const unsigned fresh = solver.newVar();
      solver.setFrozen(fresh);
      cnfToSolver[var] = fresh;
    }

  SATSolver::vec_literals cl;
  for (int i = 0; i < cnf->nClauses; i++)
  {
    cl.clear();
    for (int *pLit = cnf->pClauses[i], *pStop = cnf->pClauses[i + 1];
         pLit < pStop; pLit++)
      cl.push(SATSolver::mkLit(cnfToSolver[(*pLit) >> 1], ((*pLit) & 1) != 0));
    solver.addClause(cl);
  }

  for (unsigned i = 0; i < outputs; i++)
  {
    const unsigned var =
        cnfToSolver[cnf->pVarNums[Aig_ManCo(mgr.aigMgr, (int)i)->Id]];
    if (i < width)
    {
      addEquiv(solver, resultVars[i], var);
      continue;
    }
    cl.clear();
    cl.push(SATSolver::mkLit(var, false));
    solver.addClause(cl);
  }

  Cnf_DataFree(cnf);
}

} // namespace stp
