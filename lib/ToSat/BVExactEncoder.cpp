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

std::vector<bool> subOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  return addOf(a, negOf(b));
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

    case DivLemma::QuotientIsOne:
      // s <=u x <u 2s -> t = 1
      return !fitsExactlyOnce(x, s) || t == one;

    case DivLemma::Udiv10:
      // (s | t) != (x & ~1)
      return orOf(s, t) != andOf(x, notOf(one));

    case DivLemma::Udiv11:
    {
      // (s | 1) != (x & ~t)
      std::vector<bool> sOr1 = s;
      sOr1[0] = true;
      return sOr1 != andOf(x, notOf(t));
    }

    case DivLemma::Udiv20:
      // s != ~(s >> (t >> 1))
      return s != notOf(shrOf(s, shrOf(t, one)));

    case DivLemma::Udiv21:
      // x != ~(x & (t << 1))
      return x != notOf(andOf(x, shlOf(t, one)));

    case DivLemma::Udiv22:
      // t >=u ((x << 1) >> s)
      return ule(shrOf(shlOf(x, one), s), t);

    case DivLemma::Udiv23:
      // x >=u (s << ~(x | t))
      return ule(shlOf(s, notOf(orOf(x, t))), x);

    case DivLemma::Udiv24:
      // x >=u (t << ~(x | s))
      return ule(shlOf(t, notOf(orOf(x, s))), x);

    case DivLemma::Udiv27:
      // x >=u (s << ~(x ^ t))
      return ule(shlOf(s, notOf(xorOf(x, t))), x);

    case DivLemma::Udiv28:
      // x >=u (t << ~(x ^ s))
      return ule(shlOf(t, notOf(xorOf(x, s))), x);

    case DivLemma::Udiv29:
      // x != t + (s | (x + s))
      return x != addOf(t, orOf(s, addOf(x, s)));

    case DivLemma::Udiv30:
      // x != t + (1 + (1 << x))
      return x != addOf(t, addOf(one, shlOf(one, x)));

    case DivLemma::Udiv31:
      // s >=u ((x + t) >> t)
      return ule(shrOf(addOf(x, t), t), s);

    case DivLemma::Udiv33:
      // (s ^ (x | t)) >=u (t ^ 1)
      return ule(xorOf(t, one), xorOf(s, orOf(x, t)));

    case DivLemma::Udiv34:
      // t >=u (x >> (s - 1))
      return ule(shrOf(x, decOf(s)), t);

    case DivLemma::Udiv36:
      // x != 1 - (x << (x - t))
      return x != subOf(one, shlOf(x, subOf(x, t)));
  }
  return true;
}

bool divLemmaApplicable(DivLemma lemma, unsigned width)
{
  switch (lemma)
  {
    // `x != t + t + (x | s)` is false at one bit: x = 1, s = 0 gives the
    // totalised quotient t = 1, and 1 + 1 + (1 | 0) is 1.
    case DivLemma::DividendNotTwiceQuotientPlusOr:
    // `x != ~(x & (t << 1))` is false at one bit: x = 1 over s = 1 gives
    // t = 1, `t << 1` clears, and ~(1 & 0) is 1.
    case DivLemma::Udiv21:
      return width > 1;

    // `x != t + (1 + (1 << x))` is false at one and two bits.
    case DivLemma::Udiv30:
      return width > 2;

    // The one restriction that is not a minimum. At two bits x = 1 over
    // s = 0 gives the totalised quotient t = 3, so `x - t` is 2, the shift
    // clears the vector, and `1 - 0` is the x the fact says it is not. At
    // one bit and at three and above it is true, so a minimum of three
    // would give up a width the fact is good for -- and the sweep in
    // BVAbstractionLemma_Test would not notice, because it only ever looks
    // upward from what is declared here.
    case DivLemma::Udiv36:
      return width != 2;

    // Everything else is true at every width, checked exhaustively to eight
    // bits. A fact added here and forgotten is claimed at every width, and
    // the sweep is what catches it.
    default:
      return true;
  }
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
    case DivLemma::QuotientIsOne: return "quotient-is-one";
    case DivLemma::Udiv10: return "udiv10";
    case DivLemma::Udiv11: return "udiv11";
    case DivLemma::Udiv20: return "udiv20";
    case DivLemma::Udiv21: return "udiv21";
    case DivLemma::Udiv22: return "udiv22";
    case DivLemma::Udiv23: return "udiv23";
    case DivLemma::Udiv24: return "udiv24";
    case DivLemma::Udiv27: return "udiv27";
    case DivLemma::Udiv28: return "udiv28";
    case DivLemma::Udiv29: return "udiv29";
    case DivLemma::Udiv30: return "udiv30";
    case DivLemma::Udiv31: return "udiv31";
    case DivLemma::Udiv33: return "udiv33";
    case DivLemma::Udiv34: return "udiv34";
    case DivLemma::Udiv36: return "udiv36";
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

    case RemLemma::Urem7:
      // ~(-s) >=u t
      return ule(t, notOf(negOf(s)));
  }
  return true;
}

bool remLemmaApplicable(RemLemma lemma, unsigned width)
{
  // `x != (-x | -(~t))` is false at one and two bits -- at two, x = 2 over
  // s = 3 leaves the remainder t = 2, and -2 | -(~2) is 2. Everything else
  // here is true at every width, checked exhaustively to eight bits.
  return lemma != RemLemma::DividendNotOrOfNegations || width > 2;
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
    case RemLemma::Urem7: return "urem7";
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

    case MulLemma::Mul5:
      // s != ~(t | (1 & (x | s)))
      return s != notOf(orOf(t, andOf(one, orOf(x, s))));

    case MulLemma::Mul7:
    {
      // t != ((s | 1) << (t << x))
      std::vector<bool> sOr1 = s;
      sOr1[0] = true;
      return t != shlOf(sOr1, shlOf(t, x));
    }

    case MulLemma::Mul9:
      // t >=u (1 & ((x & s) >> 1))
      return ule(andOf(one, shrOf(andOf(x, s), one)), t);

    case MulLemma::Mul10:
      // x != (1 ^ (x << (s ^ t)))
      return x != xorOf(one, shlOf(x, xorOf(s, t)));

    case MulLemma::Mul11:
      // t != (1 | ~(x ^ s))
      return t != orOf(one, notOf(xorOf(x, s)));

    case MulLemma::Mul12:
      // t != (~1 | (x ^ s))
      return t != orOf(notOf(one), xorOf(x, s));

    case MulLemma::Mul13:
      // x != (x << (s + t)) - 1
      return x != subOf(shlOf(x, addOf(s, t)), one);

    case MulLemma::Mul14:
      // x != 1 - (x << (s - t))
      return x != subOf(one, shlOf(x, subOf(s, t)));

    case MulLemma::Mul15:
      // s != 1 + (s << (t - x))
      return s != addOf(one, shlOf(s, subOf(t, x)));

    case MulLemma::Mul16:
      // s != 1 - (s << (t - x))
      return s != subOf(one, shlOf(s, subOf(t, x)));

    case MulLemma::Mul17:
      // s != 1 + (s << (x - t))
      return s != addOf(one, shlOf(s, subOf(x, t)));

    case MulLemma::Mul18:
      // t != (1 | (x + s))
      return t != orOf(one, addOf(x, s));

    case MulLemma::Mul19:
      // x != ~(x << (s + t))
      return x != notOf(shlOf(x, addOf(s, t)));
  }
  return true;
}

bool mulLemmaApplicable(MulLemma lemma, unsigned width)
{
  switch (lemma)
  {
    // `(x & t) != (s | ~t)` is false at one bit, where the product is the
    // conjunction and x = s = t = 1 satisfies both sides. The four below it
    // are the source's other one-bit exclusions.
    case MulLemma::FactorAndProductNotOr:
    case MulLemma::Mul5:
    case MulLemma::Mul7:
    case MulLemma::Mul11:
    case MulLemma::Mul12:
    case MulLemma::Mul18:
      return width > 1;

    // `t >=u (1 & ((x & s) >> 1))` is the product side's one restriction
    // that is not a minimum: true at one bit, false at two, true above.
    case MulLemma::Mul9:
      return width != 2;

    default:
      return true;
  }
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
    case MulLemma::Mul5: return "mul5";
    case MulLemma::Mul7: return "mul7";
    case MulLemma::Mul9: return "mul9";
    case MulLemma::Mul10: return "mul10";
    case MulLemma::Mul11: return "mul11";
    case MulLemma::Mul12: return "mul12";
    case MulLemma::Mul13: return "mul13";
    case MulLemma::Mul14: return "mul14";
    case MulLemma::Mul15: return "mul15";
    case MulLemma::Mul16: return "mul16";
    case MulLemma::Mul17: return "mul17";
    case MulLemma::Mul18: return "mul18";
    case MulLemma::Mul19: return "mul19";
  }
  return "unknown";
}

bool addLemmaApplicable(AddLemma lemma, unsigned width)
{
  switch (lemma)
  {
    // `1 != (t | ~(x & s))` and `1 != (x | s | ~t)` are false at one and two
    // bits, where the vector "1" and the vector "~0" are close enough
    // together for the disjunction to reach it.
    case AddLemma::AddRef10:
    case AddLemma::AddRef12:
      return width > 2;

    // `t != ~(t | (x & s))` is false at one bit.
    case AddLemma::AddRef11:
      return width > 1;

    default:
      return true;
  }
}

bool addLemmaHolds(AddLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  const unsigned W = (unsigned)x.size();
  const std::vector<bool> zero(W, false);
  std::vector<bool> ones(W, true);
  std::vector<bool> one(W, false);
  one[0] = true;

  switch (lemma)
  {
    case AddLemma::AddZero:
      // s = 0 -> t = x
      return !allZero(s) || t == x;

    case AddLemma::AddSame:
      // x = s -> t[0] = 0
      return x != s || !t[0];

    case AddLemma::AddInv:
      // s = ~x -> t = ~0
      return s != notOf(x) || t == ones;

    case AddLemma::AddOverflow:
      // msb(x) = msb(s) = 1 -> t <u (x & s)
      return !(x[W - 1] && s[W - 1]) || !ule(andOf(x, s), t);

    case AddLemma::AddNoOverflow:
      // msb(x) = msb(s) = 0 -> t >=u (x | s)
      return x[W - 1] || s[W - 1] || ule(orOf(x, s), t);

    case AddLemma::AddOr:
      // x & s = 0 -> t = x | s
      return !allZero(andOf(x, s)) || t == orOf(x, s);

    case AddLemma::AddRef6:
      // 0 = x & s & t & 1
      return zero == andOf(x, andOf(s, andOf(t, one)));

    case AddLemma::AddRef7:
      // (1 & (s | t)) >=u (x & 1)
      return ule(andOf(x, one), andOf(one, orOf(s, t)));

    case AddLemma::AddRef8:
      // (1 & (x | t)) >=u (s & 1)
      return ule(andOf(s, one), andOf(one, orOf(x, t)));

    case AddLemma::AddRef9:
      // (1 & (x | s)) >=u (t & 1)
      return ule(andOf(t, one), andOf(one, orOf(x, s)));

    case AddLemma::AddRef10:
      // 1 != (t | ~(x & s))
      return one != orOf(t, notOf(andOf(x, s)));

    case AddLemma::AddRef11:
      // t != ~(t | (x & s))
      return t != notOf(orOf(t, andOf(x, s)));

    case AddLemma::AddRef12:
      // 1 != (x | s | ~t)
      return one != orOf(x, orOf(s, notOf(t)));
  }
  return true;
}

const char* addLemmaName(AddLemma lemma)
{
  switch (lemma)
  {
    case AddLemma::AddZero: return "add-zero";
    case AddLemma::AddSame: return "add-same";
    case AddLemma::AddInv: return "add-inv";
    case AddLemma::AddOverflow: return "add-overflow";
    case AddLemma::AddNoOverflow: return "add-no-overflow";
    case AddLemma::AddOr: return "add-or";
    case AddLemma::AddRef6: return "add-ref6";
    case AddLemma::AddRef7: return "add-ref7";
    case AddLemma::AddRef8: return "add-ref8";
    case AddLemma::AddRef9: return "add-ref9";
    case AddLemma::AddRef10: return "add-ref10";
    case AddLemma::AddRef11: return "add-ref11";
    case AddLemma::AddRef12: return "add-ref12";
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

void BVExactEncoder::encodeAddLemma(SATSolver& solver, AddLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& xVars,
                                    const std::vector<unsigned>& sVars,
                                    const std::vector<unsigned>& resultVars,
                                    bool xNegated, bool sNegated)
{
  spliceLemma(bm, solver, width, {&xVars, &sVars, &resultVars},
              [lemma, xNegated, sNegated](BitBlaster& bb,
                                          const std::vector<BBNodeVec>& in,
                                          BBNodeSet& support) {
                return bb.BBAddLemma(lemma, in[0], in[1], in[2], xNegated,
                                     sNegated, support);
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
