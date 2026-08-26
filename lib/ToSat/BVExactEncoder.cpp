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
#include <limits>

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
    r[i] = a[i] != b[i];
  return r;
}

std::vector<bool> addOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  std::vector<bool> r(a.size());
  bool carry = false;
  for (unsigned i = 0; i < a.size(); ++i)
  {
    r[i] = (a[i] != b[i]) != carry;
    carry = (a[i] && b[i]) || (a[i] && carry) || (b[i] && carry);
  }
  return r;
}

std::vector<bool> subOf(const std::vector<bool>& a, const std::vector<bool>& b)
{
  return addOf(a, negOf(b));
}

// The unsigned value of a shift amount, saturated at the value width. Once
// the represented amount reaches that width both SMT-LIB logical shifts are
// all zero, so there is no reason to risk overflowing a host integer while
// reading the remaining high bits.
unsigned saturatedShiftAmount(const std::vector<bool>& amount, unsigned width)
{
  unsigned by = 0;
  for (unsigned i = 0; i < amount.size(); ++i)
    if (amount[i])
    {
      if (i >= std::numeric_limits<unsigned>::digits)
        return width;
      const unsigned add = 1u << i;
      if (add >= width || by >= width - add)
        return width;
      by += add;
    }
  return by;
}

// Logical shifts by the value `amount` holds. A shift at or past the width
// clears the vector, matching both SMT-LIB operations and the barrel shifters
// the circuit uses.
std::vector<bool> shrOf(const std::vector<bool>& v,
                        const std::vector<bool>& amount)
{
  const unsigned W = (unsigned)v.size();
  const unsigned by = saturatedShiftAmount(amount, W);

  std::vector<bool> r(W, false);
  for (unsigned i = 0; i + by < W; ++i)
    r[i] = v[i + by];
  return r;
}

std::vector<bool> shlOf(const std::vector<bool>& v,
                        const std::vector<bool>& amount)
{
  const unsigned W = (unsigned)v.size();
  const unsigned by = saturatedShiftAmount(amount, W);

  std::vector<bool> r(W, false);
  for (unsigned i = by; i < W; ++i)
    r[i] = v[i - by];
  return r;
}

// `s <=u x <u 2s`, with doubling interpreted in the integers. If the top
// bit of s is set, 2s lies beyond the bit-vector range and the upper half of
// the premise is automatically true. The premise also excludes s = 0.
bool fitsExactlyOnce(const std::vector<bool>& x,
                     const std::vector<bool>& s)
{
  const unsigned W = (unsigned)x.size();
  std::vector<bool> one(W, false);
  one[0] = true;
  return ule(s, x) && (s[W - 1] || !ule(shlOf(s, one), x));
}

} // namespace

bool divLemmaApplicable(DivLemma lemma, unsigned width)
{
  switch (lemma)
  {
    case DivLemma::UdivRef21:
    case DivLemma::DividendNotTwiceQuotientPlusOr:
      return width > 1;
    case DivLemma::UdivRef31: return width > 2;
    case DivLemma::UdivRef38: return width != 2;
    default: return width > 0;
  }
}

bool divLemmaHolds(DivLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  assert(x.size() == s.size());
  assert(x.size() == t.size());

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

    case DivLemma::MaskedDividendAboveDivisorAndQuotient:
      // (x & -t) >=u (s & t)
      return ule(andOf(s, t), andOf(x, negOf(t)));

    case DivLemma::DividendAboveDoubledShiftedDivisor:
      // x >=u ((s >> (s << t)) << 1)
      return ule(shlOf(shrOf(s, shlOf(s, t)), one), x);

    case DivLemma::QuotientAboveDoubledShiftedDividend:
      // t >=u ((x >> s) << 1)
      return ule(shlOf(shrOf(x, s), one), t);

    case DivLemma::DividendAboveOrAndDoubledDivisor:
      // x >=u ((x | t) & (s << 1))
      return ule(andOf(orOf(x, t), shlOf(s, one)), x);

    case DivLemma::DividendAboveOrAndDoubledQuotient:
      // x >=u ((x | s) & (t << 1))
      return ule(andOf(orOf(x, s), shlOf(t, one)), x);

    case DivLemma::ShiftedDividendNotOr:
      // (x >> t) != (s | t)
      return shrOf(x, t) != orOf(s, t);

    case DivLemma::DividendAboveQuotientXorShifted:
      // x >=u (t xor (t >> (s >> 1)))
      return ule(xorOf(t, shrOf(t, shrOf(s, one))), x);

    case DivLemma::DividendAboveDivisorXorShifted:
      // x >=u (s xor (s >> (t >> 1)))
      return ule(xorOf(s, shrOf(s, shrOf(t, one))), x);

    case DivLemma::DividendNotTwiceQuotientPlusOr:
      // x != t + t + (x | s)
      return x != addOf(t, addOf(t, orOf(x, s)));

    case DivLemma::QuotientIsOne:
      // s <=u x <u 2s -> t = 1
      return !fitsExactlyOnce(x, s) || t == one;

    case DivLemma::UdivRef10:
      // (s | t) != (x & ~1)
      return orOf(s, t) != andOf(x, notOf(one));

    case DivLemma::UdivRef11:
      // (s | 1) != (x & ~t)
    {
      std::vector<bool> sOrOne = s;
      sOrOne[0] = true;
      return sOrOne != andOf(x, notOf(t));
    }

    case DivLemma::UdivRef20:
      // s != ~(s >> (t >> 1))
      return s != notOf(shrOf(s, shrOf(t, one)));

    case DivLemma::UdivRef21:
      // x != ~(x & (t << 1))
      return x != notOf(andOf(x, shlOf(t, one)));

    case DivLemma::UdivRef23:
      // t >=u ((x << 1) >> s)
      return ule(shrOf(shlOf(x, one), s), t);

    case DivLemma::UdivRef24:
      // x >=u (s << ~(x | t))
      return ule(shlOf(s, notOf(orOf(x, t))), x);

    case DivLemma::UdivRef25:
      // x >=u (t << ~(x | s))
      return ule(shlOf(t, notOf(orOf(x, s))), x);

    case DivLemma::UdivRef28:
      // x >=u (s << ~(x xor t))
      return ule(shlOf(s, notOf(xorOf(x, t))), x);

    case DivLemma::UdivRef29:
      // x >=u (t << ~(x xor s))
      return ule(shlOf(t, notOf(xorOf(x, s))), x);

    case DivLemma::UdivRef30:
      // x != t + (s | (x + s))
      return x != addOf(t, orOf(s, addOf(x, s)));

    case DivLemma::UdivRef31:
      // x != t + (1 + (1 << x))
      return x != addOf(t, addOf(one, shlOf(one, x)));

    case DivLemma::UdivRef32:
      // s >=u ((x + t) >> t)
      return ule(shrOf(addOf(x, t), t), s);

    case DivLemma::UdivRef34:
      // (s xor (x | t)) >=u (t xor 1)
      return ule(xorOf(t, one), xorOf(s, orOf(x, t)));

    case DivLemma::UdivRef36:
      // t >=u (x >> (s - 1))
      return ule(shrOf(x, decOf(s)), t);

    case DivLemma::UdivRef38:
      // x != 1 - (x << (x - t))
      return x != subOf(one, shlOf(x, subOf(x, t)));
  }
  return true;
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
    case DivLemma::MaskedDividendAboveDivisorAndQuotient:
      return "masked-dividend-above-divisor-and-quotient";
    case DivLemma::DividendAboveDoubledShiftedDivisor:
      return "dividend-above-doubled-shifted-divisor";
    case DivLemma::QuotientAboveDoubledShiftedDividend:
      return "quotient-above-doubled-shifted-dividend";
    case DivLemma::DividendAboveOrAndDoubledDivisor:
      return "dividend-above-or-and-doubled-divisor";
    case DivLemma::DividendAboveOrAndDoubledQuotient:
      return "dividend-above-or-and-doubled-quotient";
    case DivLemma::ShiftedDividendNotOr:
      return "shifted-dividend-not-or";
    case DivLemma::DividendAboveQuotientXorShifted:
      return "dividend-above-quotient-xor-shifted";
    case DivLemma::DividendAboveDivisorXorShifted:
      return "dividend-above-divisor-xor-shifted";
    case DivLemma::DividendNotTwiceQuotientPlusOr:
      return "dividend-not-twice-quotient-plus-or";
    case DivLemma::QuotientIsOne: return "quotient-is-one";
    case DivLemma::UdivRef10:
      return "divisor-or-quotient-not-masked-dividend";
    case DivLemma::UdivRef11:
      return "divisor-or-one-not-dividend-without-quotient";
    case DivLemma::UdivRef20:
      return "divisor-not-negated-self-shifted-by-half-quotient";
    case DivLemma::UdivRef21:
      return "dividend-not-negated-and-doubled-quotient";
    case DivLemma::UdivRef23:
      return "quotient-above-doubled-dividend-shifted-by-divisor";
    case DivLemma::UdivRef24:
      return "dividend-above-divisor-shifted-by-negated-or";
    case DivLemma::UdivRef25:
      return "dividend-above-quotient-shifted-by-negated-or";
    case DivLemma::UdivRef28:
      return "dividend-above-divisor-shifted-by-negated-xor";
    case DivLemma::UdivRef29:
      return "dividend-above-quotient-shifted-by-negated-xor";
    case DivLemma::UdivRef30:
      return "dividend-not-quotient-plus-divisor-or-sum";
    case DivLemma::UdivRef31:
      return "dividend-not-quotient-plus-one-plus-shifted-one";
    case DivLemma::UdivRef32:
      return "divisor-above-sum-shifted-by-quotient";
    case DivLemma::UdivRef34:
      return "divisor-xor-or-above-quotient-xor-one";
    case DivLemma::UdivRef36:
      return "quotient-above-dividend-shifted-by-divisor-less-one";
    case DivLemma::UdivRef38:
      return "dividend-not-one-less-shifted-dividend";
  }
  return "unknown";
}

bool remLemmaApplicable(RemLemma lemma, unsigned width)
{
  if (lemma == RemLemma::DividendNotOrOfNegations)
    return width > 2;
  return width > 0;
}

bool remLemmaEnabled(RemLemma lemma)
{
  // Bitwuzla defines but deliberately omits REF6 from its active registry.
  // It is also redundant in STP: for s != 0, t < s implies t <= s - 1;
  // for s = 0, its all-ones upper bound says nothing.
  return lemma != RemLemma::RemainderBelowDivisorDisabled;
}

bool remLemmaHolds(RemLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  assert(x.size() == s.size());
  assert(x.size() == t.size());

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

    case RemLemma::RemainderIsDifference:
      // s <=u x <u 2s -> t = x - s
      return !fitsExactlyOnce(x, s) || t == addOf(x, negOf(s));

    case RemLemma::RemainderBelowDivisorDisabled:
      // ~(-s) >=u t
      return ule(t, notOf(negOf(s)));

    case RemLemma::DividendWithinDivisorOrRemainder:
      // x = x & (s | t | -s)
      return x == andOf(x, orOf(s, orOf(t, negOf(s))));

    case RemLemma::DividendAboveRemainderOrAnd:
      // x >=u (t | (x & s))
      return ule(orOf(t, andOf(x, s)), x);

    case RemLemma::RemainderOutsideOperandsNotOne:
      // 1 != (t & ~(x | s))
      return one != andOf(t, notOf(orOf(x, s)));

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
      // (x + -s) >=u t
      return ule(t, addOf(x, negOf(s)));

    case RemLemma::XorAboveRemainder:
      // ((-s) xor (x | s)) >=u t
      return ule(t, xorOf(negOf(s), orOf(x, s)));
  }
  return true;
}

const char* remLemmaName(RemLemma lemma)
{
  switch (lemma)
  {
    case RemLemma::DividendZero:
      return "dividend-zero";
    case RemLemma::DivisorEqualsDividend:
      return "divisor-equals-dividend";
    case RemLemma::DividendBelowDivisor:
      return "dividend-below-divisor";
    case RemLemma::RemainderIsDifference:
      return "remainder-is-difference";
    case RemLemma::RemainderBelowDivisorDisabled:
      return "remainder-below-divisor-disabled";
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
    case RemLemma::XorAboveRemainder:
      return "xor-above-remainder";
  }
  return "unknown";
}

bool mulLemmaApplicable(MulLemma lemma, unsigned width)
{
  switch (lemma)
  {
    case MulLemma::MulRef1:
    case MulLemma::FactorAndProductNotOr:
    case MulLemma::MulRefN3:
    case MulLemma::MulRef14:
    case MulLemma::MulRef15:
    case MulLemma::MulRef13: return width > 1;
    case MulLemma::MulRefN5: return width != 2;
    default: return width > 0;
  }
}

bool mulLemmaHolds(MulLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  assert(x.size() == s.size());
  assert(x.size() == t.size());

  const unsigned W = (unsigned)x.size();
  std::vector<bool> one(W, false);
  one[0] = true;

  switch (lemma)
  {
    case MulLemma::FactorUnchangedByMaskedShift:
      // s = s << (x & (1 >> t))
      return s == shlOf(s, andOf(x, shrOf(one, t)));

    case MulLemma::MulRef1:
      // s != ~(t | (1 & (x | s)))
      return s != notOf(orOf(t, andOf(one, orOf(x, s))));

    case MulLemma::FactorAndProductNotOr:
      // (x & t) != (s | ~t)
      return andOf(x, t) != orOf(s, notOf(t));

    case MulLemma::MulRefN3:
    {
      // t != ((s | 1) << (t << x))
      std::vector<bool> sOrOne = s;
      sOrOne[0] = true;
      return t != shlOf(sOrOne, shlOf(t, x));
    }

    case MulLemma::MulRefN5:
      // t >=u (1 & ((x & s) >> 1))
      return ule(andOf(one, shrOf(andOf(x, s), one)), t);

    case MulLemma::MulRefN6:
      // x != (1 xor (x << (s xor t)))
      return x != xorOf(one, shlOf(x, xorOf(s, t)));

    case MulLemma::MulRef14:
      // t != (1 | ~(x xor s))
      return t != orOf(one, notOf(xorOf(x, s)));

    case MulLemma::MulRef15:
      // t != (~1 | (x xor s))
      return t != orOf(notOf(one), xorOf(x, s));

    case MulLemma::MulRefN9:
      // x != (x << (s + t)) - 1
      return x != subOf(shlOf(x, addOf(s, t)), one);

    case MulLemma::MulRef18:
      // x != 1 - (x << (s - t))
      return x != subOf(one, shlOf(x, subOf(s, t)));

    case MulLemma::MulRefN11:
      // s != 1 + (s << (t - x))
      return s != addOf(one, shlOf(s, subOf(t, x)));

    case MulLemma::MulRefN12:
      // s != 1 - (s << (t - x))
      return s != subOf(one, shlOf(s, subOf(t, x)));

    case MulLemma::MulRefN13:
      // s != 1 + (s << (x - t))
      return s != addOf(one, shlOf(s, subOf(x, t)));

    case MulLemma::MulRef13:
      // t != (1 | (x + s))
      return t != orOf(one, addOf(x, s));

    case MulLemma::MulRef12:
      // x != ~(x << (s + t))
      return x != notOf(shlOf(x, addOf(s, t)));
  }
  return true;
}

const char* mulLemmaName(MulLemma lemma)
{
  switch (lemma)
  {
    case MulLemma::FactorUnchangedByMaskedShift:
      return "factor-unchanged-by-masked-shift";
    case MulLemma::MulRef1:
      return "factor-not-negated-product-or-low-bit";
    case MulLemma::FactorAndProductNotOr:
      return "factor-and-product-not-or";
    case MulLemma::MulRefN3:
      return "product-not-odd-factor-shifted-by-shifted-product";
    case MulLemma::MulRefN5:
      return "product-above-masked-shifted-factors";
    case MulLemma::MulRefN6:
      return "factor-not-one-xor-factor-shifted-by-xor";
    case MulLemma::MulRef14:
      return "product-not-one-or-negated-xor";
    case MulLemma::MulRef15:
      return "product-not-high-ones-or-xor";
    case MulLemma::MulRefN9:
      return "factor-not-shifted-factor-less-one";
    case MulLemma::MulRef18:
      return "factor-not-one-less-shifted-factor";
    case MulLemma::MulRefN11:
      return "factor-not-one-plus-shifted-factor";
    case MulLemma::MulRefN12:
      return "factor-not-one-less-shifted-factor-reversed";
    case MulLemma::MulRefN13:
      return "factor-not-one-plus-shifted-factor-reversed";
    case MulLemma::MulRef13:
      return "product-not-one-or-sum";
    case MulLemma::MulRef12:
      return "factor-not-negated-shifted-factor";
  }
  return "unknown";
}

bool mul8PublishedHolds(const std::vector<bool>& x, const std::vector<bool>& s,
                        const std::vector<bool>& t)
{
  assert(!x.empty());
  assert(x.size() == s.size());
  assert(x.size() == t.size());

  std::vector<bool> one(x.size(), false);
  one[0] = true;
  return s == shlOf(s, andOf(x, shrOf(one, t)));
}

bool addLemmaApplicable(AddLemma lemma, unsigned width)
{
  if (lemma == AddLemma::AddRef10 || lemma == AddLemma::AddRef12)
    return width > 2;
  if (lemma == AddLemma::AddRef11)
    return width > 1;
  return width > 0;
}

bool addLemmaHolds(AddLemma lemma, const std::vector<bool>& x,
                   const std::vector<bool>& s, const std::vector<bool>& t)
{
  assert(!x.empty());
  assert(x.size() == s.size());
  assert(x.size() == t.size());

  const unsigned W = (unsigned)x.size();
  const std::vector<bool> zero(W, false);
  const std::vector<bool> ones(W, true);
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
    case AddLemma::AddInv: return "add-inverse";
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

// Blast one theorem, splice the resulting CNF onto its live SAT vectors, and
// assert it. Most facts have two operands and one abstract result; paired
// DIV/REM recomposition has four vectors. The delicate CI/CNF variable
// mapping belongs in one arity-independent place.
template <typename BuildClaim>
void encodeNaryLemma(
    STPMgr* bm, SATSolver& solver, unsigned width,
    const std::vector<const std::vector<unsigned>*>& liveVars,
    BuildClaim buildClaim)
{
  assert(!liveVars.empty());
  for (const std::vector<unsigned>* vars : liveVars)
  {
    assert(vars != NULL);
    assert(vars->size() >= width);
  }

  AbstractionOff scope(bm->UserFlags);

  BBNodeManagerAIG mgr;
  mgr.nodeBudget = bm->UserFlags.aig_node_budget;
  SubstitutionMap sm(bm);
  Simplifier simp(bm, &sm);
  BitBlaster bb(&mgr, &simp, bm->defaultNodeFactory, &bm->UserFlags);

  // Every live vector is an input here. Abstract results are not circuit
  // outputs: the theorem constrains them without defining the operations.
  std::vector<BBNodeVec> inputs(liveVars.size(), BBNodeVec(width));
  for (unsigned v = 0; v < inputs.size(); ++v)
    for (unsigned i = 0; i < width; i++)
    {
      inputs[v][i] = BBNodeAIG(Aig_ObjCreateCi(mgr.aigMgr));
      inputs[v][i].symbol_index = mgr.aigMgr->vCis->nSize - 1;
    }

  BBNodeSet support;
  const BBNodeAIG claim = buildClaim(bb, inputs, support);

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
  for (unsigned i = 0; i < liveVars.size() * width; ++i)
  {
    const int var = cnf->pVarNums[Aig_ManCi(mgr.aigMgr, (int)i)->Id];
    if (var < 0)
      continue;
    cnfToSolver[var] = (*liveVars[i / width])[i % width];
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

template <typename BuildClaim>
void encodeTernaryLemma(STPMgr* bm, SATSolver& solver, unsigned width,
                        const std::vector<unsigned>& xVars,
                        const std::vector<unsigned>& sVars,
                        const std::vector<unsigned>& tVars,
                        BuildClaim buildClaim)
{
  std::vector<const std::vector<unsigned>*> liveVars;
  liveVars.push_back(&xVars);
  liveVars.push_back(&sVars);
  liveVars.push_back(&tVars);
  encodeNaryLemma(
      bm, solver, width, liveVars,
      [&buildClaim](BitBlaster& bb, const std::vector<BBNodeVec>& inputs,
                    BBNodeSet& support) {
        return buildClaim(bb, inputs[0], inputs[1], inputs[2], support);
      });
}

} // namespace

void BVExactEncoder::encodeDivLemma(SATSolver& solver, DivLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& dividendVars,
                                    const std::vector<unsigned>& divisorVars,
                                    const std::vector<unsigned>& resultVars)
{
  encodeTernaryLemma(
      bm, solver, width, dividendVars, divisorVars, resultVars,
      [lemma](BitBlaster& bb, const BBNodeVec& x, const BBNodeVec& s,
              const BBNodeVec& t, BBNodeSet& support) {
        return bb.BBDivLemma(lemma, x, s, t, support);
      });
}

void BVExactEncoder::encodeRemLemma(SATSolver& solver, RemLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& dividendVars,
                                    const std::vector<unsigned>& divisorVars,
                                    const std::vector<unsigned>& resultVars)
{
  encodeTernaryLemma(
      bm, solver, width, dividendVars, divisorVars, resultVars,
      [lemma](BitBlaster& bb, const BBNodeVec& x, const BBNodeVec& s,
              const BBNodeVec& t, BBNodeSet& support) {
        return bb.BBRemLemma(lemma, x, s, t, support);
      });
}

void BVExactEncoder::encodeMulLemma(SATSolver& solver, MulLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& xVars,
                                    const std::vector<unsigned>& sVars,
                                    const std::vector<unsigned>& resultVars)
{
  encodeTernaryLemma(
      bm, solver, width, xVars, sVars, resultVars,
      [lemma](BitBlaster& bb, const BBNodeVec& x, const BBNodeVec& s,
              const BBNodeVec& t, BBNodeSet& support) {
        return bb.BBMulLemma(lemma, x, s, t, support);
      });
}

void BVExactEncoder::encodeAddLemma(SATSolver& solver, AddLemma lemma,
                                    unsigned width,
                                    const std::vector<unsigned>& xVars,
                                    const std::vector<unsigned>& sVars,
                                    const std::vector<unsigned>& resultVars)
{
  encodeTernaryLemma(
      bm, solver, width, xVars, sVars, resultVars,
      [lemma](BitBlaster& bb, const BBNodeVec& x, const BBNodeVec& s,
              const BBNodeVec& t, BBNodeSet& support) {
        return bb.BBAddLemma(lemma, x, s, t, support);
      });
}

void BVExactEncoder::encodeDivRemIdentity(
    SATSolver& solver, const ASTNode& product, unsigned width,
    const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& divisorVars,
    const std::vector<unsigned>& quotientVars,
    const std::vector<unsigned>& remainderVars)
{
  std::vector<const std::vector<unsigned>*> liveVars;
  liveVars.push_back(&dividendVars);
  liveVars.push_back(&divisorVars);
  liveVars.push_back(&quotientVars);
  liveVars.push_back(&remainderVars);
  encodeNaryLemma(
      bm, solver, width, liveVars,
      [&product](BitBlaster& bb, const std::vector<BBNodeVec>& inputs,
                 BBNodeSet& support) {
        return bb.BBDivRemIdentity(product, inputs[0], inputs[1], inputs[2],
                                   inputs[3], support);
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
