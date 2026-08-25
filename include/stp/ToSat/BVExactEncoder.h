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

#ifndef BVEXACTENCODER_H
#define BVEXACTENCODER_H

// Puts `result = a op b` into a SAT solver that is already running, over
// variables it already has.
//
// This is how --bv-term-abstraction gives up. A BVMULT, BVDIV or BVMOD it
// abstracted is refined by ruling out one pair of operand values at a time,
// and after a bounded number of those the refinement stops enumerating and
// says what the operation is. What it says has to be worth having: an
// abstraction that is abandoned late should leave the solver no worse off
// than one that was never taken, and the only way that holds is if the
// encoding it falls back on is the one the query would have had anyway.
//
// So this does not write clauses. It builds the circuit with the same
// BitBlaster that a plain solve uses, hands the AIG to the same ABC cut
// enumeration and technology mapping that ToCNFAIG uses, and splices the
// CNF that comes back onto the variables the abstraction has been talking
// about all along -- the operand proxies and the abstraction's own result
// bits. Hand-written gates were about twice the clauses for the same
// function, which is a strange thing to pay for at the exact moment the
// abstraction has admitted it is not helping.
//
// Nothing here is retractable and nothing needs to be: what it adds is a
// definitional fact about the operation, true whatever else is asserted.

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolver.h"

#include <vector>

namespace stp
{

// The facts about division that STP had no way to state before this: each
// is an inequality or an implication over the dividend, the divisor and the
// quotient, rather than a value for the quotient.
//
// They are Bitwuzla's, taken from its abstraction module and reimplemented
// here over the bit-blaster rather than copied. Both projects are MIT.
//
//   Aina Niemetz, Mathias Preiner, Yoni Zohar.
//   Scalable Bit-Blasting with Abstractions.
//   CAV 2024, LNCS 14681, pp. 178-200. doi:10.1007/978-3-031-65627-9_9
//
// The ones with no premise are not facts anyone would derive by thinking
// about division -- `x >=u -((-s) & (-t))` is the output of the syntax-guided
// synthesis that paper describes -- which is the argument for porting them
// rather than inventing a set.
//
// Which eighteen: every UDIV fact that fired at all on the queries that
// motivated this -- 1530 firings between them over the 73 files STP could
// not decide, from 280 down to 2. Fifteen more exist upstream and are not
// here, having fired nothing. That is weaker evidence against them than it
// looks: the solver those counts come from stops at the first fact a
// candidate breaks, so a strong fact late in its order is never reached and
// never counted. What is measured is which facts are productive *first*,
// which is exactly what the table's order needs, and not which are useless.
enum class DivLemma
{
  // x = 0 and s != 0 -> t = 0
  DividendZero,
  // s = x and s != 0 -> t = 1
  DivisorEqualsDividend,
  // s = ~0 and x != ~0 -> t = 0
  DivisorAllOnes,
  // t <=u -(s | 1)
  QuotientBelowNegatedDivisor,
  // x >=u -((-s) & (-t))
  DividendAboveNegatedAnd,
  // s >=u (x >> t)
  DivisorAboveShiftedDividend,
  // (s - 1) >=u (x >> t)
  DivisorLessOneAboveShiftedDividend,
  // x >=u ((t << 1) >> (t << s))
  DividendAboveShiftedDoubleQuotient,
  // t != -(s & ~x)
  QuotientNotNegatedAnd,
  // x >=u ((s >> (s << t)) << 1)
  DividendAboveDoubledShiftedDivisor,
  // x != t + t + (x | s). The one fact here that is false at a width the
  // abstraction can be asked for; see divLemmaMinWidth().
  DividendNotTwiceQuotientPlusOr,
  // t >=u ((x >> s) << 1)
  QuotientAboveDoubledShiftedDividend,
  // x >=u ((x | t) & (s << 1))
  DividendAboveOrAndDoubledDivisor,
  // (x & -t) >=u (s & t)
  MaskedDividendAboveDivisorAndQuotient,
  // x >=u (t ^ (t >> (s >> 1)))
  DividendAboveQuotientXorShifted,
  // (x >> t) != (s | t)
  ShiftedDividendNotOr,
  // x >=u ((x | s) & (t << 1))
  DividendAboveOrAndDoubledQuotient,
  // x >=u (s ^ (s >> (t >> 1)))
  DividendAboveDivisorXorShifted
};

// Whether one of them holds of these three values. The refiner asks before
// installing -- a lemma the candidate already satisfies rules nothing out --
// and the tests ask to check the circuits say the same thing.
//
// Bit vectors, least significant bit first, all of the same width.
DLL_PUBLIC bool divLemmaHolds(DivLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);

// The narrowest bit vector a fact is true of. One for all but the synthesised
// ones the source marks as restricted, which are false at a width or two and
// true from there up.
//
// The solver they come from sidesteps this by refusing to abstract anything
// narrower than three bits at all. STP's threshold is a flag whose default is
// 64 but whose floor is one, so the restriction is carried per fact instead
// and the chooser skips a fact the abstraction in front of it is too narrow
// for. A minimum is exact rather than cautious: the tests check that the fact
// really does fail one bit below it.
DLL_PUBLIC unsigned divLemmaMinWidth(DivLemma lemma);

DLL_PUBLIC const char* divLemmaName(DivLemma lemma);

// The same for `t = x urem s`, which STP had none of at all: an abstracted
// BVMOD carried the two bounds and the divisor-guarded schemas and nothing
// else, so the widest thing it could say about a remainder over a divisor
// that was neither zero nor a power of two was that it was below the
// divisor.
//
// The order here is the source's own rather than a firing count, because
// there is no firing count: the family that motivated the division work
// barely uses a remainder at all -- twenty-five lemma kinds fired across it
// and not one of them was a UREM -- so what these are worth is untested and
// the honest order is the one they were published in. What they cost is a
// refinement round each, on an operation with nothing else to spend one on.
//
// One of the source's sixteen is absent by its own judgement rather than
// mine: `~(-s) >=u t` is `s != 0 -> t <u s` written without the premise,
// which STP already installs as DivSchema::RemainderBelowDivisor, and the
// source keeps it commented out for the same reason.
enum class RemLemma
{
  // x = 0 -> t = 0
  DividendZero,
  // s = x -> t = 0
  DivisorEqualsDividend,
  // x <u s -> t = x. The one that settles the operation outright, and the
  // cheapest circuit of the eleven.
  DividendBelowDivisor,
  // x = x & (s | t | -s)
  DividendWithinDivisorOrRemainder,
  // x >=u (t | (x & s))
  DividendAboveRemainderOrAnd,
  // (t & ~(x | s)) != 1
  RemainderOutsideOperandsNotOne,
  // t != (~x | -s)
  RemainderNotOrOfComplements,
  // (t & (x | s)) >=u (t & 1)
  RemainderInOperandsAboveLowBit,
  // x != (-x | -(~t)). Restricted; see remLemmaMinWidth().
  DividendNotOrOfNegations,
  // (x - s) >=u t
  DifferenceAboveRemainder,
  // ((-s) ^ (x | s)) >=u t
  XorAboveRemainder
};

DLL_PUBLIC bool remLemmaHolds(RemLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);

DLL_PUBLIC unsigned remLemmaMinWidth(RemLemma lemma);

DLL_PUBLIC const char* remLemmaName(RemLemma lemma);

class DLL_PUBLIC BVExactEncoder
{
  STPMgr* bm;

public:
  explicit BVExactEncoder(STPMgr* bm_) : bm(bm_) {}

  // `term` is the operation's own node -- its kind is one of BVMULT, BVDIV
  // and BVMOD, and the multiplier reads its operands for constant detection
  // and Booth recoding. `aVars`, `bVars` and `resultVars` are the SAT
  // variables the operands and the result are already carried by, each
  // `width` bits wide; every one of them must be a variable the solver has.
  //
  // The clauses added define the result bits from the operand bits, so a
  // caller may mark the abstraction defined once this returns.
  void encode(SATSolver& solver, const ASTNode& term, unsigned width,
              const std::vector<unsigned>& aVars,
              const std::vector<unsigned>& bVars,
              const std::vector<unsigned>& resultVars);

  // One algebraic fact about `t = x udiv s`, spliced onto the variables the
  // dividend, the divisor and the abstraction's result are already carried
  // by, and asserted.
  //
  // The same splice as `encode` above and for the same reason: a lemma has
  // to talk about the bits the rest of the query talks about. What differs
  // is that this asserts a single Boolean rather than defining the result
  // bits, so the abstraction stays an abstraction -- the fact constrains it
  // without saying what it is.
  //
  // Going through the bit-blaster rather than emitting clauses by hand is
  // what makes the facts below affordable at all: several are inequalities
  // over a shift by a variable amount, which is a barrel shifter, which is
  // not something to write a clause at a time.
  void encodeDivLemma(SATSolver& solver, DivLemma lemma, unsigned width,
                      const std::vector<unsigned>& dividendVars,
                      const std::vector<unsigned>& divisorVars,
                      const std::vector<unsigned>& resultVars);

  // ... and one about `t = x urem s`, spliced the same way onto the same
  // three sets of variables. Only the circuit differs.
  void encodeRemLemma(SATSolver& solver, RemLemma lemma, unsigned width,
                      const std::vector<unsigned>& dividendVars,
                      const std::vector<unsigned>& divisorVars,
                      const std::vector<unsigned>& resultVars);
};

} // namespace stp

#endif
