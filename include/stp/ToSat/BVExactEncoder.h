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
// This is how --bv-term-abstraction gives up, and how its algebraic schemas
// are inserted. A BVMULT, BVDIV or BVMOD it abstracted is refined by ruling
// out one pair of operand values at a time, and after a bounded number of
// those the refinement stops enumerating and says what the operation is.
// Addition, multiplication, division and remainder schemas use the same
// circuit-to-live-CNF splice to assert facts that rule out larger candidate
// regions. What any of those encodings says has to be worth having: an
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
// The four with no premise are not facts anyone would derive by thinking
// about division -- `x >=u -((-s) & (-t))` is the output of the syntax-guided
// synthesis that paper describes -- which is the argument for porting them
// rather than inventing a set.
//
// The enum identifiers retain Bitwuzla's registry IDs where that makes source
// reconciliation mechanical. divLemmaName() gives every measured entry a
// semantic diagnostic name, while the unobserved tail deliberately keeps its
// source number. The table in the refiner keeps measured entries in firing
// order and the unobserved tail in source order. Completeness is useful for
// controlled ablations, not evidence that every fact should eventually be
// enabled by default.
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

  // These identifiers deliberately retain Bitwuzla's registry numbers.
  // The observed entries have readable diagnostic names in divLemmaName();
  // the source ID remains here so the transcription is still auditable.
  UdivRef9,
  UdivRef12,
  UdivRef14,
  UdivRef16,
  UdivRef17,
  UdivRef18,
  UdivRef19,
  UdivRef26,
  UdivRef27,
  UdivRef33,
  UdivRef10,
  UdivRef11,
  UdivRef20,
  UdivRef21,
  UdivRef23,
  UdivRef24,
  UdivRef25,
  UdivRef28,
  UdivRef29,
  UdivRef30,
  UdivRef31,
  UdivRef32,
  UdivRef34,
  UdivRef36,
  UdivRef38
};

// The remainder-specific part of Bitwuzla's registry. Enum identifiers keep
// the source IDs, while remLemmaName() describes each enabled relationship in
// solver diagnostics. UremRef6 is retained so the transcription and its
// circuit stay checked, but the source solver does not enable it and neither
// does STP: it is subsumed by the existing non-zero-divisor remainder bound
// (and is vacuous over a zero divisor).
enum class RemLemma
{
  UremRef2,
  UremRef4,
  UremRef5,
  UremRef6,
  UremRef7,
  UremRef8,
  UremRef9,
  UremRef10,
  UremRef11,
  UremRef12,
  UremRef13,
  UremRef14
};

// The unconditional multiplication facts not already represented by STP's
// power-of-two, low-bit, trailing-zero and odd-inverse schemas. The IDs are
// Bitwuzla's registry names; mulLemmaName() gives the qualified MulRef3 fact
// its semantic name. Each has two readings because multiplication is
// commutative but most synthesised expressions are not syntactically so.
enum class MulLemma
{
  MulRef1,
  MulRef3,
  MulRefN3,
  MulRefN5,
  MulRefN6,
  MulRef14,
  MulRef15,
  MulRefN9,
  MulRef18,
  MulRefN11,
  MulRefN12,
  MulRefN13,
  MulRef13,
  MulRef12
};

enum class AddLemma
{
  AddZero,
  AddSame,
  AddInv,
  AddOverflow,
  AddNoOverflow,
  AddOr,
  AddRef6,
  AddRef7,
  AddRef8,
  AddRef9,
  AddRef10,
  AddRef11,
  AddRef12
};

// Whether one of them holds of these three values. The refiner asks before
// installing -- a lemma the candidate already satisfies rules nothing out --
// and the tests ask to check the circuits say the same thing.
//
// Bit vectors, least significant bit first, all of the same width.
DLL_PUBLIC bool divLemmaHolds(DivLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);

// Some synthesised facts are theorems only above a stated bit width. A
// caller must not evaluate or install one outside that domain.
DLL_PUBLIC bool divLemmaApplicable(DivLemma lemma, unsigned width);

DLL_PUBLIC const char* divLemmaName(DivLemma lemma);

DLL_PUBLIC bool remLemmaHolds(RemLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);
DLL_PUBLIC bool remLemmaApplicable(RemLemma lemma, unsigned width);
DLL_PUBLIC bool remLemmaEnabled(RemLemma lemma);
DLL_PUBLIC const char* remLemmaName(RemLemma lemma);

DLL_PUBLIC bool mulLemmaHolds(MulLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);
DLL_PUBLIC bool mulLemmaApplicable(MulLemma lemma, unsigned width);
DLL_PUBLIC const char* mulLemmaName(MulLemma lemma);

DLL_PUBLIC bool addLemmaHolds(AddLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);
DLL_PUBLIC bool addLemmaApplicable(AddLemma lemma, unsigned width);
DLL_PUBLIC const char* addLemmaName(AddLemma lemma);

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

  void encodeRemLemma(SATSolver& solver, RemLemma lemma, unsigned width,
                      const std::vector<unsigned>& dividendVars,
                      const std::vector<unsigned>& divisorVars,
                      const std::vector<unsigned>& resultVars);

  void encodeMulLemma(SATSolver& solver, MulLemma lemma, unsigned width,
                      const std::vector<unsigned>& xVars,
                      const std::vector<unsigned>& sVars,
                      const std::vector<unsigned>& resultVars);

  void encodeAddLemma(SATSolver& solver, AddLemma lemma, unsigned width,
                      const std::vector<unsigned>& xVars,
                      const std::vector<unsigned>& sVars,
                      const std::vector<unsigned>& resultVars);

  // Splice x = q*s+r over the four live vectors belonging to a paired BVDIV
  // and BVMOD abstraction. Arithmetic is truncated to `width`, so this is a
  // theorem of SMT-LIB's totalised division even when the divisor is zero.
  void encodeDivRemIdentity(
      SATSolver& solver, const ASTNode& product, unsigned width,
      const std::vector<unsigned>& dividendVars,
      const std::vector<unsigned>& divisorVars,
      const std::vector<unsigned>& quotientVars,
      const std::vector<unsigned>& remainderVars);
};

} // namespace stp

#endif
