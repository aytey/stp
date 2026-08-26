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

#ifndef BVABSTRACTIONREFINER_H
#define BVABSTRACTIONREFINER_H

// The CEGAR half of --bv-eq-abstraction and --bv-term-abstraction.
//
// The bit-blaster replaces an equality, a comparison or an arithmetic
// operation by free combinational inputs and records what it stood for.
// That is an over-approximation, so a candidate model is an assignment of
// the query only once every abstraction in it has been checked against
// the operands underneath and, where the two disagree, pinned by clauses.
// This is the party that does the checking and the pinning.
//
// It is kept apart from the lowering that mints the records because there
// are two of those -- the batch pipeline's whole-formula ToSATAIG and the
// incremental driver's persistent, per-conjunct encoder -- and only the
// resolution of a record's SAT variables differs between them. Everything
// here works from the records plus one map from node to SAT variables, and
// so is shared.
//
// Nothing it adds to the solver is retractable, and nothing needs to be:
// every clause is a definitional fact about the blasted circuit -- this
// abstraction variable means these operand bits -- which holds whatever
// else is asserted. Refining an abstraction only ever brings the encoding
// closer to the query it already stood for.

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/BVExactEncoder.h"
#include "stp/ToSat/ToSATBase.h"

#include <cstdint>
#include <vector>

namespace stp
{

// The variable a record does not have: the condition input of a family that
// carries none, or one whose input never reached the solver. It is ~0u
// rather than zero because zero is a SAT variable like any other -- the
// incremental driver has handed variable 1 to an abstraction input -- and a
// record whose variable read as absent would be skipped, which for an
// over-approximation means certified.
const unsigned BV_ABSTRACTION_NO_VAR = ~((unsigned)0);

// An equality replaced by one free Boolean. `refinedBits` counts the bit
// positions whose agreement has been encoded so far, and `defined` marks
// the point where all of them have been, after which the Boolean is the
// equality and the record is never revisited.
struct BVEQAbstraction
{
  ASTNode eqNode;
  unsigned abstractionSATVar = BV_ABSTRACTION_NO_VAR;
  ASTNode leftSymbol;
  ASTNode rightSymbol;
  unsigned width;
  bool defined = false;
  unsigned refinedBits = 0;
  std::vector<unsigned> xnorHelpers;
};

// An operation replaced by free result bits (and, for a comparison or an
// if-then-else, a free condition variable).
// The algebraic facts about a multiplication that a refinement round may
// spend in place of ruling out the one pair of operand values the candidate
// happens to hold.
//
// A blocking lemma excludes a single point of a 2^(2W) space, so a
// multiplication the search has to work through can need more rounds than
// there are pairs of operands -- at 53 bits, one of 2^106. Each of these
// excludes a slice instead: they are theorems about every pair, not about
// the one in hand, and the candidate is read only to decide which of them
// it contradicts.
//
// The hand-written schemas cover low-bit parity, trailing-zero preservation,
// zero-products with an odd operand, and positive and negative powers of two;
// Lemma carries the remainder of the upstream synthesised registry.
enum class MulSchema
{
  // Nothing the candidate contradicts. The round falls through to the
  // blocking lemma and the escalation behind it.
  None,
  // t[0] = a[0] & b[0]: the product is odd exactly when both operands are.
  Odd,
  // An odd bit-vector is invertible modulo 2^W, so if one operand is odd
  // and the product is zero, the other operand must be zero. This is MUL8
  // from the Bitwuzla set, simplified from
  //   s = s << (x & (1 >> t))
  // to its only nontrivial case: t = 0 and x[0] = 1 imply s = 0.
  ZeroProductOddOperand,
  // The product carries at least as many trailing zeros as either operand,
  // written per bit: t[i] holds only if some bit of that operand at or
  // below i does. Equivalently, for operand s and product t:
  // `(bvand (bvor (bvneg s) s) t) = t`.
  TrailingZeros,
  // An operand whose value is 2^k turns the product into a shift of the
  // other one: a = 2^k -> t = b << k. The premise fixes one operand, so
  // this still rules out 2^W pairs rather than one.
  Pow2,
  // ... and an operand whose value is -2^k turns it into a shift of the
  // other one negated: a = -2^k -> t = (-b) << k.
  NegPow2,
  // The exact low min(3, W) bits of the product. Unlike the later
  // piece-at-a-time escalation, this is offered before any blocking lemma
  // and is paid for only once.
  LowPrefix,
  // One of the remaining synthesised facts, named by lemmaIndex.
  Lemma
};

// Which fact to spend, over which operand. Multiplication is commutative,
// so each schema has two readings and they are separate lemmas.
struct MulSchemaChoice
{
  MulSchema schema = MulSchema::None;
  unsigned operand = 0;
  // log2 of the power of two for the two shift schemas, or the number of
  // exact result bits for LowPrefix.
  unsigned shift = 0;
  // Set for Lemma: index in mulLemmaTable().
  unsigned lemmaIndex = 0;
  // The option family that admitted this choice. BASE is also the harmless
  // default for None and for the established schemas' aggregate initialisers.
  BVSchemaGroup group = BVSchemaGroup::BASE;
};

// Bits of BVTermAbstraction::installedSchemas. Only the unconditional facts
// are tracked: once installed, no candidate can contradict them again, so
// re-checking them is wasted and re-emitting them is worse. The two
// value-guarded schemas need no flag -- installing one for a given operand
// value settles that value for good, and there are only as many of them as
// there are bits.
enum : uint64_t
{
  MUL_SCHEMA_INSTALLED_ODD = 1ull,
  MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0 = 2ull,
  MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1 = 4ull,
  MUL_SCHEMA_INSTALLED_ZERO_PRODUCT_ODD_0 = 8ull,
  MUL_SCHEMA_INSTALLED_ZERO_PRODUCT_ODD_1 = 16ull,
  MUL_LEMMA_INSTALLED_FIRST = 32ull,
  // Fourteen lemmas in two operand readings occupy bits 5 through 32.
  MUL_SCHEMA_INSTALLED_LOW_PREFIX = 1ull << 33
};

inline uint64_t mulLemmaInstalledBit(unsigned index, unsigned operand)
{
  return MUL_LEMMA_INSTALLED_FIRST << (2 * index + operand);
}

DLL_PUBLIC const MulLemma* mulLemmaTable(unsigned& count);

struct AddSchemaChoice
{
  bool found = false;
  unsigned operand = 0;
  unsigned lemmaIndex = 0;
  // Nonzero selects the exact low-prefix schema instead of lemmaIndex.
  unsigned prefixBits = 0;
  BVSchemaGroup group = BVSchemaGroup::BASE;
};

// Thirteen lemmas in two operand readings occupy bits 0 through 25.
const uint64_t ADD_SCHEMA_INSTALLED_LOW_PREFIX = 1ull << 26;

inline uint64_t addLemmaInstalledBit(unsigned index, unsigned operand)
{
  return uint64_t{1} << (2 * index + operand);
}

DLL_PUBLIC const AddLemma* addLemmaTable(unsigned& count);
DLL_PUBLIC AddSchemaChoice
chooseAddSchema(const std::vector<bool>& aBits, const std::vector<bool>& bBits,
                const std::vector<bool>& tBits, uint64_t installedSchemas,
                uint32_t enabledGroups = BV_SCHEMA_GROUP_ALL);

// The first fact above that this candidate contradicts, or None. Pure: the
// caller has already read the model, and what comes back depends on nothing
// else.
//
// `tBits` is the product bits the candidate holds, NOT the product of
// `aBits` and `bBits` -- the whole point is that the two disagree. Called
// only once they do.
DLL_PUBLIC MulSchemaChoice
chooseMulSchema(const std::vector<bool>& aBits, const std::vector<bool>& bBits,
                const std::vector<bool>& tBits, uint64_t installedSchemas,
                uint32_t enabledGroups = BV_SCHEMA_GROUP_ALL);

// Whether the candidate result agrees with the exact low `prefixBits` of an
// addition or multiplication. All vectors are least-significant-bit first.
DLL_PUBLIC bool exactLowPrefixHolds(Kind opKind,
                                    const std::vector<bool>& aBits,
                                    const std::vector<bool>& bBits,
                                    const std::vector<bool>& resultBits,
                                    unsigned prefixBits);

// Exact low-prefix circuits over the live abstraction variables. Addition
// accepts the negated-operand spelling recorded by the bit-blaster; at most
// one operand is negated on every abstracted addition.
DLL_PUBLIC void encodeAddLowPrefix(
    SATSolver& solver, const std::vector<unsigned>& aVars,
    const std::vector<unsigned>& bVars,
    const std::vector<unsigned>& resultVars, unsigned width,
    unsigned prefixBits, bool aNegated = false, bool bNegated = false);
DLL_PUBLIC void encodeMulLowPrefix(
    SATSolver& solver, const std::vector<unsigned>& aVars,
    const std::vector<unsigned>& bVars,
    const std::vector<unsigned>& resultVars, unsigned width,
    unsigned prefixBits);

// x[0] = 1 and s != 0 -> t != 0. This is the compact CNF form of the
// ZeroProductOddOperand schema above. Exposed so the exhaustive test can
// independently compare what the chooser claims with what the clauses say.
DLL_PUBLIC void encodeMulZeroProductOddOperand(
    SATSolver& solver, const std::vector<unsigned>& oddOperandVars,
    const std::vector<unsigned>& otherOperandVars,
    const std::vector<unsigned>& resultVars, unsigned width);

// The algebraic facts an abstracted BVDIV or BVMOD is refined with.
//
// Division is not commutative and has no cheap unconditional fact about its
// low bits to match the multiplication schemas: the low bits of a quotient
// depend on the whole of both operands. The first two facts are value-guarded
// on the *divisor*. Each says what the operation is for one divisor and
// leaves the dividend free, which rules out 2^W pairs where a blocking lemma
// rules out one. They need no installed flag: fixing a divisor value settles
// that value for good. The bounds and synthesised facts that follow apply to
// whole candidate regions and are each installed once.
enum class DivSchema
{
  // Nothing the candidate contradicts. The round falls through to the
  // blocking lemma and the escalation behind it.
  None,
  // b = 0 -> t = ~0 for BVDIV, t = a for BVMOD. SMT-LIB totalises both and
  // the abstraction is told neither, so a candidate may divide by zero and
  // call the answer anything at all. This is the one divisor a blocking
  // lemma is worst at: it rules out the pair (a, 0) and leaves every other
  // dividend over the same zero divisor still to be found.
  DivisorZero,
  // b = 2^k -> t = a >> k for BVDIV, t = a & (2^k - 1) for BVMOD. k = 0 is
  // the useful degenerate reading: dividing by one is the dividend, and the
  // remainder over one is zero.
  Pow2Divisor,
  // The facts below name no particular divisor, which is what makes them
  // fire. A candidate handed a 256-bit divisor is almost never
  // handed zero or a power of two, so the two schemas above sit idle on
  // exactly the queries the abstraction exists for -- while a bound is
  // contradicted by any candidate that overshoots, whatever the divisor is.
  //
  // Each is installed once and then never again: they are facts about every
  // pair of operands, so a second copy would say nothing new.
  //
  // r <=u a. True over a zero divisor as well, where the remainder is the
  // dividend, so this one carries no premise whatsoever.
  RemainderAtMostDividend,
  // b != 0 -> r <u b, which is what a remainder is.
  RemainderBelowDivisor,
  // The quotient-one band, stated without doubling the divisor (which could
  // overflow): b <=u a and (a - b) <u b -> r = a - b. The two comparisons
  // make the premise false for b = 0, so SMT-LIB's totalised zero-divisor
  // result needs no separate case.
  RemainderQuotientOne,
  // The quotient half of the same band:
  //   b <=u a and (a - b) <u b -> q = 1.
  // This names the quotient exactly where one subtraction, but not two,
  // fits. It is kept in a separate group from the remainder fact so corpus
  // qualification can decide on each cost independently.
  QuotientOne,
  // b != 0 -> t <=u a. Dividing by one leaves the dividend and dividing by
  // more only shrinks it; the premise is there for the zero divisor, whose
  // totalised all-ones quotient is the one case that breaks it.
  QuotientAtMostDividend,
  // For q = a udiv b and every 0 < k < W:
  //   q >= 2^k <-> b <=u (a >> k).
  // For a nonzero divisor this is the definition of floor division, moved
  // across the fixed power of two. For a zero divisor both sides are true:
  // SMT-LIB gives q the all-ones value, and zero is at most every shift.
  // One violated threshold rules out a whole quotient-magnitude band with a
  // fixed shift and one comparison, rather than constructing a divider.
  QuotientPow2Threshold,
  // If the divisor has magnitude at least 2^k, the quotient cannot exceed
  // the dividend shifted right by k:
  //   b >=u 2^k -> q <=u (a >> k).
  // The chooser takes k from the candidate divisor's top bit and caps this
  // family at two instances per abstraction; without that cap a search can
  // walk through one divisor magnitude per refinement round.
  DivisorMagnitudeBound,
  // One of the DivLemma facts, named by DivSchemaChoice::lemmaIndex. They
  // are inequalities over the quotient rather than statements of what it
  // is, and several shift by a variable amount, so unlike everything above
  // they are built by the bit-blaster rather than written a clause at a
  // time.
  Lemma
};

// Bits of BVTermAbstraction::installedSchemas for the unconditional division
// or remainder facts. They share the field with the multiplication and
// addition flags, which is safe because an abstraction has only one kind.
enum : uint64_t
{
  DIV_SCHEMA_INSTALLED_QUOTIENT_ONE = 1ull,
  DIV_SCHEMA_INSTALLED_REMAINDER_QUOTIENT_ONE = 4ull,
  DIV_SCHEMA_INSTALLED_REMAINDER_AT_MOST_DIVIDEND = 8ull,
  DIV_SCHEMA_INSTALLED_REMAINDER_BELOW_DIVISOR = 16ull,
  DIV_SCHEMA_INSTALLED_QUOTIENT_AT_MOST_DIVIDEND = 32ull,
  // ... and one apiece for the DivLemma or RemLemma facts, which are
  // unconditional for the same reason and tracked the same way. The first
  // of them is 64; divLemmaInstalledBit(i) is the bit for the i'th.
  DIV_LEMMA_INSTALLED_FIRST = 64ull
};

inline uint64_t divLemmaInstalledBit(unsigned index)
{
  return DIV_LEMMA_INSTALLED_FIRST << index;
}

// The divisor-magnitude schema deliberately gets only two attempts. Its
// facts are guarded by a magnitude rather than a single divisor value, and
// an uncapped search was observed stepping through dozens of magnitudes.
// Keep these bits above the complete imported registry.
enum : uint64_t
{
  DIV_SCHEMA_MAGNITUDE_BOUND_FIRST = 1ull << 60,
  DIV_SCHEMA_MAGNITUDE_BOUND_ALLOWANCE = 2
};

inline uint64_t divMagnitudeBoundBit(unsigned index)
{
  return DIV_SCHEMA_MAGNITUDE_BOUND_FIRST << index;
}

inline bool divMagnitudeBoundsLeft(uint64_t installedSchemas)
{
  for (unsigned i = 0; i < DIV_SCHEMA_MAGNITUDE_BOUND_ALLOWANCE; ++i)
    if ((installedSchemas & divMagnitudeBoundBit(i)) == 0)
      return true;
  return false;
}

// The DivLemma facts the chooser offers, in the order it offers them, and
// how many there are. Exposed so a test can walk the same table the refiner
// does rather than keeping a second copy of it in step with this one.
DLL_PUBLIC const DivLemma* divLemmaTable(unsigned& count);

// All remainder facts STP transcribes, including the one upstream keeps
// disabled. chooseDivSchema consults remLemmaEnabled() before offering one.
DLL_PUBLIC const RemLemma* remLemmaTable(unsigned& count);

struct DivSchemaChoice
{
  DivSchema schema = DivSchema::None;
  // log2 of the divisor for Pow2Divisor, or the exponent used by one of the
  // two power-of-two quotient bounds.
  unsigned shift = 0;
  // Set when `schema` is Lemma: which DivLemma or RemLemma fact to install,
  // as an index into the operation's table.
  unsigned lemmaIndex = 0;
  BVSchemaGroup group = BVSchemaGroup::BASE;
};

// Where each bit of the result comes from once a schema has fixed the
// divisor: a bit of the dividend, or a constant. The fact is written this
// way because it is exactly what the encoder can pin under a guard, which
// keeps what the schema claims and what it installs from drifting apart --
// and it lets a test check the claim without a solver.
enum : int
{
  DIV_SOURCE_ZERO = -1,
  DIV_SOURCE_ONE = -2
};

DLL_PUBLIC std::vector<int> divSchemaSources(Kind opKind, unsigned width,
                                             const DivSchemaChoice& choice);

// The first of the facts above that this candidate contradicts, or None.
// Pure, and called under the same conditions as chooseMulSchema: `tBits` is
// what the candidate holds for the result, already known to disagree with
// what the operands say it should be.
//
// `opKind` is BVDIV or BVMOD. The two share both schemas and differ only in
// what each one concludes.
DLL_PUBLIC DivSchemaChoice chooseDivSchema(
    Kind opKind, const std::vector<bool>& aBits, const std::vector<bool>& bBits,
    const std::vector<bool>& tBits, uint64_t installedSchemas,
    uint32_t enabledGroups = BV_SCHEMA_GROUP_ALL);

// A variable that holds exactly when `lv <= rv`. Shared by the comparison
// refinement, which is where it comes from, and by the division bounds,
// which are comparisons over the abstraction's own result bits.
DLL_PUBLIC unsigned encodeLessOrEqual(SATSolver& solver,
                                      const std::vector<unsigned>& lv,
                                      const std::vector<unsigned>& rv,
                                      unsigned width, bool isSigned);

// One of the three bounds, over the operand proxies and the abstraction's
// own result bits. Exposed for the same reason as the encoder above: that
// the clauses say what the schema claims is a question only a solver can
// answer.
DLL_PUBLIC void encodeDivBound(SATSolver& solver, DivSchema schema,
                               const std::vector<unsigned>& dividendVars,
                               const std::vector<unsigned>& divisorVars,
                               const std::vector<unsigned>& resultVars,
                               unsigned width);

// q >= 2^shift <-> divisor <=u (dividend >> shift), written over an
// abstracted BVDIV's operand proxies and result bits.
DLL_PUBLIC void encodeDivPow2Threshold(
    SATSolver& solver, const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& divisorVars,
    const std::vector<unsigned>& quotientVars, unsigned width,
    unsigned shift);

// b <=u a and (a - b) <u b -> r = a - b.
DLL_PUBLIC void encodeRemQuotientOne(
    SATSolver& solver, const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& divisorVars,
    const std::vector<unsigned>& remainderVars, unsigned width);

// b <=u a and (a - b) <u b -> q = 1.
DLL_PUBLIC void encodeDivQuotientOne(
    SATSolver& solver, const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& divisorVars,
    const std::vector<unsigned>& quotientVars, unsigned width);

// b >=u 2^shift -> q <=u (a >> shift).
DLL_PUBLIC void encodeDivisorMagnitudeBound(
    SATSolver& solver, const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& divisorVars,
    const std::vector<unsigned>& quotientVars, unsigned width,
    unsigned shift);

// The prefix quotient/remainder recomposition theorem:
//   low(x) = low((q * s) + r).
// It holds for the SMT-LIB zero-divisor values as well as ordinary division;
// asking for the complete width is the full modular identity.
DLL_PUBLIC bool divRemLowPrefixHolds(
    const std::vector<bool>& dividendBits,
    const std::vector<bool>& divisorBits,
    const std::vector<bool>& quotientBits,
    const std::vector<bool>& remainderBits, unsigned prefixBits);
DLL_PUBLIC void encodeDivRemLowPrefix(
    SATSolver& solver, const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& divisorVars,
    const std::vector<unsigned>& quotientVars,
    const std::vector<unsigned>& remainderVars, unsigned width,
    unsigned prefixBits);

// divisor = divisorBits -> every result bit is a constant or a bit of the
// dividend, as `source` says. Exposed for the tests: what the schema claims
// is checked by evaluating `divSchemaSources`, and that the clauses say the
// same thing is a separate question a solver has to answer.
DLL_PUBLIC void encodeDivUnderDivisorValue(
    SATSolver& solver, const std::vector<unsigned>& divisorVars,
    const std::vector<bool>& divisorBits,
    const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& resultVars, unsigned width,
    const std::vector<int>& source);

// The blocking lemmas one abstraction of this width may spend before the
// refinement gives up on it and encodes the operation exactly.
//
// A blocking lemma rules out one pair of operand values out of 2^(2W), so
// what one is worth falls away as the operands widen and a flat allowance
// means something quite different at either end of the range. The allowance
// is a rate instead -- `width / bv_term_abstraction_value_divisor` -- held
// under the flat ceiling `bv_term_abstraction_rounds`, which keeps every
// spelling that ceiling already had: zero still never escalates, and an
// explicit count still caps.
DLL_PUBLIC unsigned valueLemmaAllowance(const UserDefinedFlags& uf,
                                        unsigned width);

struct BVTermAbstraction
{
  ASTNode termNode;
  Kind opKind;
  ASTNode operands[3];
  unsigned numOperands;
  unsigned width;
  // Direct variables for this record's free result bits. The batch path may
  // leave this empty and use nodeToSATVar. The persistent incremental path
  // fills it so correctness does not depend on the canonical-reuse invariant:
  // if duplicate records ever arise, each still owns distinct inputs.
  std::vector<unsigned> resultSATVars;
  bool operandNegated[3] = {false, false, false};
  unsigned condSATVar = BV_ABSTRACTION_NO_VAR;
  bool defined = false;
  // Blocking lemmas spent on this one abstraction so far; see
  // bv_term_abstraction_rounds.
  unsigned blockedRounds = 0;
  // Algebraic schemas spent on it, counted separately: a schema is both
  // cheaper and stronger than a blocking lemma, so it does not eat the
  // budget that decides when to give up and encode the operation exactly.
  // It is bounded by the same number, though, because a candidate that
  // keeps landing on fresh powers of two would otherwise buy a solve for
  // each one.
  unsigned schemaRounds = 0;
  // Which of the unconditional schemas are already in the solver.
  uint64_t installedSchemas = 0;
  // Set on both records when this BVDIV/BVMOD pair has received its shared
  // low-prefix recomposition lemma. It cannot use installedSchemas because
  // that field describes one operation, while this fact belongs to two.
  bool divRemLowPrefixInstalled = false;
  // Set on both records after the stronger full-width modular recomposition
  // identity has been installed. The low-prefix fact may precede it, but
  // does not have to: if the current model already satisfies the prefix,
  // emitting it would make no progress and the full fact gets the round.
  bool divRemFullInstalled = false;
  // How far up the exact encoding has been pushed, for an escalation that
  // goes a piece at a time; see bv_term_abstraction_inc_bitblast. Zero
  // until the first piece, and equal to the width once `defined` is set.
  unsigned blastedBits = 0;
  // The bits of -operand[i], minted on first use by a schema that needs the
  // semantic operand and kept so later schemas do not pay for the same
  // negation circuit again.
  std::vector<unsigned> negatedOperand[2];
};

class DLL_PUBLIC BVAbstractionRefiner
{
  STPMgr* bm;

  std::vector<BVEQAbstraction> eqs_;
  std::vector<BVTermAbstraction> terms_;

  // Monotone across the session, including across a clear(): a driver
  // compares it either side of a round to learn whether that round found
  // anything, and a counter that went backwards would read as no progress.
  uint64_t refinements_ = 0;

  unsigned refineEqualities(SATSolver& solver,
                            const ToSATBase::ASTNodeToSATVar& nodeToSATVar);
  unsigned refineTerms(SATSolver& solver,
                       const ToSATBase::ASTNodeToSATVar& nodeToSATVar);

public:
  explicit BVAbstractionRefiner(STPMgr* bm_) : bm(bm_) {}

  bool empty() const { return eqs_.empty() && terms_.empty(); }
  bool hasEqualities() const { return !eqs_.empty(); }
  bool hasTerms() const { return !terms_.empty(); }

  // The records, for whoever mints them. Everything a refinement round
  // learns is written back into them, so an owner that discards its SAT
  // solver or its bit-blast has to discard these too.
  std::vector<BVEQAbstraction>& equalities() { return eqs_; }
  std::vector<BVTermAbstraction>& terms() { return terms_; }

  void clear()
  {
    eqs_.clear();
    terms_.clear();
  }

  uint64_t refinements() const { return refinements_; }

  // Keep a simplifying backend from eliminating anything a future lemma
  // will be written over.
  void freezeVariables(SATSolver& solver,
                       const ToSATBase::ASTNodeToSATVar& nodeToSATVar) const;

  // Check every record against the current SAT model and pin the ones the
  // model contradicts. Returns how many were pinned: zero means the
  // candidate is faithful and may be handed on.
  unsigned refine(SATSolver& solver,
                  const ToSATBase::ASTNodeToSATVar& nodeToSATVar);
};
}

#endif
