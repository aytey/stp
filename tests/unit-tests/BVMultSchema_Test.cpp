/***********
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
**********************/

// The algebraic facts an abstracted BVMULT is refined with, over every
// triple of operands and candidate product there is at four bits.
//
// Two things have to hold of each of them and they are not the same thing.
//
// A schema has to be *valid*: what its clauses say must be true of every
// pair of operands, because they are added to the solver unconditionally and
// are never taken back. A schema that is merely usually true turns a
// satisfiable query unsat, silently, and only on the inputs that reach it.
//
// And it has to be *violated* by the candidate that chose it. Refinement is
// only allowed to hand a round back when it has ruled the candidate out; a
// lemma the candidate already satisfies leaves the search free to offer the
// same one again, and the abstraction never converges. The refiner has an
// error for reaching undecided with nothing pending, so this shows up as an
// abort rather than a wrong answer -- but it shows up on someone else's
// query, not here, which is why it is pinned here.
//
// Four bits, exhaustively: 4096 triples of (a, b, t), each checked against
// every hand-written schema. Enough width for the trailing-zero and power-of-two
// cases to be distinct from each other and from the odd-bit one, and small
// enough that nothing has to be sampled.
#include "stp/ToSat/BVAbstractionRefiner.h"

#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <gtest/gtest.h>

#include <memory>
#include <vector>

using namespace stp;

namespace
{

const unsigned WIDTH = 4;
const unsigned VALUES = 1u << WIDTH;

std::vector<bool> bitsOf(unsigned value)
{
  std::vector<bool> bits(WIDTH);
  for (unsigned i = 0; i < WIDTH; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

unsigned valueOf(const std::vector<bool>& bits)
{
  unsigned value = 0;
  for (unsigned i = 0; i < bits.size(); ++i)
    if (bits[i])
      value |= (1u << i);
  return value;
}

unsigned truncatedProduct(unsigned a, unsigned b)
{
  return (a * b) & (VALUES - 1);
}

// What each schema's clauses say, written out again here rather than shared
// with the refiner: a bug copied into both would pass a test that compares
// them with each other.

// result[0] <-> a[0] & b[0]
bool oddHolds(unsigned a, unsigned b, unsigned t)
{
  return (t & 1u) == ((a & 1u) & (b & 1u));
}

// t = 0 and oddOperand[0] = 1 -> otherOperand = 0. This is the
// only nontrivial case of s = s << (x & (1 >> t)), the MUL8 spelling.
bool zeroProductOddOperandHolds(unsigned oddOperand, unsigned otherOperand,
                                unsigned t)
{
  return t != 0 || (oddOperand & 1u) == 0 || otherOperand == 0;
}

// t[i] -> some bit of `op` at or below i
bool trailingZerosHolds(unsigned op, unsigned t)
{
  for (unsigned bit = 0; bit < WIDTH; ++bit)
  {
    if (((t >> bit) & 1u) == 0)
      continue;
    bool below = false;
    for (unsigned j = 0; j <= bit; ++j)
      below = below || (((op >> j) & 1u) != 0);
    if (!below)
      return false;
  }
  return true;
}

// The consequent of the two value-guarded schemas: t = source << shift,
// truncated. Their premise is that the chosen operand holds the value the
// candidate gave it, which is true by construction wherever this is asked.
bool shiftHolds(unsigned source, unsigned shift, unsigned t)
{
  return ((source << shift) & (VALUES - 1)) == t;
}

unsigned negated(unsigned v)
{
  return (VALUES - v) & (VALUES - 1);
}

// The fact the chosen schema asserts, evaluated at this triple.
bool chosenSchemaHolds(const MulSchemaChoice& choice, unsigned a, unsigned b,
                       unsigned t)
{
  const unsigned ops[2] = {a, b};
  const unsigned other = ops[1 - choice.operand];
  switch (choice.schema)
  {
    case MulSchema::Odd:
      return oddHolds(a, b, t);
    case MulSchema::ZeroProductOddOperand:
      return zeroProductOddOperandHolds(ops[choice.operand], other, t);
    case MulSchema::TrailingZeros:
      return trailingZerosHolds(ops[choice.operand], t);
    case MulSchema::Pow2:
      return shiftHolds(other, choice.shift, t);
    case MulSchema::NegPow2:
      return shiftHolds(negated(other), choice.shift, t);
    case MulSchema::LowPrefix:
    {
      const unsigned mask = (1u << choice.shift) - 1;
      return (t & mask) == (truncatedProduct(a, b) & mask);
    }
    case MulSchema::Lemma:
    {
      unsigned count = 0;
      const MulLemma* lemmas = mulLemmaTable(count);
      EXPECT_LT(choice.lemmaIndex, count);
      return choice.lemmaIndex < count &&
             mulLemmaHolds(lemmas[choice.lemmaIndex],
                           bitsOf(ops[choice.operand]), bitsOf(other),
                           bitsOf(t));
    }
    case MulSchema::None:
      break;
  }
  return true;
}

MulSchemaChoice choose(unsigned a, unsigned b, unsigned t,
                       uint64_t installed = 0)
{
  return chooseMulSchema(bitsOf(a), bitsOf(b), bitsOf(t), installed);
}

class BVMultSchemaTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  bool zeroProductCircuitPermits(unsigned oddOperand, unsigned otherOperand,
                                 unsigned t)
  {
    std::unique_ptr<SATSolver> solver(createSATSolver(mgr.UserFlags));
    EXPECT_TRUE(solver != NULL) << "no SAT backend was compiled in";

    std::vector<unsigned> oddVars(WIDTH), otherVars(WIDTH), tVars(WIDTH);
    for (unsigned i = 0; i < WIDTH; ++i)
    {
      oddVars[i] = solver->newVar();
      otherVars[i] = solver->newVar();
      tVars[i] = solver->newVar();
      solver->setFrozen(oddVars[i]);
      solver->setFrozen(otherVars[i]);
      solver->setFrozen(tVars[i]);
    }

    encodeMulZeroProductOddOperand(*solver, oddVars, otherVars, tVars, WIDTH);

    SATSolver::vec_literals unit;
    const unsigned values[3] = {oddOperand, otherOperand, t};
    const std::vector<unsigned>* vars[3] = {&oddVars, &otherVars, &tVars};
    for (unsigned v = 0; v < 3; ++v)
      for (unsigned i = 0; i < WIDTH; ++i)
      {
        unit.clear();
        unit.push(
            SATSolver::mkLit((*vars[v])[i], ((values[v] >> i) & 1u) == 0));
        solver->addClause(unit);
      }

    bool timedOut = false;
    const bool sat = solver->solve(timedOut);
    EXPECT_FALSE(timedOut);
    return sat;
  }
};

} // namespace

// Valid: every fact any of the five can assert is true of the real product,
// whichever operand it is read over and whatever the schema was chosen for.
// This is the property that keeps the clauses from removing a model the
// query has.
TEST(bv_mult_schema, EveryFactHoldsOfTheRealProduct)
{
  for (unsigned a = 0; a < VALUES; ++a)
    for (unsigned b = 0; b < VALUES; ++b)
    {
      const unsigned t = truncatedProduct(a, b);

      EXPECT_TRUE(oddHolds(a, b, t)) << "a=" << a << " b=" << b;
      EXPECT_TRUE(zeroProductOddOperandHolds(a, b, t))
          << "a=" << a << " b=" << b;
      EXPECT_TRUE(zeroProductOddOperandHolds(b, a, t))
          << "a=" << a << " b=" << b;
      EXPECT_TRUE(trailingZerosHolds(a, t)) << "a=" << a << " b=" << b;
      EXPECT_TRUE(trailingZerosHolds(b, t)) << "a=" << a << " b=" << b;
      EXPECT_TRUE(exactLowPrefixHolds(BVMULT, bitsOf(a), bitsOf(b), bitsOf(t),
                                      3))
          << "a=" << a << " b=" << b;

      // The two value-guarded ones, wherever their premise is met.
      for (unsigned i = 0; i < 2; ++i)
      {
        const unsigned chosen = (i == 0) ? a : b;
        const unsigned other = (i == 0) ? b : a;
        for (unsigned k = 0; k < WIDTH; ++k)
        {
          if (chosen == (1u << k))
          {
            EXPECT_TRUE(shiftHolds(other, k, t))
                << "a=" << a << " b=" << b << " k=" << k;
          }
          if (negated(chosen) == (1u << k) && chosen != (1u << k))
          {
            EXPECT_TRUE(shiftHolds(negated(other), k, t))
                << "a=" << a << " b=" << b << " k=" << k;
          }
        }
      }
    }
}

// Nothing is spent on a candidate that is already right. The refiner only
// calls this over a product it has just found wrong, but the guard belongs
// in the function and not only at its call site: a schema chosen over a
// faithful candidate would be a lemma that blocks nothing.
TEST(bv_mult_schema, NothingIsChosenWhenTheProductIsCorrect)
{
  for (unsigned a = 0; a < VALUES; ++a)
    for (unsigned b = 0; b < VALUES; ++b)
      EXPECT_EQ(MulSchema::None,
                choose(a, b, truncatedProduct(a, b)).schema)
          << "a=" << a << " b=" << b;
}

// Violated: whatever is chosen, the candidate contradicts it. This is what
// makes the round progress -- the clauses rule this candidate out, so the
// search cannot offer it again.
TEST(bv_mult_schema, WhateverIsChosenTheCandidateContradictsIt)
{
  for (unsigned a = 0; a < VALUES; ++a)
    for (unsigned b = 0; b < VALUES; ++b)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        if (t == truncatedProduct(a, b))
          continue;
        const MulSchemaChoice choice = choose(a, b, t);
        if (choice.schema == MulSchema::None)
          continue;
        EXPECT_FALSE(chosenSchemaHolds(choice, a, b, t))
            << "a=" << a << " b=" << b << " t=" << t
            << " schema=" << (int)choice.schema;
      }
}

// A power-of-two operand is the case worth having: the shift is the whole
// product, so one lemma settles every value of the other operand where a
// blocking lemma settles one pair. It is therefore always taken when it
// applies, and the exponent handed back is the one the shift needs.
TEST(bv_mult_schema, APowerOfTwoOperandIsAlwaysTakenAsTheShift)
{
  for (unsigned k = 0; k < WIDTH; ++k)
  {
    const unsigned pow2 = 1u << k;
    for (unsigned other = 0; other < VALUES; ++other)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        if (t == truncatedProduct(pow2, other))
          continue;

        const MulSchemaChoice first = choose(pow2, other, t);
        EXPECT_EQ(MulSchema::Pow2, first.schema);
        EXPECT_EQ(0u, first.operand);
        EXPECT_EQ(k, first.shift);

        // ... and read over the second operand just the same, unless the
        // first one is a power of two too and gets there first.
        const MulSchemaChoice second = choose(other, pow2, t);
        EXPECT_EQ(MulSchema::Pow2, second.schema);
        if (second.operand == 1u)
        {
          EXPECT_EQ(k, second.shift);
        }
      }
  }
}

// The negated form, which is the one that needs a negation circuit under it.
// -2^k excludes the powers of two themselves, so the minimum signed value --
// which is its own negation -- goes to the schema above rather than this one.
TEST(bv_mult_schema, ANegatedPowerOfTwoOperandBecomesAShiftOfTheNegatedOther)
{
  for (unsigned a = 0; a < VALUES; ++a)
  {
    const unsigned neg = negated(a);
    bool isNegPow2 = false;
    unsigned k = 0;
    for (unsigned e = 0; e < WIDTH; ++e)
      if (neg == (1u << e) && a != (1u << e))
      {
        isNegPow2 = true;
        k = e;
      }
    if (!isNegPow2)
      continue;

    for (unsigned b = 0; b < VALUES; ++b)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        if (t == truncatedProduct(a, b))
          continue;
        const MulSchemaChoice choice = choose(a, b, t);
        // A power of two on the other side outranks it; nothing else can.
        if (choice.schema == MulSchema::Pow2)
          continue;
        EXPECT_EQ(MulSchema::NegPow2, choice.schema)
            << "a=" << a << " b=" << b << " t=" << t;
        EXPECT_EQ(0u, choice.operand);
        EXPECT_EQ(k, choice.shift);
      }
  }
}

// A candidate that gives the product fewer trailing zeros than an operand
// has is refused by the fact that says it cannot, and the fact is read over
// the operand that actually has them.
TEST(bv_mult_schema, TooFewTrailingZerosIsRefusedOverTheOperandThatHasThem)
{
  // 6 = 0b0110 has one trailing zero and is not a power of two either way,
  // so nothing above this schema applies; an odd product contradicts it.
  const MulSchemaChoice overSecond = choose(3, 6, 1);
  EXPECT_EQ(MulSchema::TrailingZeros, overSecond.schema);
  EXPECT_EQ(1u, overSecond.operand);

  const MulSchemaChoice overFirst = choose(6, 3, 1);
  EXPECT_EQ(MulSchema::TrailingZeros, overFirst.schema);
  EXPECT_EQ(0u, overFirst.operand);
}

// An unconditional fact already in the solver is never chosen again. It
// cannot be contradicted twice -- the clauses that carry it are permanent --
// so a second choice would mean the clauses do not say what they are meant
// to, and re-emitting them would be paying a round for nothing.
TEST(bv_mult_schema, AnInstalledFactIsNeverChosenAgain)
{
  uint64_t all = MUL_SCHEMA_INSTALLED_ODD |
                 MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0 |
                 MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1 |
                 MUL_SCHEMA_INSTALLED_ZERO_PRODUCT_ODD_0 |
                 MUL_SCHEMA_INSTALLED_ZERO_PRODUCT_ODD_1 |
                 MUL_SCHEMA_INSTALLED_LOW_PREFIX;
  unsigned lemmaCount = 0;
  mulLemmaTable(lemmaCount);
  for (unsigned i = 0; i < lemmaCount; ++i)
    for (unsigned operand = 0; operand < 2; ++operand)
      all |= mulLemmaInstalledBit(i, operand);

  for (unsigned a = 0; a < VALUES; ++a)
    for (unsigned b = 0; b < VALUES; ++b)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        const MulSchema schema = choose(a, b, t, all).schema;
        EXPECT_NE(MulSchema::Odd, schema);
        EXPECT_NE(MulSchema::TrailingZeros, schema);
        EXPECT_NE(MulSchema::ZeroProductOddOperand, schema);
        EXPECT_NE(MulSchema::LowPrefix, schema);
        EXPECT_NE(MulSchema::Lemma, schema);
      }

  // One at a time: the two readings of the trailing-zero fact are separate
  // lemmas and are installed separately.
  const MulSchemaChoice stillFirst =
      choose(6, 3, 1, MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1);
  EXPECT_EQ(MulSchema::TrailingZeros, stillFirst.schema);
  EXPECT_EQ(0u, stillFirst.operand);
}

TEST(bv_mult_schema, AResidualLowBitErrorTakesTheExactPrefix)
{
  uint64_t installed = MUL_SCHEMA_INSTALLED_ODD |
                       MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0 |
                       MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1 |
                       MUL_SCHEMA_INSTALLED_ZERO_PRODUCT_ODD_0 |
                       MUL_SCHEMA_INSTALLED_ZERO_PRODUCT_ODD_1;
  unsigned lemmaCount = 0;
  mulLemmaTable(lemmaCount);
  for (unsigned i = 0; i < lemmaCount; ++i)
    for (unsigned operand = 0; operand < 2; ++operand)
      installed |= mulLemmaInstalledBit(i, operand);

  const MulSchemaChoice choice = choose(3, 5, 8, installed);
  EXPECT_EQ(MulSchema::LowPrefix, choice.schema);
  EXPECT_EQ(3u, choice.shift);
  EXPECT_FALSE(chosenSchemaHolds(choice, 3, 5, 8));

  EXPECT_EQ(MulSchema::None,
            choose(3, 5, 8, installed | MUL_SCHEMA_INSTALLED_LOW_PREFIX)
                .schema);
}

// The odd-bit fact remains ahead of the zero-product fact, and it is reached:
// a candidate whose product has the wrong low bit while both operands are odd
// contradicts nothing above it.
TEST(bv_mult_schema, TheOddBitFactPrecedesTheZeroProductFact)
{
  // 3 * 5 = 15; a candidate of 14 is even where the product is odd, and
  // neither operand is a power of two or the negation of one at this width.
  const MulSchemaChoice choice = choose(3, 5, 14);
  EXPECT_EQ(MulSchema::Odd, choice.schema);
  EXPECT_FALSE(oddHolds(3, 5, 14));
}

// Once the four earlier facts all agree with a wrong zero product, an odd
// operand still proves that a nonzero other operand cannot have produced it.
// The two readings are installed independently because multiplication is
// commutative but the implication names which operand is odd.
TEST(bv_mult_schema, AnOddOperandRefusesAWrongZeroProduct)
{
  const MulSchemaChoice first = choose(3, 6, 0);
  EXPECT_EQ(MulSchema::ZeroProductOddOperand, first.schema);
  EXPECT_EQ(0u, first.operand);
  EXPECT_FALSE(chosenSchemaHolds(first, 3, 6, 0));

  const MulSchemaChoice second = choose(6, 3, 0);
  EXPECT_EQ(MulSchema::ZeroProductOddOperand, second.schema);
  EXPECT_EQ(1u, second.operand);
  EXPECT_FALSE(chosenSchemaHolds(second, 6, 3, 0));

  const MulSchemaChoice firstInstalled =
      choose(3, 6, 0, MUL_SCHEMA_INSTALLED_ZERO_PRODUCT_ODD_0);
  EXPECT_NE(MulSchema::ZeroProductOddOperand, firstInstalled.schema);
}

// The compact implication circuit used by the refiner is equivalent to the
// published shift expression's only nontrivial case, over every triple.
TEST_F(BVMultSchemaTest, TheZeroProductCircuitAgreesWithThePredicate)
{
  for (unsigned oddOperand = 0; oddOperand < VALUES; ++oddOperand)
    for (unsigned otherOperand = 0; otherOperand < VALUES; ++otherOperand)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        const bool want =
            zeroProductOddOperandHolds(oddOperand, otherOperand, t);
        ASSERT_EQ(want, zeroProductCircuitPermits(oddOperand, otherOperand, t))
            << "oddOperand=" << oddOperand << " otherOperand=" << otherOperand
            << " t=" << t;
      }
}

// Round trip through the bit vectors the refiner passes, so that a change to
// the bit order shows up here rather than as a wrong lemma.
TEST(bv_mult_schema, BitsAndValuesAgree)
{
  for (unsigned v = 0; v < VALUES; ++v)
    EXPECT_EQ(v, valueOf(bitsOf(v)));
}
