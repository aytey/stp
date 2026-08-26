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

// A paired quotient and remainder can say what neither abstraction can say
// alone: x = q*s+r. The production rule keeps only the low three bits, so
// test both the relation and its deliberately unconstrained high bit.
#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/ToSat/BVExactEncoder.h"

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <memory>
#include <vector>

using namespace stp;

namespace
{

const unsigned WIDTH = 4;
const unsigned PREFIX = 3;
const unsigned VALUES = 1u << WIDTH;

std::vector<bool> bitsOf(unsigned value, unsigned width = WIDTH)
{
  std::vector<bool> bits(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

unsigned quotient(unsigned dividend, unsigned divisor, unsigned width)
{
  return divisor == 0 ? (1u << width) - 1 : dividend / divisor;
}

unsigned remainder(unsigned dividend, unsigned divisor)
{
  return divisor == 0 ? dividend : dividend % divisor;
}

bool referenceRelation(unsigned dividend, unsigned divisor,
                       unsigned quotientValue, unsigned remainderValue,
                       unsigned prefix = PREFIX)
{
  const unsigned mask = (1u << prefix) - 1;
  return (dividend & mask) ==
         ((quotientValue * divisor + remainderValue) & mask);
}

class BVDivRemSchemaTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  std::unique_ptr<SATSolver> makeSolver()
  {
    return std::unique_ptr<SATSolver>(createSATSolver(mgr.UserFlags));
  }

  std::vector<unsigned> makeVars(SATSolver& solver, unsigned width = WIDTH)
  {
    std::vector<unsigned> vars(width);
    for (unsigned i = 0; i < width; ++i)
    {
      vars[i] = solver.newVar();
      solver.setFrozen(vars[i]);
    }
    return vars;
  }

  ASTNode productNode(unsigned width = WIDTH)
  {
    const ASTNode quotient = mgr.CreateSymbol("dr_q", 0, width);
    const ASTNode divisor = mgr.CreateSymbol("dr_s", 0, width);
    return mgr.defaultNodeFactory->CreateTerm(BVMULT, width, quotient,
                                               divisor);
  }

  void pin(SATSolver& solver, const std::vector<unsigned>& vars,
           unsigned value)
  {
    SATSolver::vec_literals unit;
    for (unsigned i = 0; i < vars.size(); ++i)
    {
      unit.clear();
      unit.push(SATSolver::mkLit(vars[i], ((value >> i) & 1u) == 0));
      solver.addClause(unit);
    }
  }
};

} // namespace

TEST(BVDivRemSchema, actual_results_satisfy_recomposition_at_small_widths)
{
  for (unsigned width = 1; width <= 6; ++width)
  {
    const unsigned values = 1u << width;
    const unsigned prefix = std::min(PREFIX, width);
    for (unsigned dividend = 0; dividend < values; ++dividend)
      for (unsigned divisor = 0; divisor < values; ++divisor)
      {
        ASSERT_TRUE(divRemLowPrefixHolds(
            bitsOf(dividend, width), bitsOf(divisor, width),
            bitsOf(quotient(dividend, divisor, width), width),
            bitsOf(remainder(dividend, divisor), width), prefix))
            << "width=" << width << " dividend=" << dividend
            << " divisor=" << divisor;
        ASSERT_TRUE(divRemLowPrefixHolds(
            bitsOf(dividend, width), bitsOf(divisor, width),
            bitsOf(quotient(dividend, divisor, width), width),
            bitsOf(remainder(dividend, divisor), width), width))
            << "full identity at width=" << width
            << " dividend=" << dividend << " divisor=" << divisor;
      }
  }
}

TEST(BVDivRemSchema, value_predicate_matches_full_modular_recomposition)
{
  for (unsigned dividend = 0; dividend < VALUES; ++dividend)
    for (unsigned divisor = 0; divisor < VALUES; ++divisor)
      for (unsigned q = 0; q < VALUES; ++q)
        for (unsigned r = 0; r < VALUES; ++r)
          ASSERT_EQ(referenceRelation(dividend, divisor, q, r, WIDTH),
                    divRemLowPrefixHolds(bitsOf(dividend), bitsOf(divisor),
                                         bitsOf(q), bitsOf(r), WIDTH))
              << "dividend=" << dividend << " divisor=" << divisor
              << " q=" << q << " r=" << r;
}

TEST(BVDivRemSchema, value_predicate_matches_modular_recomposition)
{
  for (unsigned dividend = 0; dividend < VALUES; ++dividend)
    for (unsigned divisor = 0; divisor < VALUES; ++divisor)
      for (unsigned q = 0; q < VALUES; ++q)
        for (unsigned r = 0; r < VALUES; ++r)
          ASSERT_EQ(referenceRelation(dividend, divisor, q, r),
                    divRemLowPrefixHolds(bitsOf(dividend), bitsOf(divisor),
                                         bitsOf(q), bitsOf(r), PREFIX))
              << "dividend=" << dividend << " divisor=" << divisor
              << " q=" << q << " r=" << r;
}

TEST_F(BVDivRemSchemaTest, clauses_match_modular_recomposition)
{
  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  ASSERT_TRUE(solver->supportsAssumptions());

  const std::vector<unsigned> dividendVars = makeVars(*solver);
  const std::vector<unsigned> divisorVars = makeVars(*solver);
  const std::vector<unsigned> quotientVars = makeVars(*solver);
  const std::vector<unsigned> remainderVars = makeVars(*solver);
  encodeDivRemLowPrefix(*solver, dividendVars, divisorVars, quotientVars,
                        remainderVars, WIDTH, PREFIX);

  const std::vector<unsigned>* vars[4] = {
      &dividendVars, &divisorVars, &quotientVars, &remainderVars};
  for (unsigned dividend = 0; dividend < VALUES; ++dividend)
    for (unsigned divisor = 0; divisor < VALUES; ++divisor)
      for (unsigned q = 0; q < VALUES; ++q)
        for (unsigned r = 0; r < VALUES; ++r)
        {
          const unsigned values[4] = {dividend, divisor, q, r};
          SATSolver::vec_literals assumptions;
          for (unsigned v = 0; v < 4; ++v)
            for (unsigned i = 0; i < WIDTH; ++i)
              assumptions.push(SATSolver::mkLit(
                  (*vars[v])[i], ((values[v] >> i) & 1u) == 0));

          bool timedOut = false;
          const bool satisfiable =
              solver->solveWithAssumptions(assumptions, timedOut);
          ASSERT_FALSE(timedOut);
          ASSERT_EQ(referenceRelation(dividend, divisor, q, r), satisfiable)
              << "dividend=" << dividend << " divisor=" << divisor
              << " q=" << q << " r=" << r;
        }
}

TEST_F(BVDivRemSchemaTest, full_clauses_match_modular_recomposition)
{
  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  ASSERT_TRUE(solver->supportsAssumptions());

  const std::vector<unsigned> dividendVars = makeVars(*solver);
  const std::vector<unsigned> divisorVars = makeVars(*solver);
  const std::vector<unsigned> quotientVars = makeVars(*solver);
  const std::vector<unsigned> remainderVars = makeVars(*solver);
  BVExactEncoder(&mgr).encodeDivRemIdentity(
      *solver, productNode(), WIDTH, dividendVars, divisorVars, quotientVars,
      remainderVars);

  const std::vector<unsigned>* vars[4] = {
      &dividendVars, &divisorVars, &quotientVars, &remainderVars};
  for (unsigned dividend = 0; dividend < VALUES; ++dividend)
    for (unsigned divisor = 0; divisor < VALUES; ++divisor)
      for (unsigned q = 0; q < VALUES; ++q)
        for (unsigned r = 0; r < VALUES; ++r)
        {
          const unsigned values[4] = {dividend, divisor, q, r};
          SATSolver::vec_literals assumptions;
          for (unsigned v = 0; v < 4; ++v)
            for (unsigned i = 0; i < WIDTH; ++i)
              assumptions.push(SATSolver::mkLit(
                  (*vars[v])[i], ((values[v] >> i) & 1u) == 0));

          bool timedOut = false;
          const bool satisfiable =
              solver->solveWithAssumptions(assumptions, timedOut);
          ASSERT_FALSE(timedOut);
          ASSERT_EQ(referenceRelation(dividend, divisor, q, r, WIDTH),
                    satisfiable)
              << "dividend=" << dividend << " divisor=" << divisor
              << " q=" << q << " r=" << r;
        }
}

TEST_F(BVDivRemSchemaTest, refiner_pairs_identical_division_operands)
{
  // Both pair families are deliberately outside the qualified default
  // profile. Selecting them together checks the staging rule: where the low
  // prefix rejects the candidate it gets first refusal over the full circuit.
  mgr.UserFlags.bv_term_abstraction_schema_groups =
      bvSchemaGroupBit(BVSchemaGroup::DIVREM_PAIR) |
      bvSchemaGroupBit(BVSchemaGroup::DIVREM_FULL);
  NodeFactory* factory = mgr.defaultNodeFactory;
  const ASTNode dividend = mgr.CreateSymbol("dr_dividend", 0, WIDTH);
  const ASTNode divisor = mgr.CreateSymbol("dr_divisor", 0, WIDTH);
  const ASTNode div = factory->CreateTerm(BVDIV, WIDTH, dividend, divisor);
  const ASTNode rem = factory->CreateTerm(BVMOD, WIDTH, dividend, divisor);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction divRecord;
  divRecord.termNode = div;
  divRecord.opKind = BVDIV;
  divRecord.operands[0] = dividend;
  divRecord.operands[1] = divisor;
  divRecord.numOperands = 2;
  divRecord.width = WIDTH;
  refiner.terms().push_back(divRecord);

  BVTermAbstraction remRecord;
  remRecord.termNode = rem;
  remRecord.opKind = BVMOD;
  remRecord.operands[0] = dividend;
  remRecord.operands[1] = divisor;
  remRecord.numOperands = 2;
  remRecord.width = WIDTH;
  refiner.terms().push_back(remRecord);

  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  const std::vector<unsigned> dividendVars = makeVars(*solver);
  const std::vector<unsigned> divisorVars = makeVars(*solver);
  const std::vector<unsigned> quotientVars = makeVars(*solver);
  const std::vector<unsigned> remainderVars = makeVars(*solver);

  ToSATBase::ASTNodeToSATVar nodeToVars;
  nodeToVars[dividend] = dividendVars;
  nodeToVars[divisor] = divisorVars;
  nodeToVars[div] = quotientVars;
  nodeToVars[rem] = remainderVars;

  // x=13, s=3, but q=r=0: low three bits say 5=0, so the paired lemma
  // must reject this candidate before either record spends an individual
  // schema or blocking lemma.
  pin(*solver, dividendVars, 13);
  pin(*solver, divisorVars, 3);
  pin(*solver, quotientVars, 0);
  pin(*solver, remainderVars, 0);
  bool timedOut = false;
  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);

  EXPECT_EQ(1u, refiner.refine(*solver, nodeToVars));
  EXPECT_TRUE(refiner.terms()[0].divRemLowPrefixInstalled);
  EXPECT_TRUE(refiner.terms()[1].divRemLowPrefixInstalled);
  EXPECT_FALSE(refiner.terms()[0].divRemFullInstalled);
  EXPECT_FALSE(refiner.terms()[1].divRemFullInstalled);
  EXPECT_EQ(1u, refiner.terms()[0].schemaRounds);
  EXPECT_EQ(1u, refiner.terms()[1].schemaRounds);
  EXPECT_EQ(0u, refiner.terms()[0].blockedRounds);
  EXPECT_EQ(0u, refiner.terms()[1].blockedRounds);
  EXPECT_EQ(1u, mgr.UserFlags.coverage.bv_schema_lemmas);
  EXPECT_EQ(1u,
            mgr.UserFlags.coverage.bv_schema_group_lemmas[static_cast<unsigned>(
                BVSchemaGroup::DIVREM_PAIR)]);
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
  {
    if (i == static_cast<unsigned>(BVSchemaGroup::DIVREM_PAIR))
      continue;
    EXPECT_EQ(0u, mgr.UserFlags.coverage.bv_schema_group_lemmas[i]);
  }

  EXPECT_FALSE(solver->solve(timedOut));
  EXPECT_FALSE(timedOut);
}

// Incremental lowering can retain more than one abstraction record for a
// hash-consed term. The AST-keyed map then names whichever result was
// registered last, while each durable record owns the result variables its
// candidate actually uses. A paired lemma must inspect and constrain those
// record-owned variables on both sides, just like every single-record path.
TEST_F(BVDivRemSchemaTest, paired_lemma_uses_each_records_owned_result)
{
  mgr.UserFlags.bv_term_abstraction_schema_groups =
      bvSchemaGroupBit(BVSchemaGroup::DIVREM_PAIR);
  NodeFactory* factory = mgr.defaultNodeFactory;
  const ASTNode dividend = mgr.CreateSymbol("owned_dividend", 0, WIDTH);
  const ASTNode divisor = mgr.CreateSymbol("owned_divisor", 0, WIDTH);
  const ASTNode div = factory->CreateTerm(BVDIV, WIDTH, dividend, divisor);
  const ASTNode rem = factory->CreateTerm(BVMOD, WIDTH, dividend, divisor);

  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  const std::vector<unsigned> dividendVars = makeVars(*solver);
  const std::vector<unsigned> divisorVars = makeVars(*solver);
  const std::vector<unsigned> ownedQuotientVars = makeVars(*solver);
  const std::vector<unsigned> ownedRemainderVars = makeVars(*solver);
  const std::vector<unsigned> mappedQuotientVars = makeVars(*solver);
  const std::vector<unsigned> mappedRemainderVars = makeVars(*solver);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction divRecord;
  divRecord.termNode = div;
  divRecord.opKind = BVDIV;
  divRecord.operands[0] = dividend;
  divRecord.operands[1] = divisor;
  divRecord.numOperands = 2;
  divRecord.width = WIDTH;
  divRecord.resultSATVars = ownedQuotientVars;
  refiner.terms().push_back(divRecord);

  BVTermAbstraction remRecord;
  remRecord.termNode = rem;
  remRecord.opKind = BVMOD;
  remRecord.operands[0] = dividend;
  remRecord.operands[1] = divisor;
  remRecord.numOperands = 2;
  remRecord.width = WIDTH;
  remRecord.resultSATVars = ownedRemainderVars;
  refiner.terms().push_back(remRecord);

  ToSATBase::ASTNodeToSATVar nodeToVars;
  nodeToVars[dividend] = dividendVars;
  nodeToVars[divisor] = divisorVars;
  nodeToVars[div] = mappedQuotientVars;
  nodeToVars[rem] = mappedRemainderVars;

  // x=13 and s=3. The map's q=4,r=1 satisfies recomposition, while the
  // durable records' q=r=0 do not. Reading the map would miss the paired
  // violation; writing the lemma to the map would fail to block it.
  pin(*solver, dividendVars, 13);
  pin(*solver, divisorVars, 3);
  pin(*solver, ownedQuotientVars, 0);
  pin(*solver, ownedRemainderVars, 0);
  pin(*solver, mappedQuotientVars, 4);
  pin(*solver, mappedRemainderVars, 1);
  bool timedOut = false;
  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);

  EXPECT_EQ(1u, refiner.refine(*solver, nodeToVars));
  EXPECT_TRUE(refiner.terms()[0].divRemLowPrefixInstalled);
  EXPECT_TRUE(refiner.terms()[1].divRemLowPrefixInstalled);
  EXPECT_EQ(1u, mgr.UserFlags.coverage.bv_schema_lemmas);

  EXPECT_FALSE(solver->solve(timedOut));
  EXPECT_FALSE(timedOut);
}

TEST_F(BVDivRemSchemaTest,
       refiner_uses_full_identity_when_the_low_prefix_already_holds)
{
  mgr.UserFlags.bv_term_abstraction_schema_groups =
      bvSchemaGroupBit(BVSchemaGroup::DIVREM_PAIR) |
      bvSchemaGroupBit(BVSchemaGroup::DIVREM_FULL);
  NodeFactory* factory = mgr.defaultNodeFactory;
  const ASTNode dividend = mgr.CreateSymbol("full_dividend", 0, WIDTH);
  const ASTNode divisor = mgr.CreateSymbol("full_divisor", 0, WIDTH);
  const ASTNode div = factory->CreateTerm(BVDIV, WIDTH, dividend, divisor);
  const ASTNode rem = factory->CreateTerm(BVMOD, WIDTH, dividend, divisor);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction divRecord;
  divRecord.termNode = div;
  divRecord.opKind = BVDIV;
  divRecord.operands[0] = dividend;
  divRecord.operands[1] = divisor;
  divRecord.numOperands = 2;
  divRecord.width = WIDTH;
  refiner.terms().push_back(divRecord);

  BVTermAbstraction remRecord;
  remRecord.termNode = rem;
  remRecord.opKind = BVMOD;
  remRecord.operands[0] = dividend;
  remRecord.operands[1] = divisor;
  remRecord.numOperands = 2;
  remRecord.width = WIDTH;
  refiner.terms().push_back(remRecord);

  std::unique_ptr<SATSolver> solver = makeSolver();
  ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
  const std::vector<unsigned> dividendVars = makeVars(*solver);
  const std::vector<unsigned> divisorVars = makeVars(*solver);
  const std::vector<unsigned> quotientVars = makeVars(*solver);
  const std::vector<unsigned> remainderVars = makeVars(*solver);

  ToSATBase::ASTNodeToSATVar nodeToVars;
  nodeToVars[dividend] = dividendVars;
  nodeToVars[divisor] = divisorVars;
  nodeToVars[div] = quotientVars;
  nodeToVars[rem] = remainderVars;

  // x=8 and q*s+r=0 agree in their low three bits but not at full width.
  // Emitting the prefix would not reject this model, so the full identity
  // must take the round directly.
  pin(*solver, dividendVars, 8);
  pin(*solver, divisorVars, 3);
  pin(*solver, quotientVars, 0);
  pin(*solver, remainderVars, 0);
  bool timedOut = false;
  ASSERT_TRUE(solver->solve(timedOut));
  ASSERT_FALSE(timedOut);

  EXPECT_EQ(1u, refiner.refine(*solver, nodeToVars));
  EXPECT_FALSE(refiner.terms()[0].divRemLowPrefixInstalled);
  EXPECT_FALSE(refiner.terms()[1].divRemLowPrefixInstalled);
  EXPECT_TRUE(refiner.terms()[0].divRemFullInstalled);
  EXPECT_TRUE(refiner.terms()[1].divRemFullInstalled);
  EXPECT_EQ(1u, refiner.terms()[0].schemaRounds);
  EXPECT_EQ(1u, refiner.terms()[1].schemaRounds);
  EXPECT_EQ(0u, refiner.terms()[0].blockedRounds);
  EXPECT_EQ(0u, refiner.terms()[1].blockedRounds);
  EXPECT_EQ(1u, mgr.UserFlags.coverage.bv_schema_lemmas);
  EXPECT_EQ(1u,
            mgr.UserFlags.coverage.bv_schema_group_lemmas[static_cast<unsigned>(
                BVSchemaGroup::DIVREM_FULL)]);
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
  {
    if (i == static_cast<unsigned>(BVSchemaGroup::DIVREM_FULL))
      continue;
    EXPECT_EQ(0u, mgr.UserFlags.coverage.bv_schema_group_lemmas[i]);
  }

  EXPECT_FALSE(solver->solve(timedOut));
  EXPECT_FALSE(timedOut);
}
