// Native UF refinement clauses must be fully reified and, in the persistent
// adapter, every helper and semantic clause must carry the exact-stack block
// guard.  These tests drive the production checker and adapters with a
// concrete candidate, then inspect a backend-neutral recording SAT solver.

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/ToSat/ToSATBase.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFLowering.h"
#include "stp/UninterpretedFunctions/UFRefinement.h"

#include <gtest/gtest.h>
#include <algorithm>
#include <vector>

using namespace stp;

namespace
{

class RecordingSolver final : public SATSolver
{
public:
  explicit RecordingSolver(unsigned firstFresh) : next_(firstFresh) {}

  bool okay() const override { return true; }
  uint8_t modelValue(uint32_t) const override { return undef_literal(); }
  uint32_t newVar() override { return next_++; }
  uint32_t nVars() const override { return next_; }
  void printStats() const override {}
  void setVerbosity(int) override {}
  lbool true_literal() const override { return 0; }
  lbool false_literal() const override { return 1; }
  lbool undef_literal() const override { return 2; }

  unsigned nextVariable() const { return next_; }
  const std::vector<std::vector<int>>& clauses() const { return clauses_; }

protected:
  bool addClauseInternal(const vec_literals& clause) override
  {
    std::vector<int> copy;
    for (int i = 0; i < clause.size(); ++i)
      copy.push_back(toInt(clause[i]));
    clauses_.push_back(copy);
    return true;
  }
  bool solveInternal(bool&) override { return false; }

private:
  unsigned next_;
  std::vector<std::vector<int>> clauses_;
};

class RecordingToSAT final : public ToSATBase
{
public:
  explicit RecordingToSAT(STPMgr* manager) : ToSATBase(manager) {}

  bool CallSAT(SATSolver&, const ASTNode&, bool) override { return false; }
  ASTNodeToSATVar& SATVar_to_SymbolIndexMap() override { return bindings_; }
  void ClearAllTables() override { bindings_.clear(); }

  void bind(const ASTNode& node, std::initializer_list<unsigned> variables)
  {
    bindings_[node] = std::vector<unsigned>(variables);
  }

private:
  ASTNodeToSATVar bindings_;
};

struct RefinementFixture
{
  STPMgr manager;
  SubstitutionMap substitutions;
  Simplifier simplifier;
  ArrayTransformer transformer;
  AbsRefine_CounterExample counterexample;
  UFContext* context;
  const UFDecl* function;
  ASTNode a;
  ASTNode b;
  ASTNode left;
  ASTNode right;
  LoweredApplicationView batchView;
  LoweredApplicationView persistentView;
  RecordingToSAT tosat;

  RefinementFixture()
      : substitutions(&manager), simplifier(&manager, &substitutions),
        transformer(&manager, &simplifier),
        counterexample(&manager, &simplifier, &transformer), context(NULL),
        function(NULL), tosat(&manager)
  {
    manager.UserFlags.enable_uninterpreted_functions = true;
    context = manager.getUFContext();
    std::string diagnostic;
    function = context->declareFunction(
        "f", {SourceSort::boolean()}, SourceSort::bitVector(2),
        &diagnostic);
    EXPECT_NE(nullptr, function) << diagnostic;
    a = manager.CreateSourceSymbol("a", SourceSort::boolean());
    b = manager.CreateSourceSymbol("b", SourceSort::boolean());
    left = context->apply(function, {a}, &diagnostic);
    right = context->apply(function, {b}, &diagnostic);
    const ASTNode root = manager.defaultNodeFactory->CreateNode(
        NOT, manager.defaultNodeFactory->CreateNode(EQ, left, right));
    UFLowering lowerer(&manager);
    batchView = lowerer.lowerCompletedRoot(root, UFSolveScope::batch(1));
    persistentView = lowerer.lowerCompletedRoot(
        root, UFSolveScope::persistent(9, 7));

    populate(batchView);
    populate(persistentView);
  }

  void populate(const LoweredApplicationView& view)
  {
    ASSERT_EQ(2u, view.applications.size());
    for (const LoweredApplicationRecord& record : view.applications)
    {
      const bool isLeft = record.durableHandle == left;
      counterexample.InsertIntoCounterExampleMap(
          record.namedActuals[0], manager.CreateNode(TRUE));
      counterexample.InsertIntoCounterExampleMap(
          record.resultSymbol, manager.CreateBVConst(2, isLeft ? 1 : 2));
      if (isLeft)
      {
        tosat.bind(record.namedActuals[0], {0});
        tosat.bind(record.resultSymbol, {2, 3});
      }
      else
      {
        tosat.bind(record.namedActuals[0], {1});
        tosat.bind(record.resultSymbol, {4, 5});
      }
    }
  }
};

bool satisfies(const std::vector<std::vector<int>>& clauses,
               const std::vector<bool>& assignment)
{
  for (const std::vector<int>& clause : clauses)
  {
    bool clauseValue = false;
    for (const int literal : clause)
    {
      const unsigned variable = static_cast<unsigned>(literal) >> 1;
      const bool sign = (literal & 1) != 0;
      clauseValue = clauseValue || (assignment[variable] != sign);
    }
    if (!clauseValue)
      return false;
  }
  return true;
}

bool containsLiteral(const std::vector<int>& clause, int literal)
{
  return std::find(clause.begin(), clause.end(), literal) != clause.end();
}

} // namespace

TEST(UFRefinement, BatchCNFExactlyImplementsCongruenceImplication)
{
  RefinementFixture fixture;
  UFBatchAdapter adapter(&fixture.manager);
  adapter.beginQuery(&fixture.batchView);
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  ASSERT_TRUE(adapter.hasPendingLemma());

  RecordingSolver solver(6);
  adapter.encodePendingLemma(solver, &fixture.tosat);
  EXPECT_FALSE(adapter.hasPendingLemma());
  EXPECT_EQ(1u, adapter.lemmasEmitted());
  // Bool XNOR: 4; two BV-bit XNORs plus their conjunction: 11;
  // the semantic implication: 1.
  ASSERT_EQ(16u, solver.clauses().size());

  const unsigned helperCount = solver.nextVariable() - 6;
  for (unsigned original = 0; original < (1u << 6); ++original)
  {
    const bool argumentEqual =
        ((original >> 0) & 1u) == ((original >> 1) & 1u);
    const bool resultEqual =
        ((original >> 2) & 1u) == ((original >> 4) & 1u) &&
        ((original >> 3) & 1u) == ((original >> 5) & 1u);
    const bool expected = !argumentEqual || resultEqual;
    bool encoded = false;
    for (unsigned helpers = 0; helpers < (1u << helperCount); ++helpers)
    {
      std::vector<bool> assignment(solver.nextVariable(), false);
      for (unsigned bit = 0; bit < 6; ++bit)
        assignment[bit] = ((original >> bit) & 1u) != 0;
      for (unsigned bit = 0; bit < helperCount; ++bit)
        assignment[6 + bit] = ((helpers >> bit) & 1u) != 0;
      if (satisfies(solver.clauses(), assignment))
      {
        encoded = true;
        break;
      }
    }
    EXPECT_EQ(expected, encoded) << "original assignment " << original;
  }

  // A repeated candidate in one fresh query reuses both equality literals
  // and submits only the new candidate-blocking implication.
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  adapter.encodePendingLemma(solver, &fixture.tosat);
  EXPECT_EQ(17u, solver.clauses().size());
  EXPECT_EQ(2u, adapter.lemmasEmitted());
}

TEST(UFRefinement, PersistentCNFGuardsHelpersAndScopesItsCache)
{
  RefinementFixture fixture;
  UFPersistentAdapter adapter(&fixture.manager);
  RecordingSolver solver(6);

  // Positive block literal 200 has negation 201. Every helper definition
  // and the final semantic clause must contain that guard.
  adapter.beginBlock(&fixture.persistentView, 7, 9, 200);
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  adapter.encodePendingLemma(solver, &fixture.tosat);
  ASSERT_EQ(16u, solver.clauses().size());
  for (const std::vector<int>& clause : solver.clauses())
    EXPECT_TRUE(containsLiteral(clause, 201));

  // With the block inactive, its negated guard satisfies the entire bundle.
  std::vector<bool> inactive(101, false);
  EXPECT_TRUE(satisfies(solver.clauses(), inactive));

  // Same epoch and block: equality helpers are cached, so only one final
  // implication is emitted. A different block cannot reuse those helpers.
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  adapter.encodePendingLemma(solver, &fixture.tosat);
  ASSERT_EQ(17u, solver.clauses().size());
  EXPECT_TRUE(containsLiteral(solver.clauses().back(), 201));

  adapter.beginBlock(&fixture.persistentView, 7, 10, 202);
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  adapter.encodePendingLemma(solver, &fixture.tosat);
  ASSERT_EQ(33u, solver.clauses().size());
  for (std::size_t i = 17; i < 33; ++i)
    EXPECT_TRUE(containsLiteral(solver.clauses()[i], 203));

  // Epoch identity is also part of the cache key, and explicit epoch clear
  // must reclaim even a cache that would otherwise have matched.
  adapter.beginBlock(&fixture.persistentView, 8, 10, 204);
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  adapter.encodePendingLemma(solver, &fixture.tosat);
  ASSERT_EQ(49u, solver.clauses().size());
  adapter.clearEncodingEpoch();
  adapter.beginBlock(&fixture.persistentView, 8, 10, 206);
  ASSERT_EQ(UFCandidateOutcome::Conflict,
            adapter.checkCandidate(fixture.counterexample));
  adapter.encodePendingLemma(solver, &fixture.tosat);
  EXPECT_EQ(65u, solver.clauses().size());
}
