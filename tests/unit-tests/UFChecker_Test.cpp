#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFChecker.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFLemma.h"

#include <gtest/gtest.h>
#include <map>

using namespace stp;

namespace
{

class Candidate final : public UFScalarCandidate
{
public:
  explicit Candidate(uint64_t version = 1) : version_(version) {}

  void set(const ASTNode& scalar, const UFConcreteValue& value)
  {
    values_[scalar] = value;
  }

  uint64_t version() const override { return version_; }

  bool read(const ASTNode& scalar, const SourceSort& expected,
            UFConcreteValue& value,
            std::string& diagnostic) const override
  {
    const std::map<ASTNode, UFConcreteValue>::const_iterator found =
        values_.find(scalar);
    if (found == values_.end())
    {
      diagnostic = "test candidate is missing a scalar";
      return false;
    }
    if (found->second.sort() != expected)
    {
      diagnostic = "test candidate scalar sort mismatch";
      return false;
    }
    value = found->second;
    return true;
  }

private:
  uint64_t version_;
  std::map<ASTNode, UFConcreteValue> values_;
};

struct UnaryFixture
{
  STPMgr manager;
  UFContext* context;
  const UFDecl* f;
  ASTNode x;
  ASTNode y;
  ASTNode fx;
  ASTNode fy;
  LoweredApplicationView view;

  UnaryFixture() : context(NULL), f(NULL)
  {
    manager.UserFlags.enable_uninterpreted_functions = true;
    context = manager.getUFContext();
    std::string diagnostic;
    f = context->declareFunction(
        "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
        &diagnostic);
    x = manager.CreateSourceSymbol("x", SourceSort::bitVector(8));
    y = manager.CreateSourceSymbol("y", SourceSort::bitVector(8));
    fx = context->apply(f, {x}, &diagnostic);
    fy = context->apply(f, {y}, &diagnostic);
    const ASTNode root = manager.defaultNodeFactory->CreateNode(EQ, fx, fy);
    UFLowering lowerer(&manager);
    view = lowerer.lowerCompletedRoot(root, UFSolveScope::batch(1));
  }

  Candidate candidate(uint64_t version, uint64_t xValue, uint64_t yValue,
                      uint64_t fxValue, uint64_t fyValue) const
  {
    Candidate result(version);
    for (const LoweredApplicationRecord& record : view.applications)
    {
      const bool isX = record.durableHandle == fx;
      result.set(record.namedActuals[0],
                 UFConcreteValue::fromUInt(8, isX ? xValue : yValue));
      result.set(record.resultSymbol,
                 UFConcreteValue::fromUInt(8, isX ? fxValue : fyValue));
    }
    return result;
  }
};

} // namespace

TEST(UFChecker, ReturnsStableUnaryConflictAndValidatedLemma)
{
  UnaryFixture fixture;
  const Candidate candidate = fixture.candidate(42, 3, 3, 10, 11);
  const UFCheckResult result = UFChecker::check(
      fixture.context->activeDeclarations(), fixture.view, candidate);

  ASSERT_TRUE(result.hasConflict()) << result.diagnostic;
  EXPECT_EQ(42u, result.conflicts[0].candidateVersion);
  EXPECT_EQ(fixture.f, result.conflicts[0].declaration);
  EXPECT_EQ(fixture.fx, result.conflicts[0].representativeHandle);
  EXPECT_EQ(fixture.fy, result.conflicts[0].conflictingHandle);
  ASSERT_EQ(1u, result.conflicts[0].arguments.size());
  EXPECT_EQ(UFConcreteValue::fromUInt(8, 3),
            result.conflicts[0].arguments[0].concreteValue);
  EXPECT_EQ(1u, result.stats.insertions);
  EXPECT_EQ(1u, result.stats.comparisons);

  UFAbstractLemma lemma;
  std::string diagnostic;
  ASSERT_TRUE(UFLemmaOracle::buildAndValidate(result.conflicts[0], lemma,
                                              diagnostic))
      << diagnostic;
  ASSERT_EQ(1u, lemma.premise.size());
  EXPECT_FALSE(lemma.evaluate(false, {true}));
  EXPECT_TRUE(lemma.evaluate(true, {true}));
  EXPECT_TRUE(lemma.evaluate(false, {false}));
}

namespace
{

// Four applications of one function, all reachable from a single root so the
// lowering keeps them in one view. Handed a candidate that gives every actual
// the same value and every result a different one, the bucket holds one
// representative and three records that disagree with it.
struct CollidingFixture
{
  STPMgr manager;
  UFContext* context;
  const UFDecl* f;
  std::vector<ASTNode> arguments;
  std::vector<ASTNode> applications;
  LoweredApplicationView view;

  CollidingFixture() : context(NULL), f(NULL)
  {
    manager.UserFlags.enable_uninterpreted_functions = true;
    context = manager.getUFContext();
    std::string diagnostic;
    f = context->declareFunction("f", {SourceSort::bitVector(8)},
                                 SourceSort::bitVector(8), &diagnostic);
    ASTVec conjuncts;
    for (size_t i = 0; i < 4; ++i)
    {
      const ASTNode argument = manager.CreateSourceSymbol(
          ("a" + std::to_string(i)).c_str(), SourceSort::bitVector(8));
      arguments.push_back(argument);
      applications.push_back(context->apply(f, {argument}, &diagnostic));
      conjuncts.push_back(manager.defaultNodeFactory->CreateNode(
          EQ, applications.back(), manager.CreateBVConst(8, i)));
    }
    const ASTNode root =
        manager.defaultNodeFactory->CreateNode(AND, conjuncts);
    UFLowering lowerer(&manager);
    view = lowerer.lowerCompletedRoot(root, UFSolveScope::batch(40));
  }

  // Every argument reads 7; result i reads i, so records 1..3 each disagree
  // with record 0.
  Candidate collidingCandidate(uint64_t version) const
  {
    Candidate result(version);
    for (const LoweredApplicationRecord& record : view.applications)
    {
      result.set(record.namedActuals[0], UFConcreteValue::fromUInt(8, 7));
      for (size_t i = 0; i < applications.size(); ++i)
        if (record.durableHandle == applications[i])
          result.set(record.resultSymbol, UFConcreteValue::fromUInt(8, i));
    }
    return result;
  }
};

} // namespace

TEST(UFChecker, CollectsEveryConflictOneCandidateExposes)
{
  CollidingFixture fixture;
  const UFCheckResult result =
      UFChecker::check(fixture.context->activeDeclarations(), fixture.view,
                       fixture.collidingCandidate(7));

  ASSERT_TRUE(result.hasConflict()) << result.diagnostic;
  // One bucket, one representative, three records disagreeing with it.
  ASSERT_EQ(3u, result.conflicts.size());
  EXPECT_EQ(1u, result.stats.insertions);
  EXPECT_EQ(3u, result.stats.comparisons);

  // Every conflict is against that one representative, is stamped with the
  // candidate it was read from, and reports a strictly increasing order.
  size_t previousOrder = 0;
  for (const UFCongruenceConflict& conflict : result.conflicts)
  {
    EXPECT_EQ(fixture.f, conflict.declaration);
    EXPECT_EQ(result.conflicts[0].representativeHandle,
              conflict.representativeHandle);
    EXPECT_NE(conflict.representativeHandle, conflict.conflictingHandle);
    EXPECT_EQ(7u, conflict.candidateVersion);
    EXPECT_LT(previousOrder, conflict.stableConflictOrder);
    previousOrder = conflict.stableConflictOrder;

    UFAbstractLemma lemma;
    std::string diagnostic;
    ASSERT_TRUE(UFLemmaOracle::buildAndValidate(conflict, lemma, diagnostic))
        << diagnostic;
    // Each one independently rejects the candidate it came from.
    EXPECT_FALSE(lemma.evaluate(false, std::vector<bool>(
                                           lemma.premise.size(), true)));
  }

  // A conflicting candidate publishes no model.
  EXPECT_TRUE(result.modelSeed.functions.empty());
}

TEST(UFChecker, ConflictCapStopsTheScanAndIsAPrefix)
{
  CollidingFixture fixture;
  const std::vector<const UFDecl*> declarations =
      fixture.context->activeDeclarations();
  const UFCheckPlan plan = UFChecker::validate(declarations, fixture.view);
  ASSERT_TRUE(plan.valid()) << plan.diagnostic();

  const UFCheckResult unlimited =
      UFChecker::check(plan, fixture.collidingCandidate(9), 0);
  ASSERT_EQ(3u, unlimited.conflicts.size());

  for (size_t cap = 1; cap <= 3; ++cap)
  {
    const UFCheckResult capped =
        UFChecker::check(plan, fixture.collidingCandidate(9), cap);
    ASSERT_TRUE(capped.hasConflict()) << capped.diagnostic;
    ASSERT_EQ(cap, capped.conflicts.size());
    // Capping only stops the scan early: what it does report is the same
    // prefix, in the same order, as the uncapped run.
    for (size_t i = 0; i < cap; ++i)
    {
      EXPECT_EQ(unlimited.conflicts[i].conflictingHandle,
                capped.conflicts[i].conflictingHandle);
      EXPECT_EQ(unlimited.conflicts[i].stableConflictOrder,
                capped.conflicts[i].stableConflictOrder);
    }
  }
}

TEST(UFChecker, PreparedPlanIsReusableAndRejectsMalformedViews)
{
  UnaryFixture fixture;
  const UFCheckPlan plan = UFChecker::validate(
      fixture.context->activeDeclarations(), fixture.view);
  ASSERT_TRUE(plan.valid()) << plan.diagnostic();

  const UFCheckResult conflict =
      UFChecker::check(plan, fixture.candidate(43, 3, 3, 10, 11));
  ASSERT_TRUE(conflict.hasConflict()) << conflict.diagnostic;
  const UFCheckResult consistent =
      UFChecker::check(plan, fixture.candidate(44, 3, 4, 10, 11));
  ASSERT_TRUE(consistent.consistent()) << consistent.diagnostic;

  LoweredApplicationView malformed = fixture.view;
  malformed.handleToResult.clear();
  const UFCheckPlan rejected = UFChecker::validate(
      fixture.context->activeDeclarations(), malformed);
  EXPECT_FALSE(rejected.valid());
  EXPECT_NE(std::string::npos, rejected.diagnostic().find("wrong size"));
}

TEST(UFChecker, PreservesNonInjectivity)
{
  UnaryFixture fixture;
  const Candidate candidate = fixture.candidate(2, 1, 2, 7, 7);
  const UFCheckResult result = UFChecker::check(
      fixture.context->activeDeclarations(), fixture.view, candidate);
  ASSERT_TRUE(result.consistent()) << result.diagnostic;
  ASSERT_EQ(1u, result.modelSeed.functions.size());
  EXPECT_EQ(2u, result.modelSeed.functions[0].cases.size());
}

TEST(UFChecker, KeepsTuplePositionsAndDeclarationsIndependent)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const SourceSort bv = SourceSort::bitVector(4);
  const UFDecl* f = context->declareFunction("f", {bv, bv}, bv, &diagnostic);
  const UFDecl* g = context->declareFunction("g", {bv, bv}, bv, &diagnostic);
  const ASTNode a = manager.CreateSourceSymbol("a", bv);
  const ASTNode b = manager.CreateSourceSymbol("b", bv);
  const ASTNode fab = context->apply(f, {a, b}, &diagnostic);
  const ASTNode fba = context->apply(f, {b, a}, &diagnostic);
  const ASTNode gab = context->apply(g, {a, b}, &diagnostic);
  const ASTNode root = manager.defaultNodeFactory->CreateNode(
      AND, manager.defaultNodeFactory->CreateNode(EQ, fab, fba),
      manager.defaultNodeFactory->CreateNode(EQ, fba, gab));
  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(2));

  Candidate candidate(3);
  for (const LoweredApplicationRecord& record : view.applications)
  {
    candidate.set(record.namedActuals[0],
                  UFConcreteValue::fromUInt(4,
                      record.namedActuals[0] == a ? 1 : 2));
    candidate.set(record.namedActuals[1],
                  UFConcreteValue::fromUInt(4,
                      record.namedActuals[1] == a ? 1 : 2));
    candidate.set(record.resultSymbol,
                  UFConcreteValue::fromUInt(4,
                      record.durableHandle == fab ? 3 :
                      record.durableHandle == fba ? 4 : 9));
  }
  const UFCheckResult result =
      UFChecker::check(context->activeDeclarations(), view, candidate);
  ASSERT_TRUE(result.consistent()) << result.diagnostic;
  ASSERT_EQ(2u, result.modelSeed.functions.size());
  EXPECT_EQ(f, result.modelSeed.functions[0].declaration);
  EXPECT_EQ(2u, result.modelSeed.functions[0].cases.size());
  EXPECT_EQ(g, result.modelSeed.functions[1].declaration);
  EXPECT_EQ(1u, result.modelSeed.functions[1].cases.size());
}

TEST(UFChecker, SupportsMixedBooleanAndBitVectorTuples)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const UFDecl* p = context->declareFunction(
      "p", {SourceSort::boolean(), SourceSort::bitVector(5)},
      SourceSort::boolean(), &diagnostic);
  const ASTNode a =
      manager.CreateSourceSymbol("a", SourceSort::boolean());
  const ASTNode b =
      manager.CreateSourceSymbol("b", SourceSort::boolean());
  const ASTNode x =
      manager.CreateSourceSymbol("x", SourceSort::bitVector(5));
  const ASTNode y =
      manager.CreateSourceSymbol("y", SourceSort::bitVector(5));
  const ASTNode left = context->apply(p, {a, x}, &diagnostic);
  const ASTNode right = context->apply(p, {b, y}, &diagnostic);
  UFLowering lowerer(&manager);
  const LoweredApplicationView view = lowerer.lowerCompletedRoot(
      manager.defaultNodeFactory->CreateNode(IFF, left, right),
      UFSolveScope::batch(3));

  Candidate candidate(4);
  for (const LoweredApplicationRecord& record : view.applications)
  {
    candidate.set(record.namedActuals[0], UFConcreteValue::boolean(true));
    candidate.set(record.namedActuals[1], UFConcreteValue::fromUInt(5, 17));
    candidate.set(record.resultSymbol,
                  UFConcreteValue::boolean(record.durableHandle == left));
  }
  const UFCheckResult result =
      UFChecker::check(context->activeDeclarations(), view, candidate);
  ASSERT_TRUE(result.hasConflict()) << result.diagnostic;
  EXPECT_EQ(SourceSort::Kind::Bool,
            result.conflicts[0].arguments[0].concreteValue.sort().kind());
  EXPECT_EQ(5u,
            result.conflicts[0].arguments[1].concreteValue.sort().bitVectorWidth());
  EXPECT_EQ(SourceSort::Kind::Bool,
            result.conflicts[0].leftResultValue.sort().kind());
}

TEST(UFChecker, PreservesValuesWiderThanMachineWords)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const SourceSort wide = SourceSort::bitVector(129);
  const UFDecl* f =
      context->declareFunction("wide", {wide}, wide, &diagnostic);
  ASSERT_NE(nullptr, f) << diagnostic;
  const ASTNode x = manager.CreateSourceSymbol("x129", wide);
  const ASTNode y = manager.CreateSourceSymbol("y129", wide);
  const ASTNode left = context->apply(f, {x}, &diagnostic);
  const ASTNode right = context->apply(f, {y}, &diagnostic);
  UFLowering lowerer(&manager);
  const LoweredApplicationView view = lowerer.lowerCompletedRoot(
      manager.defaultNodeFactory->CreateNode(EQ, left, right),
      UFSolveScope::batch(31));

  std::vector<uint8_t> tupleBytes(17, 0);
  tupleBytes[0] = 0xA5;
  tupleBytes[16] = 0xFF; // normalized to the one used bit at width 129
  const UFConcreteValue tuple =
      UFConcreteValue::bitVector(129, tupleBytes);
  ASSERT_EQ(17u, tuple.bytes().size());
  EXPECT_EQ(1u, tuple.bytes().back());

  std::vector<uint8_t> leftBytes(17, 0);
  std::vector<uint8_t> rightBytes(17, 0);
  leftBytes[8] = 0x40;
  rightBytes[12] = 0x20;
  Candidate candidate(32);
  for (const LoweredApplicationRecord& record : view.applications)
  {
    candidate.set(record.namedActuals[0], tuple);
    candidate.set(record.resultSymbol, UFConcreteValue::bitVector(
        129, record.durableHandle == left ? leftBytes : rightBytes));
  }
  const UFCheckResult result =
      UFChecker::check(context->activeDeclarations(), view, candidate);
  ASSERT_TRUE(result.hasConflict()) << result.diagnostic;
  EXPECT_EQ(129u,
            result.conflicts[0].arguments[0].concreteValue.sort().bitVectorWidth());
  EXPECT_NE(result.conflicts[0].leftResultValue,
            result.conflicts[0].rightResultValue);
}

TEST(UFChecker, OmitsOnlyIdenticalAndDuplicatePremises)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const SourceSort bv = SourceSort::bitVector(8);
  const UFDecl* f = context->declareFunction("f", {bv, bv, bv}, bv,
                                             &diagnostic);
  const ASTNode x = manager.CreateSourceSymbol("x", bv);
  const ASTNode y = manager.CreateSourceSymbol("y", bv);
  const ASTNode z = manager.CreateSourceSymbol("z", bv);
  const ASTNode left = context->apply(f, {x, x, z}, &diagnostic);
  const ASTNode right = context->apply(f, {x, y, y}, &diagnostic);
  UFLowering lowerer(&manager);
  const LoweredApplicationView view = lowerer.lowerCompletedRoot(
      manager.defaultNodeFactory->CreateNode(EQ, left, right),
      UFSolveScope::batch(4));

  Candidate candidate(5);
  for (const LoweredApplicationRecord& record : view.applications)
  {
    for (const ASTNode& arg : record.namedActuals)
      candidate.set(arg, UFConcreteValue::fromUInt(8, 6));
    candidate.set(record.resultSymbol,
                  UFConcreteValue::fromUInt(
                      8, record.durableHandle == left ? 1 : 2));
  }
  const UFCheckResult result =
      UFChecker::check(context->activeDeclarations(), view, candidate);
  ASSERT_TRUE(result.hasConflict()) << result.diagnostic;
  UFAbstractLemma lemma;
  ASSERT_TRUE(UFLemmaOracle::buildAndValidate(result.conflicts[0], lemma,
                                              diagnostic))
      << diagnostic;
  // Position 0 is reflexive. Positions 1 and 2 both normalize to x=y and
  // z=y respectively in this shape, so neither is dropped merely because
  // the candidate values agree.
  ASSERT_EQ(2u, lemma.premise.size());
  EXPECT_EQ(1u, lemma.premise[0].originalPosition);
  EXPECT_EQ(2u, lemma.premise[1].originalPosition);
}

TEST(UFChecker, DeduplicatesExactlyRepeatedPremiseAtoms)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const SourceSort bv = SourceSort::bitVector(8);
  const UFDecl* f = context->declareFunction("f", {bv, bv}, bv, &diagnostic);
  const ASTNode x = manager.CreateSourceSymbol("x", bv);
  const ASTNode y = manager.CreateSourceSymbol("y", bv);
  const ASTNode left = context->apply(f, {x, x}, &diagnostic);
  const ASTNode right = context->apply(f, {y, y}, &diagnostic);
  UFLowering lowerer(&manager);
  const LoweredApplicationView view = lowerer.lowerCompletedRoot(
      manager.defaultNodeFactory->CreateNode(EQ, left, right),
      UFSolveScope::batch(5));
  Candidate candidate(6);
  for (const LoweredApplicationRecord& record : view.applications)
  {
    for (const ASTNode& arg : record.namedActuals)
      candidate.set(arg, UFConcreteValue::fromUInt(8, 0));
    candidate.set(record.resultSymbol,
                  UFConcreteValue::fromUInt(
                      8, record.durableHandle == left ? 1 : 2));
  }
  const UFCheckResult result =
      UFChecker::check(context->activeDeclarations(), view, candidate);
  ASSERT_TRUE(result.hasConflict());
  UFAbstractLemma lemma;
  ASSERT_TRUE(UFLemmaOracle::buildAndValidate(result.conflicts[0], lemma,
                                              diagnostic));
  ASSERT_EQ(1u, lemma.premise.size());
  EXPECT_EQ(0u, lemma.premise[0].originalPosition);
}

TEST(UFChecker, ReturnsInternalErrorForUnobservableScalar)
{
  UnaryFixture fixture;
  Candidate incomplete(7);
  const LoweredApplicationRecord& first = fixture.view.applications[0];
  incomplete.set(first.namedActuals[0], UFConcreteValue::fromUInt(8, 1));
  const UFCheckResult result = UFChecker::check(
      fixture.context->activeDeclarations(), fixture.view, incomplete);
  EXPECT_EQ(UFCheckResult::Status::InternalError, result.status);
  EXPECT_NE(std::string::npos, result.diagnostic.find("missing"));
}

TEST(UFChecker, ProducesDefaultSeedForDeclarationWithoutObservation)
{
  UnaryFixture fixture;
  std::string diagnostic;
  const UFDecl* unused = fixture.context->declareFunction(
      "unused", {SourceSort::bitVector(3)}, SourceSort::boolean(),
      &diagnostic);
  ASSERT_NE(nullptr, unused);
  const Candidate candidate = fixture.candidate(8, 1, 2, 3, 4);
  const UFCheckResult result = UFChecker::check(
      fixture.context->activeDeclarations(), fixture.view, candidate);
  ASSERT_TRUE(result.consistent()) << result.diagnostic;
  ASSERT_EQ(2u, result.modelSeed.functions.size());
  EXPECT_EQ(unused, result.modelSeed.functions[1].declaration);
  EXPECT_TRUE(result.modelSeed.functions[1].cases.empty());
  EXPECT_EQ(UFConcreteValue::boolean(false),
            result.modelSeed.functions[1].defaultValue);
}
