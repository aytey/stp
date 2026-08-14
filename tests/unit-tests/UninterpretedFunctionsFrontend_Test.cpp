#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/Globals/Globals.h"
#include "stp/Parser/parser.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/cpp_interface.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFLowering.h"

#include <gtest/gtest.h>

using namespace stp;

TEST(UninterpretedFunctionsFrontend, IsDisabledByDefault)
{
  STPMgr manager;
  EXPECT_FALSE(manager.UserFlags.enable_uninterpreted_functions);

  std::string diagnostic;
  EXPECT_EQ(nullptr, manager.getUFContext()->declareFunction(
                      "f", {SourceSort::bitVector(8)},
                      SourceSort::bitVector(8), &diagnostic));
  EXPECT_EQ(0u, manager.getUFContext()->declarationCount());
  EXPECT_NE(std::string::npos, diagnostic.find("disabled"));
}

TEST(UninterpretedFunctionsFrontend, SignatureUsesRestrictedSourceSorts)
{
  EXPECT_THROW(UFSignature({}, SourceSort::boolean()), std::invalid_argument);
  EXPECT_THROW(UFSignature({SourceSort::floatingPoint(8, 24)},
                           SourceSort::boolean()),
               std::invalid_argument);
  EXPECT_THROW(UFSignature({SourceSort::roundingMode()},
                           SourceSort::boolean()),
               std::invalid_argument);
  EXPECT_THROW(UFSignature({SourceSort::bitVector(8)},
                           SourceSort::array(SourceSort::bitVector(8),
                                             SourceSort::bitVector(8))),
               std::invalid_argument);

  const UFSignature signature(
      {SourceSort::boolean(), SourceSort::bitVector(17)},
      SourceSort::bitVector(3));
  ASSERT_EQ(2u, signature.arity());
  EXPECT_EQ(SourceSort::Kind::Bool, signature.domain()[0].kind());
  EXPECT_EQ(17u, signature.domain()[1].bitVectorWidth());
  EXPECT_EQ(3u, signature.codomain().bitVectorWidth());
}

TEST(UninterpretedFunctionsFrontend,
     UnsupportedDirectSignaturesMutateNoRegistry)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  const SourceSort bv8 = SourceSort::bitVector(8);
  const SourceSort fp = SourceSort::floatingPoint(8, 24);
  const SourceSort rm = SourceSort::roundingMode();
  const SourceSort array = SourceSort::array(bv8, bv8);
  std::string diagnostic;

  EXPECT_EQ(nullptr,
            context->declareFunction("empty", {}, bv8, &diagnostic));
  EXPECT_EQ(nullptr,
            context->declareFunction("fp", {fp}, bv8, &diagnostic));
  EXPECT_EQ(nullptr,
            context->declareFunction("rm", {rm}, bv8, &diagnostic));
  EXPECT_EQ(nullptr,
            context->declareFunction("array", {array}, bv8, &diagnostic));
  EXPECT_EQ(nullptr, context->declareFunction(
                         "unknown", {SourceSort::unknown()}, bv8,
                         &diagnostic));
  EXPECT_EQ(nullptr,
            context->declareFunction("result", {bv8}, fp, &diagnostic));
  EXPECT_EQ(0u, context->declarationCount());
  EXPECT_EQ(0u, context->registeredApplicationCount());
}

TEST(UninterpretedFunctionsFrontend, DurableApplicationsAreTypedAndHashConsed)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();

  std::string diagnostic;
  const UFDecl* bv = context->declareFunction(
      "f", {SourceSort::bitVector(8), SourceSort::boolean()},
      SourceSort::bitVector(16), &diagnostic);
  const UFDecl* pred = context->declareFunction(
      "p", {SourceSort::bitVector(8)}, SourceSort::boolean(), &diagnostic);
  ASSERT_NE(nullptr, bv) << diagnostic;
  ASSERT_NE(nullptr, pred) << diagnostic;

  const ASTNode x =
      manager.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode b =
      manager.CreateSourceSymbol("b", SourceSort::boolean());
  const ASTNode app = context->apply(bv, {x, b}, &diagnostic);
  const ASTNode again = context->apply(bv, {x, b}, &diagnostic);
  const ASTNode boolApp = context->apply(pred, {x}, &diagnostic);

  EXPECT_EQ(UF_APPLY, app.GetKind());
  EXPECT_EQ(app, again);
  EXPECT_EQ(bv->identityNode(), app[0]);
  EXPECT_EQ(x, app[1]);
  EXPECT_EQ(b, app[2]);
  EXPECT_EQ(SourceSort::bitVector(16), app.GetSourceSort());
  EXPECT_EQ(BITVECTOR_TYPE, app.GetType());
  EXPECT_EQ(16u, app.GetValueWidth());
  EXPECT_EQ(SourceSort::boolean(), boolApp.GetSourceSort());
  EXPECT_EQ(BOOLEAN_TYPE, boolApp.GetType());
  EXPECT_TRUE(context->isRegisteredApplication(app));
  EXPECT_EQ(2u, context->registeredApplicationCount());
  EXPECT_TRUE(BVTypeCheck(app));
  EXPECT_TRUE(BVTypeCheck(boolApp));
}

TEST(UninterpretedFunctionsFrontend, FailedApplicationsRegisterNothing)
{
  STPMgr first;
  STPMgr second;
  first.UserFlags.enable_uninterpreted_functions = true;
  second.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = first.getUFContext();
  std::string diagnostic;
  const UFDecl* declaration = context->declareFunction(
      "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
      &diagnostic);
  ASSERT_NE(nullptr, declaration);

  const ASTNode wrong =
      first.CreateSourceSymbol("wrong", SourceSort::boolean());
  const ASTNode foreign =
      second.CreateSourceSymbol("foreign", SourceSort::bitVector(8));
  EXPECT_EQ(UNDEFINED,
            context->apply(declaration, ASTVec(), &diagnostic).GetKind());
  EXPECT_EQ(UNDEFINED,
            context->apply(declaration, {wrong}, &diagnostic).GetKind());
  EXPECT_EQ(UNDEFINED,
            context->apply(declaration, {foreign}, &diagnostic).GetKind());
  EXPECT_EQ(0u, context->registeredApplicationCount());

  ASSERT_TRUE(context->deactivate(declaration, &diagnostic));
  const ASTNode x =
      first.CreateSourceSymbol("x", SourceSort::bitVector(8));
  EXPECT_EQ(UNDEFINED,
            context->apply(declaration, {x}, &diagnostic).GetKind());
  EXPECT_EQ(0u, context->registeredApplicationCount());
}

TEST(UninterpretedFunctionsFrontend,
     MalformedParserApplicationRejectsWholeCommandAndContinues)
{
  STPMgr manager;
  Cpp_interface interface(manager, manager.defaultNodeFactory);
  STPMgr* const savedManager = GlobalParserBM;
  Cpp_interface* const savedInterface = GlobalParserInterface;
  GlobalParserBM = &manager;
  GlobalParserInterface = &interface;
  interface.startup();
  manager.UserFlags.enable_uninterpreted_functions = true;

  // The first assertion has a valid application followed by one with the
  // wrong arity. Its valid prefix and parser-side carrier must both roll back:
  // neither may become an assertion or a registered durable application.
  // Parsing must nevertheless continue to the independent assertion.
  const char* const input = R"(
    (set-logic QF_UFBV)
    (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
    (declare-const x (_ BitVec 8))
    (assert (and (= (f x) x) (= (f x x) x)))
    (assert (= x #x00))
  )";
  SMT2ScanString(input);
  EXPECT_EQ(0, SMT2Parse());
  smt2lex_destroy();

  const std::size_t applicationCount =
      manager.getUFContext()->registeredApplicationCount();
  const std::size_t declarationCount =
      manager.getUFContext()->declarationCount();
  const bool xIsUF = manager.getUFContext()->lookup("x") != nullptr;
  const ASTVec assertions = manager.GetAsserts();
  const bool containsApplication =
      !assertions.empty() && containsKind(assertions[0], UF_APPLY);
  const bool rejected = interface.currentCommandRejected();

  GlobalParserBM = savedManager;
  GlobalParserInterface = savedInterface;

  EXPECT_EQ(0u, applicationCount);
  EXPECT_EQ(1u, declarationCount);
  EXPECT_FALSE(xIsUF);
  ASSERT_EQ(1u, assertions.size());
  EXPECT_FALSE(containsApplication);
  EXPECT_FALSE(rejected);
}

TEST(UninterpretedFunctionsFrontend,
     MalformedFormalCannotLeakLexerOrTemporaryStateAcrossParses)
{
  STPMgr manager;
  Cpp_interface interface(manager, manager.defaultNodeFactory);
  STPMgr* const savedManager = GlobalParserBM;
  Cpp_interface* const savedInterface = GlobalParserInterface;
  GlobalParserBM = &manager;
  GlobalParserInterface = &interface;
  interface.startup();
  manager.UserFlags.enable_uninterpreted_functions = true;

  // The empty formal reaches function_param_open but supplies no identifier,
  // leaving the lexer's next-name expectation armed unless parse-abort cleanup
  // explicitly clears it.
  SMT2ScanString(R"(
    (set-logic QF_UFBV)
    (define-fun broken (() Bool) Bool true)
  )");
  EXPECT_NE(0, SMT2Parse());
  smt2lex_destroy();

  // A second parse on the same interface must start a fresh command and may
  // declare/use another formal normally.
  SMT2ScanString(R"(
    (define-fun good ((fresh Bool)) Bool fresh)
    (declare-const witness Bool)
    (assert (good witness))
  )");
  EXPECT_EQ(0, SMT2Parse());
  smt2lex_destroy();

  const ASTVec assertions = manager.GetAsserts();

  GlobalParserBM = savedManager;
  GlobalParserInterface = savedInterface;

  ASSERT_EQ(1u, assertions.size());
  EXPECT_EQ(SYMBOL, assertions[0].GetKind());
  EXPECT_STREQ("witness", assertions[0].GetName());
  EXPECT_EQ(SourceSort::boolean(), assertions[0].GetSourceSort());
}

TEST(UninterpretedFunctionsFrontend, SubstitutionRebuildsDurableApplication)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const UFDecl* declaration = context->declareFunction(
      "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
      &diagnostic);
  ASSERT_NE(nullptr, declaration);
  const ASTNode formal =
      manager.CreateSourceSymbol("formal", SourceSort::bitVector(8));
  const ASTNode actual = manager.CreateBVConst(8, 42);
  const ASTNode generic = context->apply(declaration, {formal}, &diagnostic);

  ASTNodeMap substitutions;
  substitutions.insert(std::make_pair(formal, actual));
  ASTNodeMap cache;
  const ASTNode specialized = SubstitutionMap::replace(
      generic, substitutions, cache, manager.defaultNodeFactory);

  ASSERT_EQ(UF_APPLY, specialized.GetKind());
  EXPECT_NE(generic, specialized);
  EXPECT_EQ(declaration->identityNode(), specialized[0]);
  EXPECT_EQ(actual, specialized[1]);
  EXPECT_TRUE(context->isRegisteredApplication(specialized));
}

TEST(UninterpretedFunctionsFrontend,
     CompletedRootLoweringBuildsOnlyReachableNestedClosure)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const UFDecl* declaration = context->declareFunction(
      "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
      &diagnostic);
  ASSERT_NE(nullptr, declaration) << diagnostic;

  const ASTNode x =
      manager.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode inner = context->apply(declaration, {x}, &diagnostic);
  const ASTNode outer = context->apply(declaration, {inner}, &diagnostic);
  const ASTNode unreachable = context->apply(
      declaration, {manager.CreateBVConst(8, 9)}, &diagnostic);
  ASSERT_FALSE(unreachable.IsNull());
  const ASTNode root =
      manager.defaultNodeFactory->CreateNode(EQ, outer, x);

  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(17));

  ASSERT_EQ(2u, view.size());
  EXPECT_EQ(root, view.publicRoot);
  EXPECT_FALSE(containsKind(view.semanticRoot, UF_APPLY));
  EXPECT_TRUE(view.handleToResult.find(inner) != view.handleToResult.end());
  EXPECT_TRUE(view.handleToResult.find(outer) != view.handleToResult.end());
  EXPECT_TRUE(view.handleToResult.find(unreachable) ==
              view.handleToResult.end());
  EXPECT_EQ(inner, view.applications[0].durableHandle);
  EXPECT_EQ(outer, view.applications[1].durableHandle);
  ASSERT_EQ(1u, view.applications[1].namedActuals.size());
  EXPECT_EQ(view.applications[0].resultSymbol,
            view.applications[1].namedActuals[0]);
  EXPECT_TRUE(context->isProtected(view.applications[0].resultSymbol));
  EXPECT_TRUE(context->isProtected(view.applications[1].resultSymbol));
  EXPECT_TRUE(context->isSolveScalar(view.applications[0].resultSymbol));
  EXPECT_TRUE(context->isSolveScalar(view.applications[1].resultSymbol));
}

TEST(UninterpretedFunctionsFrontend,
     CompletedRootLoweringNamesEachComplexActualOnce)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const UFDecl* f = context->declareFunction(
      "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
      &diagnostic);
  const UFDecl* g = context->declareFunction(
      "g", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
      &diagnostic);
  ASSERT_NE(nullptr, f);
  ASSERT_NE(nullptr, g);
  const ASTNode x =
      manager.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode one = manager.CreateBVConst(8, 1);
  const ASTNode complex = manager.defaultNodeFactory->CreateTerm(
      BVPLUS, 8, x, one);
  const ASTNode fx = context->apply(f, {complex}, &diagnostic);
  const ASTNode gx = context->apply(g, {complex}, &diagnostic);
  const ASTNode root = manager.defaultNodeFactory->CreateNode(EQ, fx, gx);

  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(root, UFSolveScope::batch(18));
  ASSERT_EQ(2u, view.size());
  ASSERT_EQ(1u, view.namingDefinitions.size());
  ASSERT_EQ(1u, view.nameToTerm.size());
  EXPECT_EQ(view.applications[0].namedActuals[0],
            view.applications[1].namedActuals[0]);
  EXPECT_TRUE(context->isProtected(view.applications[0].namedActuals[0]));
  EXPECT_TRUE(context->isSolveScalar(view.applications[0].namedActuals[0]));
  EXPECT_FALSE(containsKind(view.semanticRootWithDefinitions(&manager),
                            UF_APPLY));

  // The ordinary substitution funnel must not delete either a UF result or
  // its argument-name definition after the lowering barrier.
  SubstitutionMap substitutions(&manager);
  EXPECT_FALSE(context->activeInSolve());
  {
    UFContext::SolveScope scope(context);
    EXPECT_TRUE(context->activeInSolve());
    EXPECT_FALSE(substitutions.UpdateSolverMap(
        view.applications[0].resultSymbol, manager.CreateBVConst(8, 3)));
    EXPECT_FALSE(substitutions.UpdateSolverMap(
        view.applications[0].namedActuals[0], complex));
  }
  EXPECT_FALSE(context->activeInSolve());
}

TEST(UninterpretedFunctionsFrontend, BooleanLoweringRetainsBoolSourceSort)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  UFContext* context = manager.getUFContext();
  std::string diagnostic;
  const UFDecl* pred = context->declareFunction(
      "p", {SourceSort::boolean()}, SourceSort::boolean(), &diagnostic);
  ASSERT_NE(nullptr, pred);
  const ASTNode a =
      manager.CreateSourceSymbol("a", SourceSort::boolean());
  const ASTNode b =
      manager.CreateSourceSymbol("b", SourceSort::boolean());
  const ASTNode complex =
      manager.defaultNodeFactory->CreateNode(XOR, a, b);
  const ASTNode app = context->apply(pred, {complex}, &diagnostic);

  UFLowering lowerer(&manager);
  const LoweredApplicationView view =
      lowerer.lowerCompletedRoot(app, UFSolveScope::batch(19));
  ASSERT_EQ(1u, view.size());
  ASSERT_EQ(1u, view.namingDefinitions.size());
  EXPECT_EQ(SourceSort::boolean(), view.applications[0].resultSymbol.GetSourceSort());
  EXPECT_EQ(SourceSort::boolean(), view.applications[0].namedActuals[0].GetSourceSort());
  EXPECT_EQ(IFF, view.namingDefinitions[0].GetKind());
}

TEST(UninterpretedFunctionsFrontend, CppAPIReadsOnlyCertifiedDurableHandle)
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  STP solver(&manager);
  STP* const saved = GlobalSTP;
  GlobalSTP = &solver;
  {
    Cpp_interface interface(manager, manager.defaultNodeFactory);
    interface.setOption("produce-models", "true");
    std::string diagnostic;
    const UFDecl* function = interface.declareUninterpretedFunction(
        "f", {SourceSort::bitVector(8)}, SourceSort::bitVector(8),
        &diagnostic);
    ASSERT_NE(nullptr, function) << diagnostic;
    const ASTNode x = interface.CreateSourceSymbol(
        "x", SourceSort::bitVector(8));
    const ASTNode application =
        interface.applyUninterpretedFunction(function, {x}, &diagnostic);
    ASSERT_EQ(UF_APPLY, application.GetKind()) << diagnostic;
    const ASTNode expected = manager.CreateBVConst(8, 37);
    interface.AddAssert(manager.defaultNodeFactory->CreateNode(
        EQ, application, expected));
    manager.GetRunTimes()->start(RunTimes::Parsing);
    interface.checkSat(interface.getAssertVector());

    const ASTNode value =
        interface.getUninterpretedApplicationValue(application, &diagnostic);
    ASSERT_EQ(BVCONST, value.GetKind()) << diagnostic;
    EXPECT_EQ(37u, value.GetUnsignedConst());
    EXPECT_FALSE(manager.FoundIntroducedSymbolSet(value));

    interface.push();
    EXPECT_EQ(UNDEFINED,
              interface
                  .getUninterpretedApplicationValue(application, &diagnostic)
                  .GetKind());
  }
  GlobalSTP = saved;
}
