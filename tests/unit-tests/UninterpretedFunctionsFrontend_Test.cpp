#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFContext.h"

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
