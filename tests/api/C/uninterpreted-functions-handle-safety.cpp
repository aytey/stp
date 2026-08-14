/********************************************************************
 * AUTHORS: OpenAI
 *
 * BEGIN DATE: August, 2026
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

#include "stp/c_interface.h"

// UF declarations can become inactive only through a parser scope today. Use
// the registry seam to create that state deterministically, then exercise it
// exclusively through the public C API.
#include "stp/STPManager/STP.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFDecl.h"

#include <cstdint>
#include <cstdlib>
#include <gtest/gtest.h>

namespace
{

int apiErrors = 0;
void countAPIError(const char*) { ++apiErrors; }
void ignoreAPIError(const char*) {}

TEST(UninterpretedFunctionsHandleSafety,
     InvalidAndInactiveDeclarationHandlesAreNonfatal)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;

  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  const unsigned domain[] = {8};
  UFDeclHandle declaration = vc_declareFun(vc, "f", domain, 1, 8);
  ASSERT_NE(nullptr, declaration);
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  const Expr actuals[] = {x};

  UFDeclHandle impossible =
      reinterpret_cast<UFDeclHandle>(static_cast<uintptr_t>(1));
  EXPECT_EQ(nullptr, vc_applyFun(vc, impossible, actuals, 1));
  EXPECT_EQ(nullptr, vc_applyFun(vc, static_cast<UFDeclHandle>(x), actuals, 1));

  stp::STP* engine = static_cast<stp::STP*>(vc);
  std::string diagnostic;
  const stp::UFDecl* internalDeclaration =
      engine->bm->getUFContext()->lookup("f");
  ASSERT_NE(nullptr, internalDeclaration);
  ASSERT_TRUE(engine->bm->getUFContext()->deactivate(
      internalDeclaration, &diagnostic));
  EXPECT_EQ(nullptr, vc_applyFun(vc, declaration, actuals, 1));
  EXPECT_GE(apiErrors, 3);

  vc_DeleteExpr(x);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety,
     DestroyedAndCrossContextDeclarationsAndActualsAreNonfatal)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;

  VC owner = vc_createValidityChecker();
  VC other = vc_createValidityChecker();
  vc_setFlag(owner, 'u');
  vc_setFlag(other, 'u');
  const unsigned domain[] = {8};
  UFDeclHandle fromOwner = vc_declareFun(owner, "owner_f", domain, 1, 8);
  UFDeclHandle fromOther = vc_declareFun(other, "other_f", domain, 1, 8);
  ASSERT_NE(nullptr, fromOwner);
  ASSERT_NE(nullptr, fromOther);

  Expr ownerX = vc_varExpr(owner, "owner_x", vc_bvType(owner, 8));
  Expr otherX = vc_varExpr(other, "other_x", vc_bvType(other, 8));
  const Expr otherActuals[] = {otherX};

  // Isolate declaration ownership from actual ownership: each call has only
  // one foreign input.
  EXPECT_EQ(nullptr, vc_applyFun(other, fromOwner, otherActuals, 1));
  EXPECT_EQ(nullptr, vc_applyFun(owner, fromOwner, otherActuals, 1));

  vc_DeleteExpr(ownerX);
  vc_Destroy(owner);

  // A declaration token whose owning checker is gone remains rejectable when
  // presented to a live checker; rejection must not inspect freed storage.
  EXPECT_EQ(nullptr, vc_applyFun(other, fromOwner, otherActuals, 1));
  Expr validApplication = vc_applyFun(other, fromOther, otherActuals, 1);
  EXPECT_NE(nullptr, validApplication);
  EXPECT_GE(apiErrors, 3);

  vc_DeleteExpr(validApplication);
  vc_DeleteExpr(otherX);
  vc_Destroy(other);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety, NullActualStorageIsNonfatal)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;

  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  const unsigned domain[] = {8};
  UFDeclHandle declaration = vc_declareFun(vc, "f", domain, 1, 8);
  ASSERT_NE(nullptr, declaration);
  const Expr nullActual[] = {nullptr};

  EXPECT_EQ(nullptr, vc_applyFun(vc, declaration, nullptr, 1));
  EXPECT_EQ(nullptr, vc_applyFun(vc, declaration, nullActual, 1));
  EXPECT_EQ(2, apiErrors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety, InvalidActualPointerDoesNotCrash)
{
  EXPECT_EXIT(
      {
        vc_registerErrorHandler(ignoreAPIError);
        VC vc = vc_createValidityChecker();
        vc_setFlag(vc, 'u');
        const unsigned domain[] = {8};
        UFDeclHandle declaration = vc_declareFun(vc, "f", domain, 1, 8);
        Expr invalid = reinterpret_cast<Expr>(static_cast<uintptr_t>(1));
        const Expr actuals[] = {invalid};
        Expr result = vc_applyFun(vc, declaration, actuals, 1);
        if (result != nullptr)
          std::_Exit(2);
        vc_Destroy(vc);
        std::_Exit(0);
      },
      ::testing::ExitedWithCode(0), ".*");
}

TEST(UninterpretedFunctionsHandleSafety, DestroyedActualPointerDoesNotCrash)
{
  EXPECT_EXIT(
      {
        vc_registerErrorHandler(ignoreAPIError);
        VC vc = vc_createValidityChecker();
        vc_setFlag(vc, 'u');
        const unsigned domain[] = {8};
        UFDeclHandle declaration = vc_declareFun(vc, "f", domain, 1, 8);
        Expr destroyed = vc_varExpr(vc, "x", vc_bvType(vc, 8));
        vc_DeleteExpr(destroyed);
        const Expr actuals[] = {destroyed};
        Expr result = vc_applyFun(vc, declaration, actuals, 1);
        if (result != nullptr)
          std::_Exit(2);
        vc_Destroy(vc);
        std::_Exit(0);
      },
      ::testing::ExitedWithCode(0), ".*");
}

TEST(UninterpretedFunctionsHandleSafety,
     ActualFromDestroyedContextDoesNotCrash)
{
  EXPECT_EXIT(
      {
        vc_registerErrorHandler(ignoreAPIError);
        VC owner = vc_createValidityChecker();
        VC target = vc_createValidityChecker();
        vc_setFlag(owner, 'u');
        vc_setFlag(target, 'u');
        Expr destroyedOwnerActual =
            vc_varExpr(owner, "x", vc_bvType(owner, 8));
        const unsigned domain[] = {8};
        UFDeclHandle declaration =
            vc_declareFun(target, "f", domain, 1, 8);
        vc_Destroy(owner);

        const Expr actuals[] = {destroyedOwnerActual};
        Expr result = vc_applyFun(target, declaration, actuals, 1);
        if (result != nullptr)
          std::_Exit(2);
        vc_Destroy(target);
        std::_Exit(0);
      },
      ::testing::ExitedWithCode(0), ".*");
}

TEST(UninterpretedFunctionsHandleSafety,
     DestroyedApplicationValueHandleDoesNotCrash)
{
  EXPECT_EXIT(
      {
        vc_registerErrorHandler(ignoreAPIError);
        VC vc = vc_createValidityChecker();
        vc_setFlag(vc, 'u');
        const unsigned domain[] = {8};
        UFDeclHandle declaration = vc_declareFun(vc, "f", domain, 1, 8);
        Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
        const Expr actuals[] = {x};
        Expr application = vc_applyFun(vc, declaration, actuals, 1);
        vc_DeleteExpr(application);

        Expr value = vc_getUFApplicationValue(vc, application);
        if (value != nullptr)
          std::_Exit(2);
        vc_DeleteExpr(x);
        vc_Destroy(vc);
        std::_Exit(0);
      },
      ::testing::ExitedWithCode(0), ".*");
}

TEST(UninterpretedFunctionsHandleSafety,
     DestroyedActualCannotBecomeValidThroughAddressReuse)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;

  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  const unsigned domain[] = {8};
  UFDeclHandle declaration = vc_declareFun(vc, "f", domain, 1, 8);
  ASSERT_NE(nullptr, declaration);
  Type bv8 = vc_bvType(vc, 8);
  Expr stale = vc_varExpr(vc, "stale_x", bv8);
  ASSERT_NE(nullptr, stale);
  vc_DeleteExpr(stale);

  // Expr is a legacy raw pointer, so the C layer quarantines only its tiny
  // wrapper storage after destruction. This bounded churn proves that an old
  // actual cannot become a newly allocated expression through pointer ABA.
  for (unsigned attempt = 0; attempt < 128; ++attempt)
  {
    Expr replacement = vc_varExpr(vc, "replacement_x", bv8);
    ASSERT_NE(nullptr, replacement);
    EXPECT_NE(stale, replacement);
    const Expr staleActuals[] = {stale};
    EXPECT_EQ(nullptr, vc_applyFun(vc, declaration, staleActuals, 1));
    vc_DeleteExpr(replacement);
  }

  EXPECT_GE(apiErrors, 128);
  vc_DeleteExpr(bv8);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety,
     DestroyedDeclarationCannotBecomeValidThroughAddressReuse)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;
  const unsigned domain[] = {8};

  VC original = vc_createValidityChecker();
  vc_setFlag(original, 'u');
  UFDeclHandle stale = vc_declareFun(original, "old_f", domain, 1, 8);
  ASSERT_NE(nullptr, stale);
  vc_Destroy(original);

  // Churn both managers and declarations. Opaque declaration tokens are
  // process-lifetime tombstones, so a replacement token must never reuse the
  // stale token's identity and the stale generation must remain rejectable on
  // every live checker regardless of allocator address reuse underneath it.
  for (unsigned attempt = 0; attempt < 128; ++attempt)
  {
    VC live = vc_createValidityChecker();
    vc_setFlag(live, 'u');
    UFDeclHandle replacement =
        vc_declareFun(live, "replacement_f", domain, 1, 8);
    ASSERT_NE(nullptr, replacement);
    EXPECT_NE(stale, replacement);
    Expr x = vc_varExpr(live, "x", vc_bvType(live, 8));
    const Expr actuals[] = {x};
    EXPECT_EQ(nullptr, vc_applyFun(live, stale, actuals, 1));
    vc_DeleteExpr(x);
    vc_Destroy(live);
  }

  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety,
     NamespaceRejectionDoesNotDisplaceExistingBinding)
{
  vc_registerErrorHandler(countAPIError);
  apiErrors = 0;

  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  const unsigned domain[] = {8};
  UFDeclHandle declaration = vc_declareFun(vc, "f", domain, 1, 8);
  ASSERT_NE(nullptr, declaration);
  EXPECT_EQ(nullptr, vc_declareFun(vc, "f", domain, 1, 8));
  EXPECT_EQ(nullptr, vc_varExpr(vc, "f", vc_bvType(vc, 8)));

  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  const Expr actuals[] = {x};
  Expr application = vc_applyFun(vc, declaration, actuals, 1);
  EXPECT_NE(nullptr, application);

  EXPECT_EQ(nullptr, vc_declareFun(vc, "x", domain, 1, 8));
  Expr xAgain = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  ASSERT_NE(nullptr, xAgain);
  EXPECT_EQ(getExprID(x), getExprID(xAgain));
  EXPECT_GE(apiErrors, 3);

  vc_DeleteExpr(xAgain);
  vc_DeleteExpr(application);
  vc_DeleteExpr(x);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsHandleSafety,
     BooleanApplicationUsesSourceSortEquality)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  const unsigned domain[] = {0};
  UFDeclHandle predicate = vc_declareFun(vc, "predicate", domain, 1, 0);
  ASSERT_NE(nullptr, predicate);
  Expr argument = vc_trueExpr(vc);
  const Expr actuals[] = {argument};
  Expr application = vc_applyFun(vc, predicate, actuals, 1);
  ASSERT_NE(nullptr, application);
  Expr expected = vc_falseExpr(vc);
  Expr equality = vc_eqExpr(vc, application, expected);
  ASSERT_NE(nullptr, equality);
  vc_assertFormula(vc, equality);
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_DeleteExpr(equality);
  vc_DeleteExpr(expected);
  vc_DeleteExpr(application);
  vc_DeleteExpr(argument);
  vc_Destroy(vc);
}

} // namespace
