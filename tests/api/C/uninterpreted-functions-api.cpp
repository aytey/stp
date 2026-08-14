#include "stp/c_interface.h"
#include "stp/AST/ASTKind.h"
#include <gtest/gtest.h>

namespace
{
int errors = 0;
void countError(const char*) { ++errors; }
}

TEST(UninterpretedFunctionsCAPI, OwnershipTypingAndNonfatalRejection)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC first = vc_createValidityChecker();
  VC second = vc_createValidityChecker();
  vc_setFlag(first, 'u');
  vc_setFlag(second, 'u');

  const unsigned domain[] = {8, 0};
  UFDeclHandle f = vc_declareFun(first, "f", domain, 2, 16);
  ASSERT_NE(nullptr, f);
  EXPECT_EQ(nullptr, vc_declareFun(first, "f", domain, 2, 16));

  Expr bv8 = vc_varExpr(first, "x", vc_bvType(first, 8));
  Expr boolean = vc_varExpr(first, "b", vc_boolType(first));
  const Expr actuals[] = {bv8, boolean};
  Expr application = vc_applyFun(first, f, actuals, 2);
  ASSERT_NE(nullptr, application);
  EXPECT_EQ(static_cast<int>(stp::UF_APPLY), getExprKind(application));
  EXPECT_EQ(16, vc_getBVLength(first, application));

  EXPECT_EQ(nullptr, vc_applyFun(first, f, actuals, 1));
  const Expr wrong[] = {boolean, boolean};
  EXPECT_EQ(nullptr, vc_applyFun(first, f, wrong, 2));
  EXPECT_EQ(nullptr, vc_applyFun(second, f, actuals, 2));
  EXPECT_GE(errors, 4);

  vc_DeleteExpr(application);
  vc_DeleteExpr(bv8);
  vc_DeleteExpr(boolean);
  vc_Destroy(second);
  vc_Destroy(first);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsCAPI, DefaultOffAndZeroArityAreRejected)
{
  vc_registerErrorHandler(countError);
  errors = 0;
  VC vc = vc_createValidityChecker();
  const unsigned domain[] = {8};
  EXPECT_EQ(nullptr, vc_declareFun(vc, "off", domain, 1, 8));
  vc_setFlag(vc, 'u');
  EXPECT_EQ(nullptr, vc_declareFun(vc, "zero", nullptr, 0, 8));
  EXPECT_EQ(2, errors);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}
