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
  EXPECT_EQ(nullptr, vc_varExpr(first, "f", vc_bvType(first, 8)));

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
  EXPECT_GE(errors, 5);

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

TEST(UninterpretedFunctionsCAPI, CertifiedDurableValuesBatchAndRejection)
{
  vc_registerErrorHandler(countError);
  errors = 0;
  VC first = vc_createValidityChecker();
  VC second = vc_createValidityChecker();
  vc_setFlag(first, 'u');
  vc_setFlag(second, 'u');

  const unsigned domain[] = {8};
  UFDeclHandle f = vc_declareFun(first, "f", domain, 1, 8);
  ASSERT_NE(nullptr, f);
  Expr x = vc_varExpr(first, "x", vc_bvType(first, 8));
  const Expr actuals[] = {x};
  Expr application = vc_applyFun(first, f, actuals, 1);
  ASSERT_NE(nullptr, application);
  Expr expected = vc_bvConstExprFromInt(first, 8, 42);
  Expr equation = vc_eqExpr(first, application, expected);
  vc_assertFormula(first, equation);

  Expr falseQuery = vc_falseExpr(first);
  ASSERT_EQ(0, vc_query(first, falseQuery));
  vc_DeleteExpr(falseQuery);
  Expr value = vc_getUFApplicationValue(first, application);
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(42u, getBVUnsigned(value));
  vc_DeleteExpr(value);
  value = vc_getCounterExample(first, application);
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(42u, getBVUnsigned(value));
  vc_DeleteExpr(value);

  // A newly registered but unreachable handle was not active in this solve,
  // and a foreign context cannot read the first context's handle.
  Expr y = vc_varExpr(first, "y", vc_bvType(first, 8));
  const Expr otherActuals[] = {y};
  Expr inactive = vc_applyFun(first, f, otherActuals, 1);
  ASSERT_NE(nullptr, inactive);
  EXPECT_EQ(nullptr, vc_getUFApplicationValue(first, inactive));
  EXPECT_EQ(nullptr, vc_getUFApplicationValue(second, application));

  // Mutating the asserted root invalidates the certified map immediately.
  Expr tautology = vc_trueExpr(first);
  vc_assertFormula(first, tautology);
  vc_DeleteExpr(tautology);
  EXPECT_EQ(nullptr, vc_getUFApplicationValue(first, application));
  EXPECT_GE(errors, 3);

  vc_DeleteExpr(inactive);
  vc_DeleteExpr(y);
  vc_DeleteExpr(equation);
  vc_DeleteExpr(application);
  vc_DeleteExpr(x);
  vc_Destroy(second);
  vc_Destroy(first);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsCAPI, CertifiedDurableValuePersistentMode)
{
  vc_registerErrorHandler(countError);
  errors = 0;
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  vc_setFlag(vc, 'i');

  const unsigned domain[] = {0, 9};
  UFDeclHandle p = vc_declareFun(vc, "p", domain, 2, 0);
  ASSERT_NE(nullptr, p);
  Expr b = vc_varExpr(vc, "b", vc_boolType(vc));
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 9));
  const Expr actuals[] = {b, x};
  Expr application = vc_applyFun(vc, p, actuals, 2);
  ASSERT_NE(nullptr, application);
  vc_assertFormula(vc, application);

  Expr falseQuery = vc_falseExpr(vc);
  ASSERT_EQ(0, vc_query(vc, falseQuery));
  vc_DeleteExpr(falseQuery);
  Expr value = vc_getUFApplicationValue(vc, application);
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(1, vc_isBool(value));
  vc_DeleteExpr(value);

  // A real stack mutation clears the block-owned certified lookup map.
  vc_push(vc);
  EXPECT_EQ(nullptr, vc_getUFApplicationValue(vc, application));
  EXPECT_GE(errors, 1);

  // Re-certify the pushed block, then prove that the matching pop itself
  // invalidates the block-owned durable-handle map.
  falseQuery = vc_falseExpr(vc);
  ASSERT_EQ(0, vc_query(vc, falseQuery));
  vc_DeleteExpr(falseQuery);
  value = vc_getUFApplicationValue(vc, application);
  ASSERT_NE(nullptr, value);
  vc_DeleteExpr(value);
  vc_pop(vc);
  EXPECT_EQ(nullptr, vc_getUFApplicationValue(vc, application));

  vc_DeleteExpr(application);
  vc_DeleteExpr(x);
  vc_DeleteExpr(b);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}
