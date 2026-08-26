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

#include "stp/c_interface.h"

#include <gtest/gtest.h>

#include <string>

namespace
{

VC abstractionChecker()
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');
  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION, 1);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 1);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_MULT, 1);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_SCHEMAS, 1);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_INC_BITBLAST, 1);
  vc_setInterfaceFlags(vc, BV_ABSTRACTION_WIDTH, 1);
  vc_setInterfaceFlags(vc, BV_EQ_REFINE_WIDTH, 1);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, 64);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_VALUE_DIVISOR, 0);
  vc_setInterfaceFlags(vc, DISTINCT_ORDERING, 1);
  return vc;
}

Expr murxlaDistinctRegression(VC vc)
{
  const int width = 70;
  Type type = vc_bvType(vc, width);
  Expr x0 = vc_varExpr(vc, "x0", type);
  Expr x1 = vc_varExpr(vc, "x1", type);

  const std::string maxSigned = "0" + std::string(width - 1, '1');
  Expr limit = vc_bvConstExprFromStr(vc, maxSigned.c_str());
  Expr masked = vc_bvNandExpr(vc, limit, x1);
  Expr shifted = vc_bvLeftShiftExprExpr(vc, width, x0, x0);
  Expr product = vc_bvMultExpr(vc, width, shifted, limit);
  Expr rotated = vc_bvConcatExpr(vc, vc_bvExtract(vc, x0, 20, 0),
                                 vc_bvExtract(vc, x0, 69, 21));

  Expr distinct[3] = {
      vc_notExpr(vc, vc_eqExpr(vc, product, masked)),
      vc_notExpr(vc, vc_eqExpr(vc, product, rotated)),
      vc_notExpr(vc, vc_eqExpr(vc, masked, rotated)),
  };
  return vc_andExprN(vc, distinct, 3);
}

} // namespace

// A Murxla-minimised session that repeats one formula twice at base level
// and three more times in the temporary scope used to emulate
// check-sat-assuming, which is what makes the driver offer the same wide
// multiplication and addition to the blaster more than once.
//
// Coverage rather than a regression: this answered correctly before the
// blaster shared the abstraction, because a free duplicate result is only
// wrong when the search picks a value the raw stack refutes, and here it
// never did. The query that does turn it into a wrong verdict is
// tests/query-files/incremental-tests/abstraction-shared-subterm.smt2.
TEST(bv_abstraction_incremental_model,
     RepeatedScopedFormulaProducesASemanticModel)
{
  VC vc = abstractionChecker();
  Expr formula = murxlaDistinctRegression(vc);
  vc_assertFormula(vc, formula);
  vc_assertFormula(vc, formula);

  vc_push(vc);
  vc_assertFormula(vc, formula);
  vc_assertFormula(vc, formula);
  vc_assertFormula(vc, formula);
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}
