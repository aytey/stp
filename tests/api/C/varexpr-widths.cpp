/********************************************************************
 * AUTHORS: Andrew Teylu
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
**********************/

#include "stp/c_interface.h"
#include <gtest/gtest.h>

// A zero-width bit-vector is not a sort, and the sort layer says so with an
// assertion in a header -- which means an abort on an asserting build and a
// zero-width value carried onward on a release one, where the legacy width
// checks read it as a Boolean.
//
// The parser and the command line were both closed against that. This entrance
// was not: an array-valued variable takes its element width here without any
// check, where vc_bvType has refused a zero width by the other route for years.
TEST(VarExprWidths, ArrayElementWidthMustBePositive)
{
  VC vc = vc_createValidityChecker();

  // The case that reached the assertion.
  EXPECT_EQ(NULL, vc_varExpr1(vc, "bad", 8, 0));

  // Its neighbours are unaffected: a real array, a plain bit-vector, and the
  // zero/zero spelling that means Bool rather than a zero-width anything.
  EXPECT_NE((Expr)NULL, vc_varExpr1(vc, "arr", 8, 8));
  EXPECT_NE((Expr)NULL, vc_varExpr1(vc, "bv", 0, 8));
  EXPECT_NE((Expr)NULL, vc_varExpr1(vc, "b", 0, 0));

  vc_Destroy(vc);
}
