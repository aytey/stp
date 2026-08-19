/***********
AUTHORS: Andrew Teylu

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

// Reading the model value of a floating-point term the solved query never
// mentioned.
//
// The value is a function of the model, not of the assertion stack: nothing
// about a float has to be asserted for the float to have a value once the
// bit-vectors under it do. The batch driver answers such a question, and so
// does the SMT-LIB2 frontend. The incremental driver aborted the process:
//
//   Fatal Error: floating-point model evaluation has no solve encoding context
//
// out of vc_getCounterExample -- a legal C API call, with no return value to
// check and nothing an embedder could do about it.
//
// The cause was what the driver published to the model machinery rather than
// how it evaluated anything. Its floating-point encoding context is made
// lazily, on first use *during encoding*, and it installed the context only
// when it had one -- so a stack with no float in it left the model machinery
// holding NULL. NULL there already means "no solve has run", which is what
// makes it fatal; the guard gave it a second meaning, "this solve had no
// float in it", and nothing downstream could tell the two apart.
//
// So these tests pin both halves of the distinction:
//
//   * a float the query never mentioned is answered, on every route the
//     incremental driver has to a model, and answered with the same value
//     the batch driver gives; and
//   * with no solve at all there is still no model, and the question is
//     still refused rather than answered with an invented value.
//
// Found by a Murxla campaign cross-checking STP against STP under a differing
// option vector; reduced from a 143-line trace.

#include "stp/c_interface.h"
#include <gtest/gtest.h>

namespace
{

// binary16 (eb=5, sb=11): 1 sign bit + 5 exponent + 10 significand.
const int EB = 5;
const int SB = 11;

// 1.0 packs as 0 01111 0000000000.
const unsigned long long ONE_BITS = 0x3C00ULL;
const unsigned long long ONE_EXPONENT = 15; // 0b01111

// The float under test: a binary16 reinterpreted out of three bit-vectors,
// two of them symbols. Symbols on purpose -- a float built only from
// constants folds at construction and never reaches the encoding the bug was
// about. `sign` and `exponent` are handed back so a caller can pin them with
// bit-vector assertions, which is a real solve with no float anywhere in it.
Expr buildFloat(VC vc, Expr* sign, Expr* exponent)
{
  *sign = vc_varExpr(vc, "s", vc_bvType(vc, 1));
  *exponent = vc_varExpr(vc, "e", vc_bvType(vc, EB));
  Expr significand = vc_bvConstExprFromLL(vc, SB - 1, 0);
  return vc_fpToFPFromIEEEBV(
      vc, EB, SB,
      vc_bvConcatExpr(vc, *sign, vc_bvConcatExpr(vc, *exponent, significand)));
}

// Pin the carrier bits to 1.0 through the bit-vectors alone, so the float has
// exactly one value in the model and the test can name it. Nothing asserted
// here mentions a float.
void assertBitsAreOne(VC vc, Expr sign, Expr exponent)
{
  vc_assertFormula(vc, vc_eqExpr(vc, sign, vc_bvConstExprFromLL(vc, 1, 0)));
  vc_assertFormula(
      vc, vc_eqExpr(vc, exponent, vc_bvConstExprFromLL(vc, EB, ONE_EXPONENT)));
}

// vc_query of `false` asserts nothing and asks for a model of the stack as it
// stands; 0 is INVALID, i.e. satisfiable.
int solve(VC vc) { return vc_query(vc, vc_falseExpr(vc)); }

} // namespace

// The reduced reproducer, as filed: incremental from the first query, nothing
// on the stack at all, and a float built and never mentioned again. This is
// the deferred-model route -- without the 'c' flag the model is materialised
// on the first read rather than at solve time -- so it is the read itself
// that used to abort, one call after a query that answered.
TEST(fp_model_no_fp_in_query, incremental_empty_stack_answers)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);

  ASSERT_EQ(0, solve(vc));

  Expr value = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, value);
  // Nothing constrains the sign or the exponent, so their bits are the
  // solver's to choose and the packed value is not the test's to name. The
  // significand is a constant, and the model has to carry it through.
  EXPECT_EQ((unsigned long long)0,
            getBVUnsignedLongLong(value) & ((1ULL << (SB - 1)) - 1));

  vc_Destroy(vc);
}

// The second row of the defect's table: a real solve with a real assertion
// stack, none of it floating-point. Pinning the carrier bits makes the
// float's value the test's to name -- the answer is 1.0 and nothing else.
TEST(fp_model_no_fp_in_query, incremental_bitvector_only_stack_answers)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);
  assertBitsAreOne(vc, sign, exponent);

  ASSERT_EQ(0, solve(vc));

  Expr value = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, value);
  EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(value));

  vc_Destroy(vc);
}

// The same question with the model built at solve time rather than deferred
// to the read. The driver publishes the context on both routes, and a defect
// in either is invisible from the other.
TEST(fp_model_no_fp_in_query, incremental_eager_model_answers)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');
  vc_setFlag(vc, 'c'); // check the counterexample: build it during the solve

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);
  assertBitsAreOne(vc, sign, exponent);

  ASSERT_EQ(0, solve(vc));

  Expr value = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, value);
  EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(value));

  vc_Destroy(vc);
}

// Array equality ('x') puts the driver on the exact-stack route, which
// encodes the whole active stack as one block and publishes the context from
// its own places rather than the ordinary check-sat path's. The arrays are
// bit-vector arrays: still not one float in the query.
TEST(fp_model_no_fp_in_query, incremental_exact_stack_route_answers)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Type arr = vc_arrayType(vc, vc_bvType(vc, 4), vc_bvType(vc, 8));
  Expr a = vc_varExpr(vc, "a", arr);
  Expr i = vc_varExpr(vc, "i", vc_bvType(vc, 4));
  Expr v = vc_varExpr(vc, "v", vc_bvType(vc, 8));
  // Writing what is already there is the identity, so the equality is
  // satisfiable and extensionality has to reason about it rather than fold
  // it away.
  Expr stored = vc_writeExpr(vc, a, i, vc_readExpr(vc, a, i));
  vc_assertFormula(vc, vc_eqExpr(vc, stored, a));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i), v));

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);
  assertBitsAreOne(vc, sign, exponent);

  ASSERT_EQ(0, solve(vc));

  Expr value = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, value);
  EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(value));

  vc_Destroy(vc);
}

// The invariant behind all of the above, asked directly: the two drivers are
// answering one question about one model, so they answer it the same way.
// The value is pinned by bit-vector assertions precisely so that "the same"
// is a property of the question and not of which unconstrained bits each
// driver's solver happened to pick.
TEST(fp_model_no_fp_in_query, incremental_agrees_with_batch)
{
  unsigned long long answers[2];

  for (int incremental = 0; incremental < 2; incremental++)
  {
    VC vc = vc_createValidityChecker();
    if (incremental)
      vc_setFlag(vc, 'i');

    Expr sign, exponent;
    Expr f = buildFloat(vc, &sign, &exponent);
    assertBitsAreOne(vc, sign, exponent);

    ASSERT_EQ(0, solve(vc));

    Expr value = vc_getCounterExample(vc, f);
    ASSERT_NE((Expr)NULL, value);
    answers[incremental] = getBVUnsignedLongLong(value);

    vc_Destroy(vc);
  }

  EXPECT_EQ(answers[0], answers[1]);
  EXPECT_EQ(ONE_BITS, answers[1]);
}

// Repeated solves over one checker: the context is per encoding epoch and the
// batch driver may install its own between rounds, so publishing it once is
// not enough. Each answer has to be the one belonging to the solve that
// produced the model being read.
TEST(fp_model_no_fp_in_query, incremental_repeated_solves_keep_answering)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);
  assertBitsAreOne(vc, sign, exponent);

  for (int round = 0; round < 3; round++)
  {
    ASSERT_EQ(0, solve(vc)) << "round " << round;
    Expr value = vc_getCounterExample(vc, f);
    ASSERT_NE((Expr)NULL, value) << "round " << round;
    EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(value)) << "round " << round;
  }

  vc_Destroy(vc);
}

// Across a scope, which is where the driver does its level bookkeeping: a
// solve inside the pushed scope and another after it is gone. Everything
// asserted at either depth is a bit-vector, so neither solve has a float in
// it and neither may refuse the float's value.
TEST(fp_model_no_fp_in_query, incremental_answers_either_side_of_a_scope)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);
  assertBitsAreOne(vc, sign, exponent);

  vc_push(vc);
  Expr g = vc_varExpr(vc, "g", vc_bvType(vc, 8));
  vc_assertFormula(vc, vc_eqExpr(vc, g, vc_bvConstExprFromLL(vc, 8, 3)));

  ASSERT_EQ(0, solve(vc));
  Expr inScope = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, inScope);
  EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(inScope));

  vc_pop(vc);

  ASSERT_EQ(0, solve(vc));
  Expr afterPop = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, afterPop);
  EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(afterPop));

  vc_Destroy(vc);
}

// The other half of the distinction, and the reason the fix publishes a
// context per solve rather than conjuring one at read time: with no solve
// there is no model, and a model value asked for anyway must not be invented.
//
// The abort itself is a separate defect -- a model query with no solve behind
// it should be refused through the API, not by taking the process down, and
// it reaches this same message from the same NULL. This test does not bless
// it. It pins the part that matters here: whatever that refusal is later made
// to look like, it stays a refusal.
TEST(fp_model_no_fp_in_query, no_solve_is_still_not_answered)
{
  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        vc_setFlag(vc, 'i');
        Expr sign;
        Expr exponent;
        Expr f = buildFloat(vc, &sign, &exponent);
        (void)vc_getCounterExample(vc, f);
      },
      "no solve encoding context");
}
