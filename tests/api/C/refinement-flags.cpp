// The refinement encodings a C API client can now reach.
//
// --uf-narrow-results, --uf-inject-args, --bv-eq-abstraction,
// --bv-eq-abstraction-width, --bv-eq-refine-width and --bv-term-abstraction
// were reachable only by a query read from a file: a client driving STP
// through vc_* had no way to turn any of them on or off, and got whatever the
// defaults were. Each now has an ifaceflag_t that writes the same UserFlags
// field the CLI parser writes.
//
// The VC handle IS the stp::STP object, so reading the flags back off it is
// an honest probe for "did this reach the field the solver consults?" -- the
// abstractions are otherwise invisible from outside, being encodings that by
// construction do not change what is answered.
#include "stp/STPManager/STP.h"
#include "stp/c_interface.h"
#include <gtest/gtest.h>

namespace
{
const stp::UserDefinedFlags& flags(VC vc)
{
  return ((stp::STP*)vc)->bm->UserFlags;
}

int errors = 0;
void countError(const char*)
{
  ++errors;
}
} // namespace

// The defaults a client inherits by not setting anything, which are the same
// ones the CLI captures into its --help text.
TEST(refinement_flags, DefaultsAreTheOnesTheCommandLineDocuments)
{
  VC vc = vc_createValidityChecker();
  EXPECT_TRUE(flags(vc).uf_narrow_results);
  EXPECT_FALSE(flags(vc).uf_inject_args);
  EXPECT_FALSE(flags(vc).bv_eq_abstraction);
  EXPECT_FALSE(flags(vc).bv_term_abstraction);
  EXPECT_EQ(64u, flags(vc).bv_eq_abstraction_width);
  EXPECT_EQ(0u, flags(vc).bv_eq_refine_width);
  vc_Destroy(vc);
}

// Each flag reaches its field, in both directions for the Boolean ones: a
// case that fell through to the default arm would abort rather than fail, so
// this pins the mapping and not merely that the enumerator is accepted.
TEST(refinement_flags, EachFlagReachesTheFieldTheCLIWrites)
{
  VC vc = vc_createValidityChecker();

  vc_setInterfaceFlags(vc, UF_NARROW_RESULTS, 0);
  EXPECT_FALSE(flags(vc).uf_narrow_results);
  vc_setInterfaceFlags(vc, UF_NARROW_RESULTS, 1);
  EXPECT_TRUE(flags(vc).uf_narrow_results);

  vc_setInterfaceFlags(vc, UF_EQUALITY_INJECTIVITY, 1);
  EXPECT_TRUE(flags(vc).uf_inject_args);
  vc_setInterfaceFlags(vc, UF_EQUALITY_INJECTIVITY, 0);
  EXPECT_FALSE(flags(vc).uf_inject_args);

  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION, 1);
  EXPECT_TRUE(flags(vc).bv_eq_abstraction);
  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION, 0);
  EXPECT_FALSE(flags(vc).bv_eq_abstraction);

  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 1);
  EXPECT_TRUE(flags(vc).bv_term_abstraction);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 0);
  EXPECT_FALSE(flags(vc).bv_term_abstraction);

  // Any nonzero enables, as everywhere else in this call.
  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION, 2);
  EXPECT_TRUE(flags(vc).bv_eq_abstraction);

  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION_WIDTH, 1);
  EXPECT_EQ(1u, flags(vc).bv_eq_abstraction_width);
  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION_WIDTH, 0);
  EXPECT_EQ(0u, flags(vc).bv_eq_abstraction_width);

  vc_setInterfaceFlags(vc, BV_EQ_REFINE_WIDTH, 8);
  EXPECT_EQ(8u, flags(vc).bv_eq_refine_width);

  vc_Destroy(vc);
}

// A negative width would wrap to a threshold no term can reach, silently
// disabling the abstraction the caller was asking for. It is refused with a
// diagnostic and the width it would have wrecked is left as it was.
TEST(refinement_flags, ANegativeWidthIsRefusedAndLeavesTheWidthAlone)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION_WIDTH, 32);
  vc_setInterfaceFlags(vc, BV_EQ_REFINE_WIDTH, 4);

  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION_WIDTH, -1);
  EXPECT_EQ(32u, flags(vc).bv_eq_abstraction_width);
  vc_setInterfaceFlags(vc, BV_EQ_REFINE_WIDTH, -64);
  EXPECT_EQ(4u, flags(vc).bv_eq_refine_width);
  EXPECT_EQ(2, errors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// There is deliberately no end-to-end leg for BV_EQ_ABSTRACTION or
// BV_TERM_ABSTRACTION here, only the plumbing above.
//
// Reaching the encoding needs a query that survives word-level simplification
// with wide terms intact, and every such query this could be built from
// aborts once the abstraction engages and a counterexample is constructed:
//
//   Assertion `symbol.GetKind() == SYMBOL' failed.
//   AbsRefine_CounterExample::ConstructCounterExample
//
// which reproduces on uf-cegar-abstraction's own binary and is nothing to do
// with reaching the flag from here. A leg written around it would either
// abort or, by choosing a query the simplifier finishes first, pass without
// the encoding ever running -- and a vacuous test that reads as an
// end-to-end one is worse than an absent one. UF narrowing below does engage
// (8 bits to 2 for three applications) and is checked end to end.

// Narrowing is invisible from out here: it re-sorts the introduced result
// symbol the solver reasons about, and the model still reads back at the
// sort the declaration was made at.
TEST(refinement_flags, NarrowingChangesNeitherTheAnswerNorTheSortReadBack)
{
  for (int narrow = 0; narrow < 2; narrow++)
  {
    VC vc = vc_createValidityChecker();
    vc_setFlag(vc, 'u');
    vc_setInterfaceFlags(vc, UF_NARROW_RESULTS, narrow);
    ASSERT_EQ(narrow != 0, flags(vc).uf_narrow_results);

    Type bv8 = vc_bvType(vc, 8);
    Type domain[] = {bv8};
    const UFDeclHandle f =
        vc_declareUninterpretedFunction(vc, "f", domain, 1, bv8);
    ASSERT_NE(0u, f);

    Expr a = vc_varExpr(vc, "a", vc_bvType(vc, 8));
    Expr b = vc_varExpr(vc, "b", vc_bvType(vc, 8));
    Expr c = vc_varExpr(vc, "c", vc_bvType(vc, 8));
    const Expr aArg[] = {a};
    const Expr bArg[] = {b};
    const Expr cArg[] = {c};
    Expr fa = vc_applyUninterpretedFunction(vc, f, aArg, 1);
    Expr fb = vc_applyUninterpretedFunction(vc, f, bArg, 1);
    Expr fc = vc_applyUninterpretedFunction(vc, f, cArg, 1);
    ASSERT_NE(nullptr, fa);
    ASSERT_NE(nullptr, fb);
    ASSERT_NE(nullptr, fc);

    // Three results that must differ: two bits are enough to tell them apart,
    // where the declaration asked for eight.
    vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, fa, fb)));
    vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, fb, fc)));
    vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, fa, fc)));

    EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

    // Whatever width the solver used, the declared one is what comes back.
    Expr value = vc_getUninterpretedFunctionValue(vc, fa);
    ASSERT_NE(nullptr, value);
    EXPECT_EQ(8, vc_getBVLength(vc, value));
    Expr other = vc_getUninterpretedFunctionValue(vc, fb);
    ASSERT_NE(nullptr, other);
    EXPECT_EQ(8, vc_getBVLength(vc, other));
    EXPECT_NE(getBVUnsigned(value), getBVUnsigned(other));

    vc_DeleteExpr(other);
    vc_DeleteExpr(value);
    vc_Destroy(vc);
  }
}
