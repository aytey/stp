// The options this branch added that a C API client can now reach.
//
// Every one of them was reachable only by a query read from a file: a client
// driving STP through vc_* had no way to turn any of them on or off, and got
// whatever the defaults were. Each now has an ifaceflag_t that writes the same
// UserFlags field the CLI parser writes -- the two refinement profiles
// (--uf-narrow-results, --uf-inject-args), the eager congruence encoding
// (--uf-ackermann, --uf-ackermann-budget, --uf-lemmas-per-round,
// --uf-phase-hints), the declared-sort carrier (--uf-sort-width), the BV
// abstractions and what bounds them (--bv-eq-abstraction,
// --bv-eq-abstraction-width, --bv-eq-refine-width, --bv-term-abstraction,
// --bv-term-abstraction-mult, --bv-term-abstraction-rounds), the distinct
// rewrite (--distinct-ordering) and the bit-blasting limit
// (--aig-node-budget). --uninterpreted-functions itself already had a route,
// through vc_setFlag(vc, 'u').
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
  EXPECT_TRUE(flags(vc).bv_term_abstraction_mult);
  EXPECT_EQ(32u, flags(vc).bv_term_abstraction_rounds);
  EXPECT_EQ(8u, flags(vc).uf_lemmas_per_round);
  EXPECT_EQ(stp::UserDefinedFlags::UFEagerMode::AUTO, flags(vc).uf_eager_mode);
  EXPECT_EQ(256u, flags(vc).uf_eager_budget);
  EXPECT_FALSE(flags(vc).uf_phase_hints);
  EXPECT_EQ(16u, flags(vc).uf_sort_width);
  EXPECT_TRUE(flags(vc).distinct_ordering);
  EXPECT_EQ(0u, flags(vc).aig_node_budget);
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

  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_MULT, 0);
  EXPECT_FALSE(flags(vc).bv_term_abstraction_mult);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_MULT, 1);
  EXPECT_TRUE(flags(vc).bv_term_abstraction_mult);

  vc_setInterfaceFlags(vc, UF_PHASE_HINTS, 1);
  EXPECT_TRUE(flags(vc).uf_phase_hints);
  vc_setInterfaceFlags(vc, UF_PHASE_HINTS, 0);
  EXPECT_FALSE(flags(vc).uf_phase_hints);

  vc_setInterfaceFlags(vc, DISTINCT_ORDERING, 0);
  EXPECT_FALSE(flags(vc).distinct_ordering);
  vc_setInterfaceFlags(vc, DISTINCT_ORDERING, 1);
  EXPECT_TRUE(flags(vc).distinct_ordering);

  // Zero is a meaning of its own for each of these three, not an absence:
  // never escalate, install every conflict, no AIG limit.
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, 0);
  EXPECT_EQ(0u, flags(vc).bv_term_abstraction_rounds);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, 4);
  EXPECT_EQ(4u, flags(vc).bv_term_abstraction_rounds);
  vc_setInterfaceFlags(vc, UF_LEMMAS_PER_ROUND, 0);
  EXPECT_EQ(0u, flags(vc).uf_lemmas_per_round);
  vc_setInterfaceFlags(vc, UF_LEMMAS_PER_ROUND, 1);
  EXPECT_EQ(1u, flags(vc).uf_lemmas_per_round);
  vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, 5000);
  EXPECT_EQ(5000u, flags(vc).aig_node_budget);
  vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, 0);
  EXPECT_EQ(0u, flags(vc).aig_node_budget);

  vc_setInterfaceFlags(vc, UF_ACKERMANN_BUDGET, 12);
  EXPECT_EQ(12u, flags(vc).uf_eager_budget);
  vc_setInterfaceFlags(vc, UF_SORT_WIDTH, 5);
  EXPECT_EQ(5u, flags(vc).uf_sort_width);

  // The three modes, by ordinal, in the order --uf-ackermann names them.
  typedef stp::UserDefinedFlags::UFEagerMode Mode;
  vc_setInterfaceFlags(vc, UF_ACKERMANN, 1);
  EXPECT_EQ(Mode::ON, flags(vc).uf_eager_mode);
  vc_setInterfaceFlags(vc, UF_ACKERMANN, 2);
  EXPECT_EQ(Mode::OFF, flags(vc).uf_eager_mode);
  vc_setInterfaceFlags(vc, UF_ACKERMANN, 0);
  EXPECT_EQ(Mode::AUTO, flags(vc).uf_eager_mode);

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

  // Every other field an int reaches that is unsigned underneath, refused the
  // same way and left holding what it had.
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, -1);
  EXPECT_EQ(32u, flags(vc).bv_term_abstraction_rounds);
  vc_setInterfaceFlags(vc, UF_LEMMAS_PER_ROUND, -1);
  EXPECT_EQ(8u, flags(vc).uf_lemmas_per_round);
  vc_setInterfaceFlags(vc, UF_ACKERMANN_BUDGET, -1);
  EXPECT_EQ(256u, flags(vc).uf_eager_budget);
  vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, -1);
  EXPECT_EQ(0u, flags(vc).aig_node_budget);
  EXPECT_EQ(6, errors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// The declared-sort width is bounded at both ends, not merely at zero: a
// zero-width element is read as a Boolean by the legacy width checks, and a
// width past the ceiling overflows the word arithmetic underneath. Both are
// refused and leave the width as it was, so a client cannot reach either.
TEST(refinement_flags, TheSortWidthIsRefusedOutsideTheRangeTheCLITakes)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC vc = vc_createValidityChecker();
  const int outside[] = {-1, 0, 1025, 100000};
  for (const int bad : outside)
  {
    vc_setInterfaceFlags(vc, UF_SORT_WIDTH, bad);
    EXPECT_EQ(16u, flags(vc).uf_sort_width) << "width " << bad;
  }
  EXPECT_EQ(4, errors);

  // and the two ends that are inside it
  vc_setInterfaceFlags(vc, UF_SORT_WIDTH, 1);
  EXPECT_EQ(1u, flags(vc).uf_sort_width);
  vc_setInterfaceFlags(vc, UF_SORT_WIDTH, 1024);
  EXPECT_EQ(1024u, flags(vc).uf_sort_width);
  EXPECT_EQ(4, errors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// UF_ACKERMANN names one of three modes. A value outside them names none, so
// it is refused rather than stored: the field is an enumeration, and the
// lowering tests it arm by arm.
TEST(refinement_flags, AnUnknownAckermannModeIsRefused)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC vc = vc_createValidityChecker();
  typedef stp::UserDefinedFlags::UFEagerMode Mode;
  vc_setInterfaceFlags(vc, UF_ACKERMANN, 1);
  ASSERT_EQ(Mode::ON, flags(vc).uf_eager_mode);
  const int outside[] = {-1, 3, 99};
  for (const int bad : outside)
  {
    vc_setInterfaceFlags(vc, UF_ACKERMANN, bad);
    EXPECT_EQ(Mode::ON, flags(vc).uf_eager_mode) << "mode " << bad;
  }
  EXPECT_EQ(3, errors);

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

// The AIG budget is the one option here that can change what a query answers,
// so what it answers is worth pinning. Exceeding it ends the query with 3 --
// the same value a clock expiry gives, the two being told apart by the reason
// recorded for the unknown rather than by the verdict, and this interface
// exposing no route to that reason. Without the budget the same query is
// decided, which is what says the 3 came from the budget and not from the
// query being hard.
TEST(refinement_flags, TheAigBudgetEndsAQueryWithoutAnAnswer)
{
  for (int budget = 0; budget <= 50; budget += 50)
  {
    VC vc = vc_createValidityChecker();
    vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, budget);
    Type bv = vc_bvType(vc, 32);
    Expr x = vc_varExpr(vc, "x", bv);
    Expr y = vc_varExpr(vc, "y", bv);
    vc_assertFormula(
        vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 32, x, y),
                      vc_bvConstExprFromInt(vc, 32, 0xffff)));
    vc_assertFormula(
        vc, vc_bvGtExpr(vc, x, vc_bvConstExprFromInt(vc, 32, 1)));
    const int answer = vc_query(vc, vc_falseExpr(vc));
    if (budget == 0)
      EXPECT_EQ(0, answer) << "no limit, so the query is decided";
    else
      EXPECT_EQ(3, answer) << "budget " << budget;
    vc_Destroy(vc);
  }
}

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
