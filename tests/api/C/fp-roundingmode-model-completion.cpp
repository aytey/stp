/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <gtest/gtest.h>
#include <stp/c_interface.h>

// Every RoundingMode value a model hands back names one of the five modes.
//
// The sort is carried in five bits, one-hot, so twenty-seven of the
// thirty-two patterns name nothing. A solve pins every mode its formula
// names -- the declaration does it, UF lowering does it, FpTotalise does it
// again at solve time -- but bits no constraint reached are free, and the
// backend leaves whatever it likes in them. Publishing those bits as the
// term's value took the process down: vc_getCounterExample lifts a
// RoundingMode carrier back to a mode, and a carrier that is not a mode has
// nothing to lift into.
//
//   Fatal Error: CreateRMConst requires one of the five rounding modes
//
// Two shapes reach free bits, and they are independent:
//
//   * a cell of a RoundingMode-element array that no selection reaches.
//     Read-over-write expansion introduces reads over the base array after
//     FpTotalise has run, and those are pinned only through the enclosing
//     read they stand in for -- which pins them exactly when the expansion
//     selects them.
//
//   * a rounding-mode symbol the last solve never named. Its pin belongs to
//     the assertion level it was declared at, and the incremental encoding
//     keeps its SAT variables alive after that level is popped.
//
// Both are don't-cares, and a don't-care RoundingMode has always been
// completed with RNE -- for the cell no observation covers, for the symbol
// simplified away. These are the same case and take the same answer.

namespace
{

// vc_query: 1 = VALID (the assertions are unsatisfiable), 0 = INVALID (they
// are satisfiable, so there is a model to read).
const int SAT = 0;

// The bits vc_getCounterExample hands back for a RoundingMode term are the
// VCRoundingMode encoding; see the note on vc_fpRoundingModeType.
unsigned long long modeBits(Expr value)
{
  EXPECT_TRUE(value != NULL);
  return value == NULL ? 0 : getBVUnsignedLongLong(value);
}

bool namesAMode(unsigned long long bits)
{
  return bits == VC_RM_RNE || bits == VC_RM_RTP || bits == VC_RM_RTN ||
         bits == VC_RM_RTZ || bits == VC_RM_RNA;
}

// The reported shape, without the flags it was reported with: a store whose
// index and the reading index are the same mode, so the expansion always
// takes the written value and never the read from `a`. `pin` decides whether
// the cell the test then reads back is left free or forced to a mode.
void selectNeverReachesTheCell(bool pin, unsigned long long& bits)
{
  VC vc = vc_createValidityChecker();

  Type rm = vc_fpRoundingModeType(vc);
  Type arr = vc_arrayType(vc, rm, rm);

  Expr a = vc_varExpr(vc, "a", arr);
  Expr j = vc_varExpr(vc, "j", rm);
  Expr v = vc_varExpr(vc, "v", rm);
  Expr k = vc_varExpr(vc, "k", rm);
  Expr rtn = vc_fpRoundingMode(vc, VC_RM_RTN);

  Expr cell = vc_readExpr(vc, a, rtn);

  vc_assertFormula(vc, vc_eqExpr(vc, j, rtn));
  vc_assertFormula(vc, vc_eqExpr(vc, k, rtn));
  vc_assertFormula(
      vc, vc_eqExpr(vc, vc_readExpr(vc, vc_writeExpr(vc, a, j, v), k), v));
  if (pin)
    vc_assertFormula(
        vc, vc_eqExpr(vc, cell, vc_fpRoundingMode(vc, VC_RM_RTZ)));

  ASSERT_EQ(SAT, vc_query(vc, vc_falseExpr(vc)));

  bits = modeBits(vc_getCounterExample(vc, cell));
  vc_Destroy(vc);
}

} // namespace

// The defect at STP's own defaults: no flags, no incremental driver, no
// abstraction. Before the fix this aborted on the read.
TEST(fp_roundingmode_model_completion, cell_no_selection_reaches)
{
  unsigned long long bits = 0;
  ASSERT_NO_FATAL_FAILURE(selectNeverReachesTheCell(/* pin */ false, bits));
  EXPECT_TRUE(namesAMode(bits)) << "carrier " << bits << " names no mode";
}

// The control, and it carries as much as the case above: completing a free
// carrier must not overwrite one the query decided. A fix that answered RNE
// for every RoundingMode read would pass the case and fail this.
TEST(fp_roundingmode_model_completion, a_decided_cell_keeps_its_mode)
{
  unsigned long long bits = 0;
  ASSERT_NO_FATAL_FAILURE(selectNeverReachesTheCell(/* pin */ true, bits));
  EXPECT_EQ((unsigned long long)VC_RM_RTZ, bits);
}

// The shape as reported, with the four interface flags and the incremental
// driver it was reported with. The bit-vector equality abstraction decides
// which cell the model gives the query's read, so the flags change which
// cell is free rather than whether one is -- but the reported reproducer
// belongs in the suite as it was reported.
TEST(fp_roundingmode_model_completion, cell_under_the_bv_equality_abstraction)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION, 1);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 1);
  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION_WIDTH, 1);
  vc_setInterfaceFlags(vc, BV_EQ_REFINE_WIDTH, 1);

  Type rm = vc_fpRoundingModeType(vc);
  Type arr = vc_arrayType(vc, rm, rm);

  Expr x = vc_varExpr(vc, "x", rm);
  Expr a = vc_varExpr(vc, "a", arr);

  Expr cell = vc_readExpr(vc, a, vc_fpRoundingMode(vc, VC_RM_RTP));
  Expr store = vc_writeExpr(vc, a, x, cell);
  Expr i = vc_readExpr(vc, store, vc_fpRoundingMode(vc, VC_RM_RNE));
  Expr deep = vc_readExpr(vc, store, i);

  // STP has no assumption interface; a scope that stays pushed over the
  // model read is how the reproducer's driver emulated one.
  vc_push(vc);
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, deep, x)));

  ASSERT_EQ(SAT, vc_query(vc, vc_falseExpr(vc)));

  EXPECT_TRUE(namesAMode(modeBits(vc_getCounterExample(vc, cell))));
  vc_Destroy(vc);
}

// A rounding mode declared inside a scope, used by one solve, and read back
// after a later solve that never named it. The pin vc_varExpr asserts went
// with the popped level; the symbol's SAT variables did not, and the last
// solve left them free.
TEST(fp_roundingmode_model_completion, symbol_the_last_solve_never_named)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Type rm = vc_fpRoundingModeType(vc);
  Type fp = vc_fpType(vc, 11, 53);
  Expr rtn = vc_fpRoundingMode(vc, VC_RM_RTN);

  vc_push(vc);

  Expr chooser = vc_varExpr(vc, "c", vc_boolType(vc));
  Expr r = vc_varExpr(vc, "r", rm);
  Expr mode = vc_iteExpr(vc, chooser, rtn, r);

  Expr moo = vc_fpMinusInfinity(vc, fp);
  Expr rti = vc_fpRoundToIntegralExpr(vc, r, moo);
  Expr sub = vc_fpSubExpr(vc, mode, rti, rti);

  // The solve that names the mode, and the only one that does.
  vc_assertFormula(vc, vc_fpGtExpr(vc, rti, sub));
  vc_query(vc, vc_falseExpr(vc));

  // The model the read lands on: the level that named the mode -- and that
  // pinned it -- is gone.
  vc_pop(vc);
  ASSERT_EQ(SAT, vc_query(vc, vc_falseExpr(vc)));

  EXPECT_TRUE(namesAMode(modeBits(vc_getCounterExample(vc, mode))));
  EXPECT_TRUE(namesAMode(modeBits(vc_getCounterExample(vc, r))));
  vc_Destroy(vc);
}

// The same solve sequence with the mode decided by the surviving level: what
// the model answers is that mode, not the completion.
TEST(fp_roundingmode_model_completion, a_decided_symbol_keeps_its_mode)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Type rm = vc_fpRoundingModeType(vc);
  Expr r = vc_varExpr(vc, "r", rm);
  vc_assertFormula(vc, vc_eqExpr(vc, r, vc_fpRoundingMode(vc, VC_RM_RNA)));

  vc_push(vc);
  ASSERT_EQ(SAT, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  ASSERT_EQ(SAT, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)VC_RM_RNA,
            modeBits(vc_getCounterExample(vc, r)));
  vc_Destroy(vc);
}
