/***********
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

#include "stp/STPManager/STPManager.h"
#include "stp/STPManager/STP.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BitBlaster.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

class BVEQAbstractionTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  NodeFactory* factory;

  void SetUp() override { factory = mgr.defaultNodeFactory; }

  ASTNode makeSymbol(const char* name, unsigned width)
  {
    return mgr.CreateSymbol(name, 0, width);
  }
};

TEST_F(BVEQAbstractionTest, AbstractsWideSymbolEquality)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode x = makeSymbol("x", 256);
  ASTNode y = makeSymbol("y", 256);
  ASTNode eq = factory->CreateNode(EQ, x, y);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(eq);

  EXPECT_EQ(1u, bb.abstractedEQs().size());
  EXPECT_EQ(eq, bb.abstractedEQs()[0].eqNode);
  EXPECT_EQ(x, bb.abstractedEQs()[0].leftSymbol);
  EXPECT_EQ(y, bb.abstractedEQs()[0].rightSymbol);
}

TEST_F(BVEQAbstractionTest, NoAbstractionWhenDisabled)
{
  mgr.UserFlags.bv_eq_abstraction = false;

  ASTNode x = makeSymbol("x2", 256);
  ASTNode y = makeSymbol("y2", 256);
  ASTNode eq = factory->CreateNode(EQ, x, y);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(eq);

  EXPECT_TRUE(bb.abstractedEQs().empty());
}

TEST_F(BVEQAbstractionTest, NoAbstractionBelowWidthThreshold)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode x = makeSymbol("x3", 32);
  ASTNode y = makeSymbol("y3", 32);
  ASTNode eq = factory->CreateNode(EQ, x, y);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(eq);

  EXPECT_TRUE(bb.abstractedEQs().empty());
}

TEST_F(BVEQAbstractionTest, NoAbstractionForNonSymbolOperands)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode x = makeSymbol("x4", 256);
  ASTNode one = mgr.CreateBVConst(256, 1);
  ASTNode sum = factory->CreateTerm(BVPLUS, 256, x, one);
  ASTNode y = makeSymbol("y4", 256);
  ASTNode eq = factory->CreateNode(EQ, sum, y);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(eq);

  EXPECT_TRUE(bb.abstractedEQs().empty());
}

TEST_F(BVEQAbstractionTest, BooleanSkeletonContradictionIsUnsatWithoutRefinement)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode x = makeSymbol("x5", 256);
  ASTNode y = makeSymbol("y5", 256);
  ASTNode eq = factory->CreateNode(EQ, x, y);
  ASTNode neq = factory->CreateNode(NOT, eq);
  ASTNode conj = factory->CreateNode(AND, eq, neq);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  BBNodeAIG result = bb.BBForm(conj);

  EXPECT_EQ(1u, bb.abstractedEQs().size());
  EXPECT_EQ(aigMgr.getFalse(), result);
}

TEST_F(BVEQAbstractionTest, MultipleEqualitiesAbstracted)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode a = makeSymbol("a", 256);
  ASTNode b = makeSymbol("b", 256);
  ASTNode c = makeSymbol("c", 256);
  ASTNode eq1 = factory->CreateNode(EQ, a, b);
  ASTNode eq2 = factory->CreateNode(EQ, b, c);
  ASTNode conj = factory->CreateNode(AND, eq1, eq2);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(conj);

  EXPECT_EQ(2u, bb.abstractedEQs().size());
}

TEST_F(BVEQAbstractionTest, DagSharingReusesAbstraction)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode x = makeSymbol("x6", 256);
  ASTNode y = makeSymbol("y6", 256);
  ASTNode eq = factory->CreateNode(EQ, x, y);
  ASTNode conj = factory->CreateNode(AND, eq, eq);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(conj);

  EXPECT_EQ(1u, bb.abstractedEQs().size());
}

TEST_F(BVEQAbstractionTest, PrefixRefinementSatResult)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;
  mgr.UserFlags.bv_eq_refine_width = 32;

  ASTNode a = makeSymbol("pr_a", 256);
  ASTNode b = makeSymbol("pr_b", 256);
  ASTNode eq = factory->CreateNode(EQ, a, b);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(eq, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQAbstractionTest, PrefixRefinementUnsatTransitivity)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;
  mgr.UserFlags.bv_eq_refine_width = 32;

  ASTNode a = makeSymbol("pru_a", 256);
  ASTNode b = makeSymbol("pru_b", 256);
  ASTNode c = makeSymbol("pru_c", 256);

  ASTNode eq_ab = factory->CreateNode(EQ, a, b);
  ASTNode eq_bc = factory->CreateNode(EQ, b, c);
  ASTNode neq_ac = factory->CreateNode(NOT, factory->CreateNode(EQ, a, c));

  ASTNode formula = factory->CreateNode(AND, eq_ab,
      factory->CreateNode(AND, eq_bc, neq_ac));

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

TEST_F(BVEQAbstractionTest, PrefixRefinementSmallWidth)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;
  mgr.UserFlags.bv_eq_refine_width = 8;

  ASTNode a = makeSymbol("psm_a", 256);
  ASTNode b = makeSymbol("psm_b", 256);

  ASTNode eq = factory->CreateNode(EQ, a, b);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(eq, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQAbstractionTest, BVPLUSAbstractionCreatesAbstraction)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode x = makeSymbol("ta_x", 256);
  ASTNode y = makeSymbol("ta_y", 256);
  ASTNode sum = factory->CreateTerm(BVPLUS, 256, x, y);
  ASTNode z = makeSymbol("ta_z", 256);
  ASTNode eq = factory->CreateNode(EQ, sum, z);

  BBNodeManagerAIG aigMgr;
  stp::SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  BitBlaster bb(&aigMgr, &simp, factory, &mgr.UserFlags);

  bb.BBForm(eq);

  EXPECT_GE(bb.abstractedTerms().size(), 1u);
  EXPECT_EQ(BVPLUS, bb.abstractedTerms()[0].opKind);
}

TEST_F(BVEQAbstractionTest, BVPLUSAbstractionSatResult)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode x = makeSymbol("tas_x", 256);
  ASTNode y = makeSymbol("tas_y", 256);
  ASTNode sum = factory->CreateTerm(BVPLUS, 256, x, y);
  ASTNode z = makeSymbol("tas_z", 256);
  ASTNode eq = factory->CreateNode(EQ, sum, z);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(eq, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQAbstractionTest, BVPLUSAbstractionUnsatResult)
{
  mgr.UserFlags.bv_term_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode x = makeSymbol("tau_x", 256);
  ASTNode y = makeSymbol("tau_y", 256);
  ASTNode z = makeSymbol("tau_z", 256);
  ASTNode sum = factory->CreateTerm(BVPLUS, 256, x, y);
  ASTNode eqSumZ = factory->CreateNode(EQ, sum, z);
  ASTNode eqXZ = factory->CreateNode(EQ, x, z);
  ASTNode yNeq0 = factory->CreateNode(NOT,
      factory->CreateNode(EQ, y, mgr.CreateBVConst(256, 0)));
  ASTNode formula = factory->CreateNode(AND,
      factory->CreateNode(AND, eqSumZ, eqXZ), yNeq0);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

} // namespace
