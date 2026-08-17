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

#include <gtest/gtest.h>

using namespace stp;

namespace
{

class BVEQCCTest : public ::testing::Test
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

TEST_F(BVEQCCTest, TransitivityConflictDetected)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode a = makeSymbol("cc_a", 256);
  ASTNode b = makeSymbol("cc_b", 256);
  ASTNode c = makeSymbol("cc_c", 256);

  ASTNode eq_ab = factory->CreateNode(EQ, a, b);
  ASTNode eq_bc = factory->CreateNode(EQ, b, c);
  ASTNode neq_ac = factory->CreateNode(NOT, factory->CreateNode(EQ, a, c));

  // (= a b) & (= b c) & !(= a c) is UNSAT by transitivity
  ASTNode formula = factory->CreateNode(AND, eq_ab,
      factory->CreateNode(AND, eq_bc, neq_ac));

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

TEST_F(BVEQCCTest, ConsistentModelNoConflict)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode a = makeSymbol("cc2_a", 256);
  ASTNode b = makeSymbol("cc2_b", 256);
  ASTNode c = makeSymbol("cc2_c", 256);

  ASTNode eq_ab = factory->CreateNode(EQ, a, b);
  ASTNode eq_bc = factory->CreateNode(EQ, b, c);

  // (= a b) & (= b c) is SAT
  ASTNode formula = factory->CreateNode(AND, eq_ab, eq_bc);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQCCTest, LongerTransitivityChain)
{
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode a = makeSymbol("ch_a", 256);
  ASTNode b = makeSymbol("ch_b", 256);
  ASTNode c = makeSymbol("ch_c", 256);
  ASTNode d = makeSymbol("ch_d", 256);

  ASTNode eq_ab = factory->CreateNode(EQ, a, b);
  ASTNode eq_bc = factory->CreateNode(EQ, b, c);
  ASTNode eq_cd = factory->CreateNode(EQ, c, d);
  ASTNode neq_ad = factory->CreateNode(NOT, factory->CreateNode(EQ, a, d));

  // a=b & b=c & c=d & !(a=d) is UNSAT by transitivity chain
  ASTNode formula = factory->CreateNode(AND,
      factory->CreateNode(AND, eq_ab, eq_bc),
      factory->CreateNode(AND, eq_cd, neq_ad));

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

TEST_F(BVEQCCTest, ManySymbolsInEquivalenceClasses)
{
  // 12 symbols in 3 equivalence classes of 4.
  // All within-class equalities hold; no cross-class equalities.
  // CC should find no conflicts and the formula should be SAT.
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  const unsigned numClasses = 3;
  const unsigned classSize = 4;
  std::vector<std::vector<ASTNode>> classes(numClasses);

  for (unsigned c = 0; c < numClasses; ++c)
    for (unsigned i = 0; i < classSize; ++i)
    {
      std::string name = "mc_" + std::to_string(c) + "_" + std::to_string(i);
      classes[c].push_back(makeSymbol(name.c_str(), 256));
    }

  // Chain equalities within each class: s0=s1, s1=s2, s2=s3
  ASTVec conjuncts;
  for (unsigned c = 0; c < numClasses; ++c)
    for (unsigned i = 0; i + 1 < classSize; ++i)
      conjuncts.push_back(
          factory->CreateNode(EQ, classes[c][i], classes[c][i + 1]));

  ASTNode formula = conjuncts[0];
  for (unsigned i = 1; i < conjuncts.size(); ++i)
    formula = factory->CreateNode(AND, formula, conjuncts[i]);

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_INVALID, result);
}

TEST_F(BVEQCCTest, CrossClassDisequalityWithTransitivityConflict)
{
  // 3 classes: {a,b}, {c,d}, with a=b, c=d, b=c, but ¬(a=d).
  // b=c merges the two classes, so a=d by transitivity → UNSAT.
  mgr.UserFlags.bv_eq_abstraction = true;
  mgr.UserFlags.bv_eq_abstraction_width = 64;

  ASTNode a = makeSymbol("xc_a", 256);
  ASTNode b = makeSymbol("xc_b", 256);
  ASTNode c = makeSymbol("xc_c", 256);
  ASTNode d = makeSymbol("xc_d", 256);

  ASTNode formula = factory->CreateNode(AND,
      factory->CreateNode(AND,
          factory->CreateNode(EQ, a, b),
          factory->CreateNode(EQ, c, d)),
      factory->CreateNode(AND,
          factory->CreateNode(EQ, b, c),
          factory->CreateNode(NOT, factory->CreateNode(EQ, a, d))));

  STP stp(&mgr);
  SOLVER_RETURN_TYPE result = stp.TopLevelSTP(formula, mgr.ASTFalse);
  EXPECT_EQ(SOLVER_VALID, result);
}

} // namespace
