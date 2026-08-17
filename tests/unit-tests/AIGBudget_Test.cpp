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

#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/STPManager/STPManager.h"
#include <gtest/gtest.h>

using namespace stp;

namespace
{

class AIGBudgetTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  BBNodeManagerAIG aig;
  unsigned counter = 0;

  BBNodeAIG input()
  {
    const ASTNode s =
        mgr.CreateSymbol(("v" + std::to_string(counter++)).c_str(), 0, 1);
    return aig.CreateSymbol(s, 0);
  }
};

TEST_F(AIGBudgetTest, NoBudgetNeverThrows)
{
  aig.nodeBudget = 0;
  for (int i = 0; i < 100; i++)
  {
    BBNodeAIG a = input(), b = input();
    std::vector<BBNodeAIG> children{a, b};
    aig.CreateNode(AND, children);
  }
}

TEST_F(AIGBudgetTest, BudgetExhaustedThrows)
{
  aig.nodeBudget = 5;
  bool threw = false;
  try
  {
    for (int i = 0; i < 1000; i++)
    {
      BBNodeAIG a = input(), b = input();
      std::vector<BBNodeAIG> children{a, b};
      aig.CreateNode(AND, children);
    }
  }
  catch (const AIGBudgetExhausted&)
  {
    threw = true;
  }
  EXPECT_TRUE(threw);
}

TEST_F(AIGBudgetTest, ExhaustedNodeCountIsAboveBudget)
{
  aig.nodeBudget = 3;
  try
  {
    for (int i = 0; i < 1000; i++)
    {
      BBNodeAIG a = input(), b = input();
      std::vector<BBNodeAIG> children{a, b};
      aig.CreateNode(AND, children);
    }
    FAIL() << "should have thrown";
  }
  catch (const AIGBudgetExhausted& e)
  {
    EXPECT_GT(e.nodeCount, 0);
    EXPECT_GE(static_cast<unsigned>(e.nodeCount), aig.nodeBudget);
  }
}

} // namespace
