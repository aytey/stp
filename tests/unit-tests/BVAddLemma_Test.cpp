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

// Exhaustive checks for the complete addition abstraction registry. Addition
// abstraction is opt-in, just as in Bitwuzla; these tests establish soundness
// independently of whether the experiment improves a workload.
#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/ToSat/BVExactEncoder.h"

#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <gtest/gtest.h>

#include <memory>
#include <vector>

using namespace stp;

namespace
{

const unsigned WIDTH = 4;
const unsigned VALUES = 1u << WIDTH;

std::vector<bool> bitsOf(unsigned value, unsigned width = WIDTH)
{
  std::vector<bool> bits(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

unsigned referenceAdd(unsigned x, unsigned s)
{
  return (x + s) & (VALUES - 1);
}

class BVAddLemmaTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  std::unique_ptr<SATSolver> solver;
  std::vector<unsigned> xVars, sVars, tVars;

  void buildCircuit(AddLemma lemma)
  {
    solver.reset(createSATSolver(mgr.UserFlags));
    ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
    ASSERT_TRUE(solver->supportsAssumptions());

    xVars.resize(WIDTH);
    sVars.resize(WIDTH);
    tVars.resize(WIDTH);
    for (unsigned i = 0; i < WIDTH; ++i)
    {
      xVars[i] = solver->newVar();
      sVars[i] = solver->newVar();
      tVars[i] = solver->newVar();
      solver->setFrozen(xVars[i]);
      solver->setFrozen(sVars[i]);
      solver->setFrozen(tVars[i]);
    }

    BVExactEncoder(&mgr).encodeAddLemma(*solver, lemma, WIDTH, xVars, sVars,
                                        tVars);
  }

  bool circuitPermits(unsigned x, unsigned s, unsigned t)
  {
    SATSolver::vec_literals assumptions;
    const unsigned vals[3] = {x, s, t};
    const std::vector<unsigned>* vars[3] = {&xVars, &sVars, &tVars};
    for (unsigned v = 0; v < 3; ++v)
      for (unsigned i = 0; i < WIDTH; ++i)
        assumptions.push(
            SATSolver::mkLit((*vars[v])[i], ((vals[v] >> i) & 1u) == 0));

    bool timedOut = false;
    const bool sat = solver->solveWithAssumptions(assumptions, timedOut);
    EXPECT_FALSE(timedOut);
    return sat;
  }
};

} // namespace

TEST(BVAddLemma, every_lemma_is_true_of_addition)
{
  unsigned count = 0;
  const AddLemma* lemmas = addLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
    for (unsigned x = 0; x < VALUES; ++x)
      for (unsigned s = 0; s < VALUES; ++s)
      {
        const unsigned t = referenceAdd(x, s);
        ASSERT_TRUE(addLemmaHolds(lemmas[i], bitsOf(x), bitsOf(s), bitsOf(t)))
            << addLemmaName(lemmas[i]) << " is false of x=" << x << " s=" << s
            << " (sum " << t << ")";
      }
}

TEST(BVAddLemma, every_lemma_is_true_at_each_small_width)
{
  unsigned count = 0;
  const AddLemma* lemmas = addLemmaTable(count);
  for (unsigned width = 1; width <= 6; ++width)
  {
    const unsigned values = 1u << width;
    const unsigned mask = values - 1;
    for (unsigned i = 0; i < count; ++i)
    {
      if (!addLemmaApplicable(lemmas[i], width))
        continue;
      for (unsigned x = 0; x < values; ++x)
        for (unsigned s = 0; s < values; ++s)
        {
          const unsigned t = (x + s) & mask;
          ASSERT_TRUE(addLemmaHolds(lemmas[i], bitsOf(x, width),
                                    bitsOf(s, width), bitsOf(t, width)))
              << addLemmaName(lemmas[i]) << " is false at width " << width
              << " for x=" << x << " s=" << s << " (sum " << t << ")";
        }
    }
  }
}

TEST(BVAddLemma, every_lemma_rules_something_out)
{
  unsigned count = 0;
  const AddLemma* lemmas = addLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    unsigned refuted = 0;
    for (unsigned x = 0; x < VALUES; ++x)
      for (unsigned s = 0; s < VALUES; ++s)
        for (unsigned t = 0; t < VALUES; ++t)
          if (!addLemmaHolds(lemmas[i], bitsOf(x), bitsOf(s), bitsOf(t)))
            ++refuted;
    EXPECT_GT(refuted, 0u) << addLemmaName(lemmas[i]) << " excludes no triple";
  }
}

TEST_F(BVAddLemmaTest, the_circuit_agrees_with_the_predicate)
{
  unsigned count = 0;
  const AddLemma* lemmas = addLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const AddLemma lemma = lemmas[i];
    buildCircuit(lemma);
    for (unsigned x = 0; x < VALUES; ++x)
      for (unsigned s = 0; s < VALUES; ++s)
        for (unsigned t = 0; t < VALUES; ++t)
        {
          const bool want = addLemmaHolds(lemma, bitsOf(x), bitsOf(s), bitsOf(t));
          ASSERT_EQ(want, circuitPermits(x, s, t))
              << addLemmaName(lemma) << " at x=" << x << " s=" << s
              << " t=" << t;
        }
  }
}

TEST(BVAddLemma, chooser_only_returns_violated_facts)
{
  unsigned count = 0;
  const AddLemma* lemmas = addLemmaTable(count);
  for (unsigned x = 0; x < VALUES; ++x)
    for (unsigned s = 0; s < VALUES; ++s)
      for (unsigned t = 0; t < VALUES; ++t)
      {
        const AddSchemaChoice choice =
            chooseAddSchema(bitsOf(x), bitsOf(s), bitsOf(t), 0);
        if (t == referenceAdd(x, s))
        {
          ASSERT_FALSE(choice.found)
              << "correct candidate refined at x=" << x << " s=" << s;
          continue;
        }
        if (!choice.found)
          continue;
        ASSERT_LT(choice.lemmaIndex, count);
        const unsigned ops[2] = {x, s};
        ASSERT_FALSE(addLemmaHolds(lemmas[choice.lemmaIndex],
                                   bitsOf(ops[choice.operand]),
                                   bitsOf(ops[1 - choice.operand]), bitsOf(t)))
            << addLemmaName(lemmas[choice.lemmaIndex]) << " at x=" << x
            << " s=" << s << " t=" << t;
      }
}

TEST(BVAddLemma, installed_facts_are_not_offered_again)
{
  unsigned count = 0;
  addLemmaTable(count);
  uint64_t installed = 0;
  for (unsigned i = 0; i < count; ++i)
    for (unsigned operand = 0; operand < 2; ++operand)
      installed |= addLemmaInstalledBit(i, operand);

  for (unsigned x = 0; x < VALUES; ++x)
    for (unsigned s = 0; s < VALUES; ++s)
      for (unsigned t = 0; t < VALUES; ++t)
        EXPECT_FALSE(
            chooseAddSchema(bitsOf(x), bitsOf(s), bitsOf(t), installed).found);
}

TEST(BVAddLemma, small_width_restrictions_are_explicit)
{
  EXPECT_FALSE(addLemmaApplicable(AddLemma::AddRef10, 2));
  EXPECT_TRUE(addLemmaApplicable(AddLemma::AddRef10, 3));
  EXPECT_FALSE(addLemmaApplicable(AddLemma::AddRef11, 1));
  EXPECT_TRUE(addLemmaApplicable(AddLemma::AddRef11, 2));
  EXPECT_FALSE(addLemmaApplicable(AddLemma::AddRef12, 2));
  EXPECT_TRUE(addLemmaApplicable(AddLemma::AddRef12, 3));
  EXPECT_TRUE(addLemmaApplicable(AddLemma::AddRef9, 1));
}
