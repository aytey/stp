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

// Exhaustive checks for the synthesised multiplication facts that complement
// the hand-written/value-guarded schemas in BVMultSchema_Test.
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

unsigned referenceMul(unsigned x, unsigned s)
{
  return (x * s) & (VALUES - 1);
}

class BVMulLemmaTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  std::unique_ptr<SATSolver> solver;
  std::vector<unsigned> xVars, sVars, tVars;

  void buildCircuit(MulLemma lemma)
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

    BVExactEncoder(&mgr).encodeMulLemma(*solver, lemma, WIDTH, xVars, sVars,
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

TEST(BVMulLemma, every_lemma_is_true_of_multiplication)
{
  unsigned count = 0;
  const MulLemma* lemmas = mulLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const MulLemma lemma = lemmas[i];
    ASSERT_TRUE(mulLemmaApplicable(lemma, WIDTH));
    for (unsigned x = 0; x < VALUES; ++x)
      for (unsigned s = 0; s < VALUES; ++s)
      {
        const unsigned t = referenceMul(x, s);
        ASSERT_TRUE(mulLemmaHolds(lemma, bitsOf(x), bitsOf(s), bitsOf(t)))
            << mulLemmaName(lemma) << " is false of x=" << x << " s=" << s
            << " (product " << t << ")";
      }
  }
}

TEST(BVMulLemma, every_lemma_is_true_at_each_small_applicable_width)
{
  unsigned count = 0;
  const MulLemma* lemmas = mulLemmaTable(count);
  for (unsigned width = 1; width <= 6; ++width)
  {
    const unsigned values = 1u << width;
    const unsigned mask = values - 1;
    for (unsigned i = 0; i < count; ++i)
    {
      const MulLemma lemma = lemmas[i];
      if (!mulLemmaApplicable(lemma, width))
        continue;
      for (unsigned x = 0; x < values; ++x)
        for (unsigned s = 0; s < values; ++s)
        {
          const unsigned t = (x * s) & mask;
          ASSERT_TRUE(mulLemmaHolds(lemma, bitsOf(x, width), bitsOf(s, width),
                                    bitsOf(t, width)))
              << mulLemmaName(lemma) << " is false at width " << width
              << " for x=" << x << " s=" << s << " (product " << t << ")";
        }
    }
  }
}

TEST(BVMulLemma, every_lemma_rules_something_out)
{
  unsigned count = 0;
  const MulLemma* lemmas = mulLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const MulLemma lemma = lemmas[i];
    unsigned refuted = 0;
    for (unsigned x = 0; x < VALUES; ++x)
      for (unsigned s = 0; s < VALUES; ++s)
        for (unsigned t = 0; t < VALUES; ++t)
          if (!mulLemmaHolds(lemma, bitsOf(x), bitsOf(s), bitsOf(t)))
            ++refuted;
    EXPECT_GT(refuted, 0u) << mulLemmaName(lemma) << " excludes no triple";
  }
}

TEST_F(BVMulLemmaTest, the_circuit_agrees_with_the_predicate)
{
  unsigned count = 0;
  const MulLemma* lemmas = mulLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const MulLemma lemma = lemmas[i];
    buildCircuit(lemma);
    for (unsigned x = 0; x < VALUES; ++x)
      for (unsigned s = 0; s < VALUES; ++s)
        for (unsigned t = 0; t < VALUES; ++t)
        {
          const bool want = mulLemmaHolds(lemma, bitsOf(x), bitsOf(s), bitsOf(t));
          ASSERT_EQ(want, circuitPermits(x, s, t))
              << mulLemmaName(lemma) << " at x=" << x << " s=" << s
              << " t=" << t;
        }
  }
}

TEST(BVMulLemma, width_restrictions_are_explicit)
{
  EXPECT_FALSE(mulLemmaApplicable(MulLemma::MulRef1, 1));
  EXPECT_TRUE(mulLemmaApplicable(MulLemma::MulRef1, 2));
  EXPECT_TRUE(mulLemmaApplicable(MulLemma::MulRefN5, 1));
  EXPECT_FALSE(mulLemmaApplicable(MulLemma::MulRefN5, 2));
  EXPECT_TRUE(mulLemmaApplicable(MulLemma::MulRefN5, 3));
  EXPECT_TRUE(mulLemmaApplicable(MulLemma::MulRefN6, 1));
}
