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

// Independent exhaustive checks for every transcribed UREM fact, including
// the one Bitwuzla defines but keeps disabled. See BVDivLemma_Test for the
// rationale behind checking both the value predicate and the blasted circuit.
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

unsigned referenceRem(unsigned x, unsigned s)
{
  return (s == 0) ? x : x % s;
}

class BVRemLemmaTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  std::unique_ptr<SATSolver> solver;
  std::vector<unsigned> xVars, sVars, tVars;

  void buildCircuit(RemLemma lemma)
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

    BVExactEncoder(&mgr).encodeRemLemma(*solver, lemma, WIDTH, xVars, sVars,
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

TEST(BVRemLemma, every_lemma_is_true_of_remainder)
{
  unsigned count = 0;
  const RemLemma* lemmas = remLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const RemLemma lemma = lemmas[i];
    ASSERT_TRUE(remLemmaApplicable(lemma, WIDTH));
    for (unsigned x = 0; x < VALUES; ++x)
      for (unsigned s = 0; s < VALUES; ++s)
      {
        const unsigned t = referenceRem(x, s);
        ASSERT_TRUE(remLemmaHolds(lemma, bitsOf(x), bitsOf(s), bitsOf(t)))
            << remLemmaName(lemma) << " is false of x=" << x << " s=" << s
            << " (remainder " << t << ")";
      }
  }
}

TEST(BVRemLemma, every_lemma_is_true_at_each_small_applicable_width)
{
  unsigned count = 0;
  const RemLemma* lemmas = remLemmaTable(count);
  for (unsigned width = 1; width <= 6; ++width)
  {
    const unsigned values = 1u << width;
    for (unsigned i = 0; i < count; ++i)
    {
      const RemLemma lemma = lemmas[i];
      if (!remLemmaApplicable(lemma, width))
        continue;
      for (unsigned x = 0; x < values; ++x)
        for (unsigned s = 0; s < values; ++s)
        {
          const unsigned t = (s == 0) ? x : x % s;
          ASSERT_TRUE(remLemmaHolds(lemma, bitsOf(x, width), bitsOf(s, width),
                                    bitsOf(t, width)))
              << remLemmaName(lemma) << " is false at width " << width
              << " for x=" << x << " s=" << s << " (remainder " << t
              << ")";
        }
    }
  }
}

TEST(BVRemLemma, every_lemma_rules_something_out)
{
  unsigned count = 0;
  const RemLemma* lemmas = remLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const RemLemma lemma = lemmas[i];
    unsigned refuted = 0;
    for (unsigned x = 0; x < VALUES; ++x)
      for (unsigned s = 0; s < VALUES; ++s)
        for (unsigned t = 0; t < VALUES; ++t)
          if (!remLemmaHolds(lemma, bitsOf(x), bitsOf(s), bitsOf(t)))
            ++refuted;
    EXPECT_GT(refuted, 0u) << remLemmaName(lemma) << " excludes no triple";
  }
}

TEST_F(BVRemLemmaTest, the_circuit_agrees_with_the_predicate)
{
  unsigned count = 0;
  const RemLemma* lemmas = remLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const RemLemma lemma = lemmas[i];
    buildCircuit(lemma);
    for (unsigned x = 0; x < VALUES; ++x)
      for (unsigned s = 0; s < VALUES; ++s)
        for (unsigned t = 0; t < VALUES; ++t)
        {
          const bool want = remLemmaHolds(lemma, bitsOf(x), bitsOf(s), bitsOf(t));
          ASSERT_EQ(want, circuitPermits(x, s, t))
              << remLemmaName(lemma) << " at x=" << x << " s=" << s
              << " t=" << t;
        }
  }
}

TEST(BVRemLemma, restrictions_and_disabled_fact_are_explicit)
{
  EXPECT_FALSE(remLemmaApplicable(RemLemma::UremRef12, 2));
  EXPECT_TRUE(remLemmaApplicable(RemLemma::UremRef12, 3));
  EXPECT_FALSE(remLemmaEnabled(RemLemma::UremRef6));
  EXPECT_TRUE(remLemmaEnabled(RemLemma::UremRef7));
}
