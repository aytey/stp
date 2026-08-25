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

// The algebraic facts an abstracted BVDIV is refined with, beyond the ones
// that name a divisor.
//
// These are transcribed from another solver, and four of them are not facts
// anyone would arrive at by reasoning about division -- `x >=u -((-s) & (-t))`
// is a synthesised inequality, not a theorem someone wrote down. Transcription
// is exactly the kind of thing that goes wrong silently: a lemma that is
// nearly right holds on most operands, is installed unconditionally and never
// taken back, and turns a satisfiable query unsat only on the inputs that
// reach it.
//
// So nothing here trusts the transcription. Two independent checks, and they
// have to agree with each other and with division:
//
//   * The predicate the refiner uses to decide whether a candidate breaks a
//     lemma is evaluated at the *true* quotient, over every pair of operands.
//     A lemma false of real division is caught here, whatever the circuit
//     does.
//
//   * The circuit that goes into the solver is then asked, over every triple,
//     whether it permits that triple -- and it must permit exactly the ones
//     the predicate calls true. That catches a circuit that says something
//     other than its predicate, including the barrel shifters underneath the
//     facts that shift by a variable amount.
//
// Four bits, exhaustively, which is 256 operand pairs and 4096 triples per
// lemma. Wide enough for a shift amount to run past the width -- which is
// where a shifter's edge case lives -- and small enough that nothing is
// sampled.
#include "stp/ToSat/BVExactEncoder.h"
#include "stp/ToSat/BVAbstractionRefiner.h"

#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"
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

// SMT-LIB's bvudiv, totalised: division by zero is all ones.
unsigned referenceDiv(unsigned x, unsigned s)
{
  return (s == 0) ? (VALUES - 1) : (x / s);
}

class BVDivLemmaTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  std::unique_ptr<SATSolver> solver;
  std::vector<unsigned> xVars, sVars, tVars;
  unsigned circuitWidth = WIDTH;

  void buildCircuit(DivLemma lemma, unsigned width = WIDTH)
  {
    circuitWidth = width;
    solver.reset(createSATSolver(mgr.UserFlags));
    ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
    ASSERT_TRUE(solver->supportsAssumptions());

    xVars.resize(width);
    sVars.resize(width);
    tVars.resize(width);
    for (unsigned i = 0; i < width; ++i)
    {
      xVars[i] = solver->newVar();
      sVars[i] = solver->newVar();
      tVars[i] = solver->newVar();
      solver->setFrozen(xVars[i]);
      solver->setFrozen(sVars[i]);
      solver->setFrozen(tVars[i]);
    }

    BVExactEncoder(&mgr).encodeDivLemma(*solver, lemma, width, xVars, sVars,
                                        tVars);
  }

  // Does the circuit for `lemma` permit this triple?
  bool circuitPermits(unsigned x, unsigned s, unsigned t)
  {
    SATSolver::vec_literals assumptions;
    const unsigned vals[3] = {x, s, t};
    const std::vector<unsigned>* vars[3] = {&xVars, &sVars, &tVars};
    for (unsigned v = 0; v < 3; ++v)
      for (unsigned i = 0; i < circuitWidth; ++i)
        assumptions.push(
            SATSolver::mkLit((*vars[v])[i], ((vals[v] >> i) & 1u) == 0));

    bool timedOut = false;
    const bool sat = solver->solveWithAssumptions(assumptions, timedOut);
    EXPECT_FALSE(timedOut);
    return sat;
  }
};

} // namespace

TEST(BVDivLemma, registry_is_complete)
{
  unsigned count = 0;
  divLemmaTable(count);
  EXPECT_EQ(33u, count);
}

// Every lemma is true of division itself, at every pair of operands. This is
// the soundness claim: they are asserted unconditionally and never retracted.
TEST(BVDivLemma, every_lemma_is_true_of_division)
{
  unsigned count = 0;
  const DivLemma* lemmas = divLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const DivLemma lemma = lemmas[i];
    ASSERT_TRUE(divLemmaApplicable(lemma, WIDTH));
    for (unsigned x = 0; x < VALUES; x++)
      for (unsigned s = 0; s < VALUES; s++)
      {
        const unsigned t = referenceDiv(x, s);
        ASSERT_TRUE(divLemmaHolds(lemma, bitsOf(x), bitsOf(s), bitsOf(t)))
            << divLemmaName(lemma) << " is false of x=" << x << " s=" << s
            << " (quotient " << t << ")";
      }
  }
}

// Width restrictions are part of the theorem, not performance guards. Check
// every supported small width so a fact that happens to hold at four bits
// cannot hide a missing restriction.
TEST(BVDivLemma, every_lemma_is_true_at_each_small_applicable_width)
{
  unsigned count = 0;
  const DivLemma* lemmas = divLemmaTable(count);
  for (unsigned width = 1; width <= 6; ++width)
  {
    const unsigned values = 1u << width;
    for (unsigned i = 0; i < count; ++i)
    {
      const DivLemma lemma = lemmas[i];
      if (!divLemmaApplicable(lemma, width))
        continue;
      for (unsigned x = 0; x < values; ++x)
        for (unsigned s = 0; s < values; ++s)
        {
          const unsigned t = (s == 0) ? values - 1 : x / s;
          ASSERT_TRUE(divLemmaHolds(lemma, bitsOf(x, width), bitsOf(s, width),
                                    bitsOf(t, width)))
              << divLemmaName(lemma) << " is false at width " << width
              << " for x=" << x << " s=" << s << " (quotient " << t
              << ")";
        }
    }
  }
}

// Each lemma rules something out. One true of every triple would be sound and
// useless: the refiner would spend a round on it and the search would be free
// to offer the same candidate again.
TEST(BVDivLemma, every_lemma_rules_something_out)
{
  unsigned count = 0;
  const DivLemma* lemmas = divLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const DivLemma lemma = lemmas[i];
    unsigned refuted = 0;
    for (unsigned x = 0; x < VALUES; x++)
      for (unsigned s = 0; s < VALUES; s++)
        for (unsigned t = 0; t < VALUES; t++)
          if (!divLemmaHolds(lemma, bitsOf(x), bitsOf(s), bitsOf(t)))
            refuted++;
    EXPECT_GT(refuted, 0u) << divLemmaName(lemma) << " excludes no triple";
  }
}

// The circuit that goes into the solver says what its predicate says --
// permitting exactly the triples the predicate calls true, over all 4096.
TEST_F(BVDivLemmaTest, the_circuit_agrees_with_the_predicate)
{
  unsigned count = 0;
  const DivLemma* lemmas = divLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const DivLemma lemma = lemmas[i];
    buildCircuit(lemma);
    for (unsigned x = 0; x < VALUES; x++)
      for (unsigned s = 0; s < VALUES; s++)
        for (unsigned t = 0; t < VALUES; t++)
        {
          const bool want = divLemmaHolds(lemma, bitsOf(x), bitsOf(s), bitsOf(t));
          ASSERT_EQ(want, circuitPermits(x, s, t))
              << divLemmaName(lemma) << " at x=" << x << " s=" << s
              << " t=" << t;
        }
  }
}

TEST_F(BVDivLemmaTest, the_circuit_agrees_at_each_smaller_applicable_width)
{
  unsigned count = 0;
  const DivLemma* lemmas = divLemmaTable(count);
  for (unsigned width = 1; width < WIDTH; ++width)
  {
    const unsigned values = 1u << width;
    for (unsigned i = 0; i < count; ++i)
    {
      const DivLemma lemma = lemmas[i];
      if (!divLemmaApplicable(lemma, width))
        continue;
      buildCircuit(lemma, width);
      for (unsigned x = 0; x < values; ++x)
        for (unsigned s = 0; s < values; ++s)
          for (unsigned t = 0; t < values; ++t)
            ASSERT_EQ(divLemmaHolds(lemma, bitsOf(x, width), bitsOf(s, width),
                                    bitsOf(t, width)),
                      circuitPermits(x, s, t))
                << divLemmaName(lemma) << " at width " << width << " x=" << x
                << " s=" << s << " t=" << t;
    }
  }
}

TEST(BVDivLemma, width_restrictions_are_explicit)
{
  EXPECT_FALSE(divLemmaApplicable(DivLemma::UdivRef21, 1));
  EXPECT_TRUE(divLemmaApplicable(DivLemma::UdivRef21, 2));
  EXPECT_FALSE(divLemmaApplicable(DivLemma::UdivRef33, 1));
  EXPECT_TRUE(divLemmaApplicable(DivLemma::UdivRef33, 2));
  EXPECT_FALSE(divLemmaApplicable(DivLemma::UdivRef31, 2));
  EXPECT_TRUE(divLemmaApplicable(DivLemma::UdivRef31, 3));
  EXPECT_TRUE(divLemmaApplicable(DivLemma::UdivRef38, 1));
  EXPECT_FALSE(divLemmaApplicable(DivLemma::UdivRef38, 2));
  EXPECT_TRUE(divLemmaApplicable(DivLemma::UdivRef38, 3));
  EXPECT_TRUE(divLemmaApplicable(DivLemma::UdivRef9, 1));
}
