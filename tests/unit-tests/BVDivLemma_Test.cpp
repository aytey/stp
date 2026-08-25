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
// These are transcribed from another solver, and most of them are not facts
// anyone would arrive at by reasoning about division -- `x >=u -((-s) & (-t))`
// is a synthesised inequality, not a theorem someone wrote down. Transcription
// is exactly the kind of thing that goes wrong silently: a lemma that is
// nearly right holds on most operands, is installed unconditionally and never
// taken back, and turns a satisfiable query unsat only on the inputs that
// reach it.
//
// So nothing here trusts the transcription. Three independent checks, and
// they have to agree with each other and with division:
//
//   * The predicate the refiner uses to decide whether a candidate breaks a
//     lemma is evaluated at the *true* quotient, over every pair of operands.
//     A lemma false of real division is caught here, whatever the circuit
//     does.
//
//   * ... at every width from one bit up, not only the width the circuit is
//     checked at. That is what says the minimum width each fact declares is
//     the truth: sound at and above it, and genuinely broken one bit below.
//
//   * The circuit that goes into the solver is then asked, over every triple,
//     whether it permits that triple -- and it must permit exactly the ones
//     the predicate calls true. That catches a circuit that says something
//     other than its predicate, including the barrel shifters underneath the
//     seven that shift by a variable amount.
//
// Four bits for the circuit, exhaustively, which is 4096 triples per fact;
// and three as well, because a width that is not a power of two is where a
// barrel shifter's stage count stops dividing the width and the saturating
// tail has to make up the difference. Wide enough for a shift amount to run
// past the width -- which is where a shifter's other edge case lives -- and
// small enough that nothing is sampled.
//
// The facts are taken from the refiner's own table rather than listed here,
// so a fact added to one and not to the other is not a fact that goes
// untested; and the circuit is built once per fact, with the triple asked for
// by assumption, because encoding is the expensive half by a wide margin and
// there are eighteen of them.
#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/ToSat/BVExactEncoder.h"

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

// The widest bit vector the exhaustive value sweeps go to, and the widths
// the circuit is checked at.
const unsigned MAX_WIDTH = 5;
const unsigned CIRCUIT_WIDTHS[2] = {3, 4};

std::vector<DivLemma> lemmas()
{
  unsigned count = 0;
  const DivLemma* table = divLemmaTable(count);
  return std::vector<DivLemma>(table, table + count);
}

std::vector<bool> bitsOf(unsigned value, unsigned width)
{
  std::vector<bool> bits(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

// SMT-LIB's bvudiv, totalised: division by zero is all ones.
unsigned referenceDiv(unsigned x, unsigned s, unsigned width)
{
  return (s == 0) ? ((1u << width) - 1) : (x / s);
}

class BVDivLemmaTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  // One fact's circuit, in a solver of its own, with the dividend, the
  // divisor and the result carried by variables the triple is asserted over
  // as assumptions rather than as clauses.
  struct Circuit
  {
    std::unique_ptr<SATSolver> solver;
    // The dividend's bits, then the divisor's, then the result's.
    std::vector<unsigned> vars;
    unsigned width = 0;
  };

  Circuit build(DivLemma lemma, unsigned width)
  {
    Circuit c;
    c.width = width;
    c.solver.reset(createSATSolver(mgr.UserFlags));
    EXPECT_TRUE(c.solver != NULL) << "no SAT backend was compiled in";

    std::vector<unsigned> xVars(width), sVars(width), tVars(width);
    std::vector<unsigned>* group[3] = {&xVars, &sVars, &tVars};
    for (unsigned i = 0; i < width; ++i)
      for (unsigned v = 0; v < 3; ++v)
      {
        (*group[v])[i] = c.solver->newVar();
        c.solver->setFrozen((*group[v])[i]);
      }

    BVExactEncoder(&mgr).encodeDivLemma(*c.solver, lemma, width, xVars, sVars,
                                        tVars);

    for (unsigned v = 0; v < 3; ++v)
      c.vars.insert(c.vars.end(), group[v]->begin(), group[v]->end());
    return c;
  }

  // Does the circuit permit this triple?
  bool permits(Circuit& c, unsigned x, unsigned s, unsigned t)
  {
    SATSolver::vec_literals assumps;
    const unsigned vals[3] = {x, s, t};
    for (unsigned v = 0; v < 3; ++v)
      for (unsigned i = 0; i < c.width; ++i)
        assumps.push(SATSolver::mkLit(c.vars[v * c.width + i],
                                      ((vals[v] >> i) & 1u) == 0));

    bool timedOut = false;
    const bool sat = c.solver->solveWithAssumptions(assumps, timedOut);
    EXPECT_FALSE(timedOut);
    return sat;
  }
};

} // namespace

// Every lemma is true of division itself, at every pair of operands and at
// every width it declares itself good for. This is the soundness claim: they
// are asserted unconditionally and never retracted.
TEST(BVDivLemma, every_lemma_is_true_of_division)
{
  for (DivLemma lemma : lemmas())
    for (unsigned width = divLemmaMinWidth(lemma); width <= MAX_WIDTH; ++width)
    {
      const unsigned values = 1u << width;
      for (unsigned x = 0; x < values; x++)
        for (unsigned s = 0; s < values; s++)
        {
          const unsigned t = referenceDiv(x, s, width);
          ASSERT_TRUE(divLemmaHolds(lemma, bitsOf(x, width), bitsOf(s, width),
                                    bitsOf(t, width)))
              << divLemmaName(lemma) << " is false at " << width
              << " bits of x=" << x << " s=" << s << " (quotient " << t << ")";
        }
    }
}

// ... and the minimum each declares is the narrowest it is true of, not a
// margin someone rounded up. A minimum that is too high costs a fact on
// narrow abstractions for nothing; one that is too low is unsoundness, and
// the sweep above would not see it.
TEST(BVDivLemma, a_declared_minimum_width_is_the_narrowest_that_works)
{
  for (DivLemma lemma : lemmas())
  {
    const unsigned min = divLemmaMinWidth(lemma);
    if (min == 1)
      continue;

    const unsigned width = min - 1;
    const unsigned values = 1u << width;
    bool broken = false;
    for (unsigned x = 0; x < values && !broken; x++)
      for (unsigned s = 0; s < values && !broken; s++)
        broken = !divLemmaHolds(lemma, bitsOf(x, width), bitsOf(s, width),
                                bitsOf(referenceDiv(x, s, width), width));

    EXPECT_TRUE(broken) << divLemmaName(lemma) << " declares a minimum of "
                        << min << " bits but is true of division at " << width;
  }
}

// Each lemma rules something out. One true of every triple would be sound and
// useless: the refiner would spend a round on it and the search would be free
// to offer the same candidate again.
TEST(BVDivLemma, every_lemma_rules_something_out)
{
  const unsigned width = 4;
  const unsigned values = 1u << width;
  for (DivLemma lemma : lemmas())
  {
    unsigned refuted = 0;
    for (unsigned x = 0; x < values; x++)
      for (unsigned s = 0; s < values; s++)
        for (unsigned t = 0; t < values; t++)
          if (!divLemmaHolds(lemma, bitsOf(x, width), bitsOf(s, width),
                             bitsOf(t, width)))
            refuted++;
    EXPECT_GT(refuted, 0u) << divLemmaName(lemma) << " excludes no triple";
  }
}

// The circuit that goes into the solver says what its predicate says --
// permitting exactly the triples the predicate calls true.
TEST_F(BVDivLemmaTest, the_circuit_agrees_with_the_predicate)
{
  for (unsigned width : CIRCUIT_WIDTHS)
  {
    const unsigned values = 1u << width;
    for (DivLemma lemma : lemmas())
    {
      if (width < divLemmaMinWidth(lemma))
        continue;
      Circuit c = build(lemma, width);
      for (unsigned x = 0; x < values; x++)
        for (unsigned s = 0; s < values; s++)
          for (unsigned t = 0; t < values; t++)
          {
            const bool want = divLemmaHolds(
                lemma, bitsOf(x, width), bitsOf(s, width), bitsOf(t, width));
            ASSERT_EQ(want, permits(c, x, s, t))
                << divLemmaName(lemma) << " at " << width << " bits, x=" << x
                << " s=" << s << " t=" << t;
          }
    }
  }
}
