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

// `x = t*s + r`, the one fact the abstraction has about two of its records at
// once, checked the way every other one is: the predicate at the true
// quotient and remainder over every pair of operands, and then the circuit
// against the predicate over every quadruple.
//
// A quadruple rather than a triple is the whole difference, and it is why
// this is not folded into BVAbstractionLemma_Test: 4096 of them at three bits
// and 65536 at four, against 512 and 4096 there.
//
// The exhaustive sweep is also the answer to a question the other facts do
// not raise. Truncated multiplication makes this a fact and not a definition:
// the true quotient never overflows `t*s`, but a candidate quotient can, and
// then the identity can hold of a pair that division does not produce. So the
// circuit must permit exactly the quadruples the predicate calls true --
// including those -- rather than exactly the true ones.
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

const unsigned MAX_WIDTH = 6;
const unsigned CIRCUIT_WIDTHS[2] = {3, 4};

std::vector<bool> bitsOf(unsigned value, unsigned width)
{
  std::vector<bool> bits(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

// SMT-LIB's bvudiv and bvurem, totalised the way the unabstracted circuit
// totalises them.
unsigned referenceDiv(unsigned x, unsigned s, unsigned width)
{
  return (s == 0) ? ((1u << width) - 1) : (x / s);
}

unsigned referenceRem(unsigned x, unsigned s)
{
  return (s == 0) ? x : (x % s);
}

class BVDivModIdentityTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  struct Circuit
  {
    std::unique_ptr<SATSolver> solver;
    // The dividend's bits, then the divisor's, the quotient's, the
    // remainder's.
    std::vector<unsigned> vars;
    unsigned width = 0;
  };

  // A BVMULT node for the multiplier to read. Two plain symbols, which is
  // what the refiner hands it when neither operand is a constant.
  ASTNode productNode(unsigned width)
  {
    const ASTNode q = mgr.CreateSymbol("q", 0, width);
    const ASTNode d = mgr.CreateSymbol("d", 0, width);
    return mgr.defaultNodeFactory->CreateTerm(BVMULT, width, q, d);
  }

  Circuit build(unsigned width)
  {
    Circuit c;
    c.width = width;
    c.solver.reset(createSATSolver(mgr.UserFlags));
    EXPECT_TRUE(c.solver != NULL) << "no SAT backend was compiled in";

    std::vector<unsigned> group[4];
    for (unsigned v = 0; v < 4; ++v)
      group[v].resize(width);
    for (unsigned i = 0; i < width; ++i)
      for (unsigned v = 0; v < 4; ++v)
      {
        group[v][i] = c.solver->newVar();
        c.solver->setFrozen(group[v][i]);
      }

    BVExactEncoder(&mgr).encodeDivModIdentity(*c.solver, productNode(width),
                                              width, group[0], group[1],
                                              group[2], group[3]);

    for (unsigned v = 0; v < 4; ++v)
      c.vars.insert(c.vars.end(), group[v].begin(), group[v].end());
    return c;
  }

  bool permits(Circuit& c, unsigned x, unsigned s, unsigned t, unsigned r)
  {
    SATSolver::vec_literals assumps;
    const unsigned vals[4] = {x, s, t, r};
    for (unsigned v = 0; v < 4; ++v)
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

// True of division and remainder themselves, at every pair of operands and
// every width. It is asserted unconditionally and never retracted, and it
// carries no premise at all -- not even a non-zero divisor, since the
// totalised quotient is all ones there, `t*s` is zero and `r` is `x`.
TEST(BVDivModIdentity, holds_of_the_operations_at_every_width)
{
  for (unsigned width = 1; width <= MAX_WIDTH; ++width)
  {
    const unsigned values = 1u << width;
    for (unsigned x = 0; x < values; x++)
      for (unsigned s = 0; s < values; s++)
        ASSERT_TRUE(divModIdentityHolds(
            bitsOf(x, width), bitsOf(s, width),
            bitsOf(referenceDiv(x, s, width), width),
            bitsOf(referenceRem(x, s), width)))
            << "the identity is false at " << width << " bits of x=" << x
            << " s=" << s;
  }
}

// It rules out a great deal more than the facts about a single record do,
// which is the reason for the machinery that finds the pair. At four bits it
// admits one quadruple in sixteen.
TEST(BVDivModIdentity, rules_out_all_but_one_quadruple_in_a_width)
{
  for (unsigned width = 2; width <= 4; ++width)
  {
    const unsigned values = 1u << width;
    unsigned admitted = 0;
    for (unsigned x = 0; x < values; x++)
      for (unsigned s = 0; s < values; s++)
        for (unsigned t = 0; t < values; t++)
          for (unsigned r = 0; r < values; r++)
            if (divModIdentityHolds(bitsOf(x, width), bitsOf(s, width),
                                    bitsOf(t, width), bitsOf(r, width)))
              admitted++;

    // For every (x, s, t) exactly one r satisfies it: the identity fixes the
    // remainder once the other three are chosen.
    EXPECT_EQ(admitted, values * values * values)
        << "at " << width << " bits";
  }
}

// The circuit permits exactly the quadruples the predicate calls true.
TEST_F(BVDivModIdentityTest, the_circuit_agrees_with_the_predicate)
{
  for (unsigned width : CIRCUIT_WIDTHS)
  {
    const unsigned values = 1u << width;
    Circuit c = build(width);
    for (unsigned x = 0; x < values; x++)
      for (unsigned s = 0; s < values; s++)
        for (unsigned t = 0; t < values; t++)
          for (unsigned r = 0; r < values; r++)
          {
            const bool want =
                divModIdentityHolds(bitsOf(x, width), bitsOf(s, width),
                                    bitsOf(t, width), bitsOf(r, width));
            ASSERT_EQ(want, permits(c, x, s, t, r))
                << "at " << width << " bits, x=" << x << " s=" << s
                << " t=" << t << " r=" << r;
          }
  }
}
