/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
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
********************************************************************/

// The three relations that pin a result's low bits exactly rather than
// bounding the whole of it: the sum's, the product's, and the one that
// recomposes a dividend out of a quotient and a remainder.
//
// Every one of them is a theorem for the same reason -- a low bit of a sum
// or a product depends only on equally low bits of its operands, so
// `t[2:0] = (a op b)[2:0]` is true of the whole operation and not an
// approximation of it. That is the claim these tests are for, and it is
// checked in both directions: the predicate against the real operation at
// every pair of operands, and the clauses against the predicate at every
// triple. A quotient's low bits have no such property, which is why the
// third relation is about the recomposition and not about the quotient.

#include "stp/ToSat/BVAbstractionRefiner.h"

#include "stp/AST/AST.h"
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
const unsigned MASK = VALUES - 1;

std::vector<bool> bitsOf(unsigned value)
{
  std::vector<bool> bits(WIDTH);
  for (unsigned i = 0; i < WIDTH; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

unsigned referenceDiv(unsigned a, unsigned b)
{
  return (b == 0) ? MASK : (a / b);
}

unsigned referenceRem(unsigned a, unsigned b)
{
  return (b == 0) ? a : (a % b);
}

unsigned prefixMask()
{
  return (1u << lowPrefixWidth(WIDTH)) - 1;
}

class BVLowPrefixTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  std::unique_ptr<SATSolver> makeSolver()
  {
    return std::unique_ptr<SATSolver>(createSATSolver(mgr.UserFlags));
  }

  static void pin(SATSolver& solver, const std::vector<unsigned>& vars,
                  unsigned value)
  {
    for (unsigned i = 0; i < vars.size(); ++i)
    {
      SATSolver::vec_literals cl;
      cl.push(SATSolver::mkLit(vars[i], ((value >> i) & 1u) == 0));
      solver.addClause(cl);
    }
  }

  static std::vector<unsigned> fresh(SATSolver& solver, unsigned count)
  {
    std::vector<unsigned> vars(count);
    for (unsigned i = 0; i < count; ++i)
    {
      vars[i] = solver.newVar();
      solver.setFrozen(vars[i]);
    }
    return vars;
  }
};

} // namespace

// The predicate says of the true sum and the true product exactly what the
// operation does. If it did not, the schema would be installed against
// results the operation really produces.
TEST(BVLowPrefix, the_predicate_agrees_with_the_operation)
{
  const unsigned prefix = lowPrefixWidth(WIDTH);
  ASSERT_EQ(prefix, 3u);

  for (unsigned a = 0; a < VALUES; a++)
    for (unsigned b = 0; b < VALUES; b++)
    {
      ASSERT_TRUE(exactLowPrefixHolds(BVPLUS, bitsOf(a), bitsOf(b),
                                      bitsOf((a + b) & MASK), prefix))
          << "the sum prefix is false at a=" << a << " b=" << b;
      ASSERT_TRUE(exactLowPrefixHolds(BVMULT, bitsOf(a), bitsOf(b),
                                      bitsOf((a * b) & MASK), prefix))
          << "the product prefix is false at a=" << a << " b=" << b;
    }
}

// ... and it reads only the low bits. A result that agrees below the prefix
// and disagrees above it still satisfies the schema, which is what makes the
// schema a piece of the operation rather than the whole of it -- and what
// leaves the search free above it.
TEST(BVLowPrefix, the_predicate_leaves_the_high_bits_free)
{
  const unsigned prefix = lowPrefixWidth(WIDTH);
  const unsigned low = prefixMask();

  unsigned freeAbove = 0;
  for (unsigned a = 0; a < VALUES; a++)
    for (unsigned b = 0; b < VALUES; b++)
      for (unsigned t = 0; t < VALUES; t++)
      {
        const bool agreesLow = ((a + b) & low) == (t & low);
        ASSERT_EQ(agreesLow,
                  exactLowPrefixHolds(BVPLUS, bitsOf(a), bitsOf(b), bitsOf(t),
                                      prefix))
            << "sum prefix at a=" << a << " b=" << b << " t=" << t;
        if (agreesLow && t != ((a + b) & MASK))
          freeAbove++;
      }

  EXPECT_GT(freeAbove, 0u)
      << "no result was admitted that differs above the prefix, so this test "
         "is not checking what it claims to";
}

// The clauses say what the predicate says, over every triple.
TEST_F(BVLowPrefixTest, the_sum_clauses_agree_with_the_predicate)
{
  const unsigned prefix = lowPrefixWidth(WIDTH);

  // Both lowerings: operands as written, and one of them standing for its
  // own two's complement. The blaster refuses to abstract an addition whose
  // operands are both negated, so that combination is not offered here.
  const bool negations[3][2] = {{false, false}, {true, false}, {false, true}};

  for (const auto& neg : negations)
    for (unsigned a = 0; a < VALUES; a++)
      for (unsigned b = 0; b < VALUES; b++)
        for (unsigned t = 0; t < VALUES; t++)
        {
          std::unique_ptr<SATSolver> solver = makeSolver();
          ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";

          const std::vector<unsigned> av = fresh(*solver, WIDTH);
          const std::vector<unsigned> bv = fresh(*solver, WIDTH);
          const std::vector<unsigned> tv = fresh(*solver, WIDTH);

          encodeAddLowPrefix(*solver, av, bv, tv, prefix, neg[0], neg[1]);
          pin(*solver, av, a);
          pin(*solver, bv, b);
          pin(*solver, tv, t);

          bool timedOut = false;
          const bool sat = solver->solve(timedOut);
          ASSERT_FALSE(timedOut);

          // The predicate is written over what the record adds, so the
          // negation is applied to the value before asking it.
          const unsigned ea = neg[0] ? ((VALUES - a) & MASK) : a;
          const unsigned eb = neg[1] ? ((VALUES - b) & MASK) : b;
          ASSERT_EQ(exactLowPrefixHolds(BVPLUS, bitsOf(ea), bitsOf(eb),
                                        bitsOf(t), prefix),
                    sat)
              << "a=" << a << " (neg " << neg[0] << ") b=" << b << " (neg "
              << neg[1] << ") t=" << t;
        }
}

TEST_F(BVLowPrefixTest, the_product_clauses_agree_with_the_predicate)
{
  const unsigned prefix = lowPrefixWidth(WIDTH);

  for (unsigned a = 0; a < VALUES; a++)
    for (unsigned b = 0; b < VALUES; b++)
      for (unsigned t = 0; t < VALUES; t++)
      {
        std::unique_ptr<SATSolver> solver = makeSolver();
        ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";

        const std::vector<unsigned> av = fresh(*solver, WIDTH);
        const std::vector<unsigned> bv = fresh(*solver, WIDTH);
        const std::vector<unsigned> tv = fresh(*solver, WIDTH);

        encodeMulLowPrefix(*solver, av, bv, tv, prefix);
        pin(*solver, av, a);
        pin(*solver, bv, b);
        pin(*solver, tv, t);

        bool timedOut = false;
        const bool sat = solver->solve(timedOut);
        ASSERT_FALSE(timedOut);
        ASSERT_EQ(exactLowPrefixHolds(BVMULT, bitsOf(a), bitsOf(b), bitsOf(t),
                                      prefix),
                  sat)
            << "a=" << a << " b=" << b << " t=" << t;
      }
}

// `low(x) = low(q*s + r)` at the true quotient and remainder, over every
// pair of operands -- including a zero divisor, where SMT-LIB's totalised
// answers are q = ~0 and r = x, and `~0 * 0 + x` is x.
TEST(BVLowPrefix, the_recomposition_is_true_of_division)
{
  const unsigned prefix = lowPrefixWidth(WIDTH);

  for (unsigned a = 0; a < VALUES; a++)
    for (unsigned b = 0; b < VALUES; b++)
      ASSERT_TRUE(divRemLowPrefixHolds(bitsOf(a), bitsOf(b),
                                       bitsOf(referenceDiv(a, b)),
                                       bitsOf(referenceRem(a, b)), prefix))
          << "the recomposition prefix is false at a=" << a << " b=" << b;
}

// ... and its clauses agree with its predicate over all 65536 quadruples.
TEST_F(BVLowPrefixTest, the_recomposition_clauses_agree_with_the_predicate)
{
  const unsigned prefix = lowPrefixWidth(WIDTH);

  for (unsigned a = 0; a < VALUES; a++)
    for (unsigned b = 0; b < VALUES; b++)
      for (unsigned q = 0; q < VALUES; q++)
        for (unsigned r = 0; r < VALUES; r++)
        {
          std::unique_ptr<SATSolver> solver = makeSolver();
          ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";

          const std::vector<unsigned> av = fresh(*solver, WIDTH);
          const std::vector<unsigned> bv = fresh(*solver, WIDTH);
          const std::vector<unsigned> qv = fresh(*solver, WIDTH);
          const std::vector<unsigned> rv = fresh(*solver, WIDTH);

          encodeDivRemLowPrefix(*solver, av, bv, qv, rv, prefix);
          pin(*solver, av, a);
          pin(*solver, bv, b);
          pin(*solver, qv, q);
          pin(*solver, rv, r);

          bool timedOut = false;
          const bool sat = solver->solve(timedOut);
          ASSERT_FALSE(timedOut);
          ASSERT_EQ(divRemLowPrefixHolds(bitsOf(a), bitsOf(b), bitsOf(q),
                                         bitsOf(r), prefix),
                    sat)
              << "a=" << a << " b=" << b << " q=" << q << " r=" << r;
        }
}
