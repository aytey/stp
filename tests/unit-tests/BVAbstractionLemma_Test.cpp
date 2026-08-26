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

// The algebraic facts an abstracted BVDIV, BVMOD or BVMULT is refined with,
// beyond the schemas that name an operand's value.
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
// they have to agree with each other and with the operation:
//
//   * The predicate the refiner uses to decide whether a candidate breaks a
//     lemma is evaluated at the *true* result, over every pair of operands.
//     A lemma false of the operation is caught here, whatever the circuit
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
//     nine that shift by a variable amount.
//
// Four bits for the circuit, exhaustively, which is 4096 triples per fact;
// and three as well, because a width that is not a power of two is where a
// barrel shifter's stage count stops dividing the width and the saturating
// tail has to make up the difference. Wide enough for a shift amount to run
// past the width -- which is where a shifter's other edge case lives -- and
// small enough that nothing is sampled.
//
// The facts are taken from the refiner's own tables rather than listed here,
// so a fact that is added to one and not to the other is not a fact that goes
// untested; and the circuit is built once per fact, with the triple asked for
// by assumption, because encoding is the expensive half by a wide margin and
// there are thirty-one of them.
#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/ToSat/BVExactEncoder.h"

#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <gtest/gtest.h>

#include <functional>
#include <memory>
#include <string>
#include <vector>

using namespace stp;

namespace
{

// The widest bit vector the exhaustive value sweeps go to, and the widths
// the circuit is checked at.
const unsigned MAX_WIDTH = 5;
const unsigned CIRCUIT_WIDTHS[2] = {3, 4};

// One fact, whichever operation it belongs to: what it claims of a triple,
// how narrow a bit vector it is still true of, and how to put it in front of
// a solver.
struct Fact
{
  std::string name;
  // Which widths the fact declares itself good for. A predicate rather than
  // a minimum because one fact is true at one bit, false at two and true
  // above, and a minimum cannot say that.
  std::function<bool(unsigned)> applicable;
  std::function<bool(const std::vector<bool>&, const std::vector<bool>&,
                     const std::vector<bool>&)>
      holds;
  std::function<void(BVExactEncoder&, SATSolver&, unsigned,
                     const std::vector<unsigned>&,
                     const std::vector<unsigned>&,
                     const std::vector<unsigned>&)>
      encode;
};

// SMT-LIB's bvudiv and bvurem, totalised the way the unabstracted circuit
// totalises them: division by zero is all ones, and the remainder over a
// zero divisor is the dividend.
unsigned referenceDiv(unsigned x, unsigned s, unsigned width)
{
  return (s == 0) ? ((1u << width) - 1) : (x / s);
}

unsigned referenceRem(unsigned x, unsigned s, unsigned /*width*/)
{
  return (s == 0) ? x : (x % s);
}

unsigned referenceMul(unsigned x, unsigned s, unsigned width)
{
  return (x * s) & ((1u << width) - 1);
}

unsigned referenceAdd(unsigned x, unsigned s, unsigned width)
{
  return (x + s) & ((1u << width) - 1);
}

struct Family
{
  const char* what;
  unsigned (*reference)(unsigned, unsigned, unsigned);
  std::vector<Fact> facts;
};

std::vector<Family> families()
{
  Family quotients{"BVDIV", referenceDiv, {}};
  unsigned count = 0;
  const DivLemma* divTable = divLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const DivLemma lemma = divTable[i];
    quotients.facts.push_back(
        {divLemmaName(lemma),
         [lemma](unsigned width) { return divLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t) {
           return divLemmaHolds(lemma, x, s, t);
         },
         [lemma](BVExactEncoder& enc, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& xv,
                 const std::vector<unsigned>& sv,
                 const std::vector<unsigned>& tv) {
           enc.encodeDivLemma(solver, lemma, width, xv, sv, tv);
         }});
  }

  Family remainders{"BVMOD", referenceRem, {}};
  const RemLemma* remTable = remLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const RemLemma lemma = remTable[i];
    remainders.facts.push_back(
        {remLemmaName(lemma),
         [lemma](unsigned width) { return remLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t) {
           return remLemmaHolds(lemma, x, s, t);
         },
         [lemma](BVExactEncoder& enc, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& xv,
                 const std::vector<unsigned>& sv,
                 const std::vector<unsigned>& tv) {
           enc.encodeRemLemma(solver, lemma, width, xv, sv, tv);
         }});
  }

  Family products{"BVMULT", referenceMul, {}};
  const MulLemma* mulTable = mulLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const MulLemma lemma = mulTable[i];
    products.facts.push_back(
        {mulLemmaName(lemma),
         [lemma](unsigned width) { return mulLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t) {
           return mulLemmaHolds(lemma, x, s, t);
         },
         [lemma](BVExactEncoder& enc, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& xv,
                 const std::vector<unsigned>& sv,
                 const std::vector<unsigned>& tv) {
           enc.encodeMulLemma(solver, lemma, width, xv, sv, tv);
         }});
  }

  Family sums{"BVPLUS", referenceAdd, {}};
  const AddLemma* addTable = addLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const AddLemma lemma = addTable[i];
    sums.facts.push_back(
        {addLemmaName(lemma),
         [lemma](unsigned width) { return addLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t) {
           return addLemmaHolds(lemma, x, s, t);
         },
         [lemma](BVExactEncoder& enc, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& xv,
                 const std::vector<unsigned>& sv,
                 const std::vector<unsigned>& tv) {
           // Both operands as written. The lowering that folds a two's
           // complement into one of them has its own regression; what is
           // checked here is the fact itself.
           enc.encodeAddLemma(solver, lemma, width, xv, sv, tv, false, false);
         }});
  }

  return {quotients, remainders, products, sums};
}

std::vector<bool> bitsOf(unsigned value, unsigned width)
{
  std::vector<bool> bits(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

class BVAbstractionLemmaTest : public ::testing::Test
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

  Circuit build(const Fact& fact, unsigned width)
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

    BVExactEncoder encoder(&mgr);
    fact.encode(encoder, *c.solver, width, xVars, sVars, tVars);

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

// Every fact is true of the operation itself, at every pair of operands and
// at every width it declares itself good for. This is the soundness claim:
// they are asserted unconditionally and never retracted. A product fact is
// written over an `x` and an `s` the operation does not distinguish, and
// sweeping every pair covers both readings of it for free.
TEST(BVAbstractionLemma, every_lemma_is_true_of_the_operation)
{
  for (const Family& family : families())
    for (const Fact& fact : family.facts)
      for (unsigned width = 1; width <= MAX_WIDTH; ++width)
      {
        if (!fact.applicable(width))
          continue;
        const unsigned values = 1u << width;
        for (unsigned x = 0; x < values; x++)
          for (unsigned s = 0; s < values; s++)
          {
            const unsigned t = family.reference(x, s, width);
            ASSERT_TRUE(fact.holds(bitsOf(x, width), bitsOf(s, width),
                                   bitsOf(t, width)))
                << family.what << " " << fact.name << " is false at " << width
                << " bits of x=" << x << " s=" << s << " (result " << t << ")";
          }
      }
}

// ... and a width a fact refuses is one it really is false at, not a margin
// someone rounded up. A refusal that is too broad costs a fact on narrow
// abstractions for nothing; one that is too narrow is unsoundness, and the
// sweep above -- which only looks at the widths a fact admits -- would not
// see it. Together the two tests pin the answer at every width from one to
// MAX_WIDTH in both directions.
TEST(BVAbstractionLemma, a_width_is_refused_exactly_where_the_fact_is_false)
{
  for (const Family& family : families())
    for (const Fact& fact : family.facts)
      for (unsigned width = 1; width <= MAX_WIDTH; ++width)
      {
        if (fact.applicable(width))
          continue;

        const unsigned values = 1u << width;
        bool broken = false;
        for (unsigned x = 0; x < values && !broken; x++)
          for (unsigned s = 0; s < values && !broken; s++)
            broken = !fact.holds(bitsOf(x, width), bitsOf(s, width),
                                 bitsOf(family.reference(x, s, width), width));

        EXPECT_TRUE(broken)
            << family.what << " " << fact.name << " refuses " << width
            << " bits but is true of the operation there";
      }
}

// Each fact rules something out. One true of every triple would be sound and
// useless: the refiner would spend a round on it and the search would be free
// to offer the same candidate again.
TEST(BVAbstractionLemma, every_lemma_rules_something_out)
{
  const unsigned width = 4;
  const unsigned values = 1u << width;
  for (const Family& family : families())
    for (const Fact& fact : family.facts)
    {
      unsigned refuted = 0;
      for (unsigned x = 0; x < values; x++)
        for (unsigned s = 0; s < values; s++)
          for (unsigned t = 0; t < values; t++)
            if (!fact.holds(bitsOf(x, width), bitsOf(s, width),
                            bitsOf(t, width)))
              refuted++;
      EXPECT_GT(refuted, 0u)
          << family.what << " " << fact.name << " excludes no triple";
    }
}

// The circuit that goes into the solver says what its predicate says --
// permitting exactly the triples the predicate calls true.
TEST_F(BVAbstractionLemmaTest, the_circuit_agrees_with_the_predicate)
{
  for (unsigned width : CIRCUIT_WIDTHS)
  {
    const unsigned values = 1u << width;
    for (const Family& family : families())
      for (const Fact& fact : family.facts)
      {
        if (!fact.applicable(width))
          continue;
        Circuit c = build(fact, width);
        for (unsigned x = 0; x < values; x++)
          for (unsigned s = 0; s < values; s++)
            for (unsigned t = 0; t < values; t++)
            {
              const bool want = fact.holds(bitsOf(x, width), bitsOf(s, width),
                                           bitsOf(t, width));
              ASSERT_EQ(want, permits(c, x, s, t))
                  << family.what << " " << fact.name << " at " << width
                  << " bits, x=" << x << " s=" << s << " t=" << t;
            }
      }
  }
}
