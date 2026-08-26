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

// One exhaustive harness for every imported arithmetic registry. It checks
// three independent claims: each value predicate is a theorem of the exact
// operation, every declared width restriction is necessary, and the circuit
// installed in the SAT solver accepts exactly the triples the predicate does.
// The tables come from the refiner itself, so adding a fact without adding a
// test case is impossible.
#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/ToSat/BVExactEncoder.h"

#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <gtest/gtest.h>

#include <functional>
#include <memory>
#include <set>
#include <string>
#include <vector>

using namespace stp;

static_assert(DivLemma::UdivRef9 == DivLemma::QuotientNotNegatedAnd,
              "legacy UDIV spelling changed value");
static_assert(RemLemma::UremRef2 == RemLemma::DividendZero,
              "legacy UREM spelling changed value");
static_assert(MulLemma::MulRef3 == MulLemma::FactorAndProductNotOr,
              "legacy MUL spelling changed value");

namespace
{

const unsigned MAX_WIDTH = 6;
const unsigned CIRCUIT_WIDTHS[] = {3, 4};

std::vector<bool> bitsOf(unsigned value, unsigned width)
{
  std::vector<bool> bits(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

struct Fact
{
  std::string name;
  std::function<bool(unsigned)> applicable;
  std::function<bool(const std::vector<bool>&, const std::vector<bool>&,
                     const std::vector<bool>&)>
      holds;
  std::function<void(BVExactEncoder&, SATSolver&, unsigned,
                     const std::vector<unsigned>&, const std::vector<unsigned>&,
                     const std::vector<unsigned>&)>
      encode;
};

unsigned referenceDiv(unsigned x, unsigned s, unsigned width)
{
  return s == 0 ? (1u << width) - 1 : x / s;
}

unsigned referenceRem(unsigned x, unsigned s, unsigned)
{
  return s == 0 ? x : x % s;
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
  const char* name;
  unsigned expectedCount;
  unsigned (*reference)(unsigned, unsigned, unsigned);
  std::vector<Fact> facts;
};

std::vector<Family> families()
{
  std::vector<Family> result;
  unsigned count = 0;

  Family div{"BVDIV", 33, referenceDiv, {}};
  const DivLemma* divTable = divLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const DivLemma lemma = divTable[i];
    div.facts.push_back(
        {divLemmaName(lemma),
         [lemma](unsigned width) { return divLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t)
         { return divLemmaHolds(lemma, x, s, t); },
         [lemma](BVExactEncoder& encoder, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& x, const std::vector<unsigned>& s,
                 const std::vector<unsigned>& t)
         { encoder.encodeDivLemma(solver, lemma, width, x, s, t); }});
  }
  result.push_back(div);

  Family rem{"BVMOD", 12, referenceRem, {}};
  const RemLemma* remTable = remLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const RemLemma lemma = remTable[i];
    rem.facts.push_back(
        {remLemmaName(lemma),
         [lemma](unsigned width) { return remLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t)
         { return remLemmaHolds(lemma, x, s, t); },
         [lemma](BVExactEncoder& encoder, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& x, const std::vector<unsigned>& s,
                 const std::vector<unsigned>& t)
         { encoder.encodeRemLemma(solver, lemma, width, x, s, t); }});
  }
  result.push_back(rem);

  Family mul{"BVMULT", 14, referenceMul, {}};
  const MulLemma* mulTable = mulLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const MulLemma lemma = mulTable[i];
    mul.facts.push_back(
        {mulLemmaName(lemma),
         [lemma](unsigned width) { return mulLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t)
         { return mulLemmaHolds(lemma, x, s, t); },
         [lemma](BVExactEncoder& encoder, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& x, const std::vector<unsigned>& s,
                 const std::vector<unsigned>& t)
         { encoder.encodeMulLemma(solver, lemma, width, x, s, t); }});
  }
  result.push_back(mul);

  Family add{"BVPLUS", 13, referenceAdd, {}};
  const AddLemma* addTable = addLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const AddLemma lemma = addTable[i];
    add.facts.push_back(
        {addLemmaName(lemma),
         [lemma](unsigned width) { return addLemmaApplicable(lemma, width); },
         [lemma](const std::vector<bool>& x, const std::vector<bool>& s,
                 const std::vector<bool>& t)
         { return addLemmaHolds(lemma, x, s, t); },
         [lemma](BVExactEncoder& encoder, SATSolver& solver, unsigned width,
                 const std::vector<unsigned>& x, const std::vector<unsigned>& s,
                 const std::vector<unsigned>& t)
         { encoder.encodeAddLemma(solver, lemma, width, x, s, t); }});
  }
  result.push_back(add);

  return result;
}

class BVAbstractionLemmaTest : public ::testing::Test
{
protected:
  STPMgr mgr;

  struct Circuit
  {
    std::unique_ptr<SATSolver> solver;
    std::vector<unsigned> vars;
    unsigned width = 0;
  };

  Circuit build(const Fact& fact, unsigned width)
  {
    Circuit circuit;
    circuit.width = width;
    circuit.solver.reset(createSATSolver(mgr.UserFlags));
    EXPECT_TRUE(circuit.solver != NULL) << "no SAT backend was compiled in";
    EXPECT_TRUE(circuit.solver->supportsAssumptions());

    std::vector<unsigned> x(width), s(width), t(width);
    std::vector<unsigned>* groups[] = {&x, &s, &t};
    for (unsigned group = 0; group < 3; ++group)
      for (unsigned bit = 0; bit < width; ++bit)
      {
        (*groups[group])[bit] = circuit.solver->newVar();
        circuit.solver->setFrozen((*groups[group])[bit]);
      }

    BVExactEncoder encoder(&mgr);
    fact.encode(encoder, *circuit.solver, width, x, s, t);
    for (unsigned group = 0; group < 3; ++group)
      circuit.vars.insert(circuit.vars.end(), groups[group]->begin(),
                          groups[group]->end());
    return circuit;
  }

  bool permits(Circuit& circuit, unsigned x, unsigned s, unsigned t)
  {
    SATSolver::vec_literals assumptions;
    const unsigned values[] = {x, s, t};
    for (unsigned group = 0; group < 3; ++group)
      for (unsigned bit = 0; bit < circuit.width; ++bit)
        assumptions.push(
            SATSolver::mkLit(circuit.vars[group * circuit.width + bit],
                             ((values[group] >> bit) & 1u) == 0));

    bool timedOut = false;
    const bool sat =
        circuit.solver->solveWithAssumptions(assumptions, timedOut);
    EXPECT_FALSE(timedOut);
    return sat;
  }
};

} // namespace

TEST(BVAbstractionLemma, registries_have_complete_unique_metadata)
{
  for (const Family& family : families())
  {
    EXPECT_EQ(family.expectedCount, family.facts.size()) << family.name;
    std::set<std::string> names;
    for (const Fact& fact : family.facts)
    {
      EXPECT_FALSE(fact.name.empty()) << family.name;
      EXPECT_NE("unknown", fact.name) << family.name;
      EXPECT_TRUE(names.insert(fact.name).second)
          << family.name << " has duplicate name " << fact.name;
    }
  }
}

TEST(BVAbstractionLemma, every_fact_is_true_of_its_operation)
{
  for (const Family& family : families())
    for (const Fact& fact : family.facts)
      for (unsigned width = 1; width <= MAX_WIDTH; ++width)
      {
        if (!fact.applicable(width))
          continue;
        const unsigned values = 1u << width;
        for (unsigned x = 0; x < values; ++x)
          for (unsigned s = 0; s < values; ++s)
          {
            const unsigned t = family.reference(x, s, width);
            ASSERT_TRUE(fact.holds(bitsOf(x, width), bitsOf(s, width),
                                   bitsOf(t, width)))
                << family.name << " " << fact.name << " at width " << width
                << ", x=" << x << " s=" << s << " result=" << t;
          }
      }
}

TEST(BVAbstractionLemma, every_refused_width_has_a_real_counterexample)
{
  for (const Family& family : families())
    for (const Fact& fact : family.facts)
      for (unsigned width = 1; width <= MAX_WIDTH; ++width)
      {
        if (fact.applicable(width))
          continue;
        const unsigned values = 1u << width;
        bool broken = false;
        for (unsigned x = 0; x < values && !broken; ++x)
          for (unsigned s = 0; s < values && !broken; ++s)
          {
            const unsigned t = family.reference(x, s, width);
            broken = !fact.holds(bitsOf(x, width), bitsOf(s, width),
                                 bitsOf(t, width));
          }
        EXPECT_TRUE(broken) << family.name << " " << fact.name
                            << " needlessly refuses width " << width;
      }
}

TEST(BVAbstractionLemma, every_fact_rules_out_a_candidate)
{
  const unsigned width = 4;
  const unsigned values = 1u << width;
  for (const Family& family : families())
    for (const Fact& fact : family.facts)
    {
      unsigned refuted = 0;
      for (unsigned x = 0; x < values; ++x)
        for (unsigned s = 0; s < values; ++s)
          for (unsigned t = 0; t < values; ++t)
            if (!fact.holds(bitsOf(x, width), bitsOf(s, width),
                            bitsOf(t, width)))
              ++refuted;
      EXPECT_GT(refuted, 0u)
          << family.name << " " << fact.name << " excludes no triple";
    }
}

TEST_F(BVAbstractionLemmaTest, every_circuit_matches_its_value_predicate)
{
  for (const unsigned width : CIRCUIT_WIDTHS)
  {
    const unsigned values = 1u << width;
    for (const Family& family : families())
      for (const Fact& fact : family.facts)
      {
        if (!fact.applicable(width))
          continue;
        Circuit circuit = build(fact, width);
        for (unsigned x = 0; x < values; ++x)
          for (unsigned s = 0; s < values; ++s)
            for (unsigned t = 0; t < values; ++t)
            {
              const bool expected = fact.holds(
                  bitsOf(x, width), bitsOf(s, width), bitsOf(t, width));
              ASSERT_EQ(expected, permits(circuit, x, s, t))
                  << family.name << " " << fact.name << " at width " << width
                  << ", x=" << x << " s=" << s << " t=" << t;
            }
      }
  }
}
