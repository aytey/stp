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

namespace
{

const unsigned MAX_WIDTH = 6;
const unsigned CIRCUIT_WIDTHS[] = {3, 4};

// Widths the circuit and the predicate are compared at by sampling rather
// than exhaustively. Four bits is not a wide enough net on its own: the
// barrel shifters inside these circuits gain a stage at five bits and
// another at nine, and every adder and comparator in them widens with the
// operands, so a circuit that stopped agreeing with its predicate above four
// bits would go unnoticed. Exhaustive is out of reach up here -- twelve bits
// is 2^36 triples -- and unnecessary: what has to be exercised is the
// structure, and the structure repeats.
const unsigned SAMPLED_CIRCUIT_WIDTHS[] = {5, 9, 12};
const unsigned SAMPLES_PER_FACT = 400;

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

  Family div{"BVDIV", BV_DIV_LEMMA_COUNT, referenceDiv, {}};
  const BVLemmaEntry<DivLemma>* divTable = divLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const DivLemma lemma = divTable[i].lemma;
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

  Family rem{"BVMOD", BV_REM_LEMMA_COUNT, referenceRem, {}};
  const BVLemmaEntry<RemLemma>* remTable = remLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const RemLemma lemma = remTable[i].lemma;
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

  Family mul{"BVMULT", BV_MUL_LEMMA_COUNT, referenceMul, {}};
  const BVLemmaEntry<MulLemma>* mulTable = mulLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const MulLemma lemma = mulTable[i].lemma;
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

  Family add{"BVPLUS", BV_ADD_LEMMA_COUNT, referenceAdd, {}};
  const BVLemmaEntry<AddLemma>* addTable = addLemmaTable(count);
  for (unsigned i = 0; i < count; ++i)
  {
    const AddLemma lemma = addTable[i].lemma;
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

TEST(BVAbstractionLemma, custom_facts_have_the_ranked_registry_positions)
{
  unsigned count = 0;
  const BVLemmaEntry<DivLemma>* div = divLemmaTable(count);
  ASSERT_EQ(BV_DIV_LEMMA_COUNT, count);
  EXPECT_EQ(DivLemma::QuotientIsOne, div[3].lemma);

  const BVLemmaEntry<RemLemma>* rem = remLemmaTable(count);
  ASSERT_EQ(BV_REM_LEMMA_COUNT, count);
  EXPECT_EQ(RemLemma::RemainderIsDifference, rem[3].lemma);

  const BVLemmaEntry<MulLemma>* mul = mulLemmaTable(count);
  ASSERT_EQ(BV_MUL_LEMMA_COUNT, count);
  EXPECT_EQ(MulLemma::FactorUnchangedByMaskedShift, mul[0].lemma);
  EXPECT_EQ(MulLemma::FactorAndProductNotOr, mul[1].lemma);
}

TEST(BVAbstractionLemma, descriptive_tail_names_keep_the_actual_source_ids)
{
  struct DivName
  {
    DivLemma lemma;
    const char* name;
  };
  const DivName divNames[] = {
      {DivLemma::UdivRef10, "divisor-or-quotient-not-masked-dividend"},
      {DivLemma::UdivRef11, "divisor-or-one-not-dividend-without-quotient"},
      {DivLemma::UdivRef20,
       "divisor-not-negated-self-shifted-by-half-quotient"},
      {DivLemma::UdivRef21, "dividend-not-negated-and-doubled-quotient"},
      {DivLemma::UdivRef23,
       "quotient-above-doubled-dividend-shifted-by-divisor"},
      {DivLemma::UdivRef24,
       "dividend-above-divisor-shifted-by-negated-or"},
      {DivLemma::UdivRef25,
       "dividend-above-quotient-shifted-by-negated-or"},
      {DivLemma::UdivRef28,
       "dividend-above-divisor-shifted-by-negated-xor"},
      {DivLemma::UdivRef29,
       "dividend-above-quotient-shifted-by-negated-xor"},
      {DivLemma::UdivRef30, "dividend-not-quotient-plus-divisor-or-sum"},
      {DivLemma::UdivRef31,
       "dividend-not-quotient-plus-one-plus-shifted-one"},
      {DivLemma::UdivRef32, "divisor-above-sum-shifted-by-quotient"},
      {DivLemma::UdivRef34, "divisor-xor-or-above-quotient-xor-one"},
      {DivLemma::UdivRef36,
       "quotient-above-dividend-shifted-by-divisor-less-one"},
      {DivLemma::UdivRef38, "dividend-not-one-less-shifted-dividend"}};
  for (const DivName& item : divNames)
    EXPECT_STREQ(item.name, divLemmaName(item.lemma));

  struct MulName
  {
    MulLemma lemma;
    const char* name;
  };
  const MulName mulNames[] = {
      {MulLemma::MulRef1, "factor-not-negated-product-or-low-bit"},
      {MulLemma::MulRefN3,
       "product-not-odd-factor-shifted-by-shifted-product"},
      {MulLemma::MulRefN5, "product-above-masked-shifted-factors"},
      {MulLemma::MulRefN6, "factor-not-one-xor-factor-shifted-by-xor"},
      {MulLemma::MulRef14, "product-not-one-or-negated-xor"},
      {MulLemma::MulRef15, "product-not-high-ones-or-xor"},
      {MulLemma::MulRefN9, "factor-not-shifted-factor-less-one"},
      {MulLemma::MulRef18, "factor-not-one-less-shifted-factor"},
      {MulLemma::MulRefN11, "factor-not-one-plus-shifted-factor"},
      {MulLemma::MulRefN12,
       "factor-not-one-less-shifted-factor-reversed"},
      {MulLemma::MulRefN13,
       "factor-not-one-plus-shifted-factor-reversed"},
      {MulLemma::MulRef13, "product-not-one-or-sum"},
      {MulLemma::MulRef12, "factor-not-negated-shifted-factor"}};
  for (const MulName& item : mulNames)
    EXPECT_STREQ(item.name, mulLemmaName(item.lemma));
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

// The values a sampled comparison draws from.
//
// Uniformly random operands would prove very little: almost every fact here
// is an implication, and almost every random triple leaves the premise false
// and the fact vacuously true. Zero, one, the all-ones word, each power of
// two and its neighbours are what turn those premises on, so the pool is
// those first and random words after.
std::vector<unsigned> samplePool(unsigned width, unsigned count)
{
  const unsigned mask = (1u << width) - 1;
  std::vector<unsigned> pool;
  pool.push_back(0);
  pool.push_back(1);
  pool.push_back(2);
  pool.push_back(3);
  pool.push_back(mask);
  pool.push_back(mask - 1);
  for (unsigned k = 0; k < width; ++k)
  {
    pool.push_back(1u << k);          // 2^k
    pool.push_back((1u << k) - 1);    // the mask below it
    pool.push_back((~(1u << k)) & mask);  // its complement
    pool.push_back(((~(1u << k)) + 1) & mask); // -2^k
  }

  // A fixed generator, so a failure is reproducible and a green run is not
  // green by luck of the day.
  unsigned state = 0x9e3779b9u ^ (width * 2654435761u);
  while (pool.size() < count)
  {
    state = state * 1664525u + 1013904223u;
    pool.push_back((state >> 8) & mask);
  }
  return pool;
}

TEST_F(BVAbstractionLemmaTest, every_circuit_agrees_with_its_predicate_when_sampled_wide)
{
  for (const unsigned width : SAMPLED_CIRCUIT_WIDTHS)
  {
    const std::vector<unsigned> pool = samplePool(width, SAMPLES_PER_FACT);
    for (const Family& family : families())
      for (const Fact& fact : family.facts)
      {
        if (!fact.applicable(width))
          continue;
        Circuit circuit = build(fact, width);
        for (unsigned i = 0; i < SAMPLES_PER_FACT; ++i)
        {
          // Rotate the three positions independently so the same value does
          // not sit in all three on every draw.
          const unsigned x = pool[i % pool.size()];
          const unsigned s = pool[(i * 7 + 3) % pool.size()];
          // Every third triple gets the operation's real answer, which is
          // where the implications with a determined conclusion live.
          const unsigned t = (i % 3 == 0) ? family.reference(x, s, width)
                                          : pool[(i * 13 + 5) % pool.size()];
          const bool expected =
              fact.holds(bitsOf(x, width), bitsOf(s, width), bitsOf(t, width));
          ASSERT_EQ(expected, permits(circuit, x, s, t))
              << family.name << " " << fact.name << " at width " << width
              << ", x=" << x << " s=" << s << " t=" << t;
        }
      }
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
