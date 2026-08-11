// The array-refinement axiom memo.
//
// getEquals mints a FRESH comparison circuit on every call -- a variable per
// index bit plus the clauses tying it to the operands -- so a refinement round
// that re-derives a pair the solver already constrains does not submit a
// duplicate clause. It submits an entirely new circuit encoding a constraint
// that is already there, and no clause- or variable-based progress measure can
// tell that apart from real work. That is why the loop's no-progress guard
// could never fire, and why the memo exists.
//
// These tests exist because nothing else can reach it: no file in the query
// corpus produces a repeated derivation, so the memo's hit path is dead to the
// suite. Its failure mode is a dropped congruence axiom -- an unsat query
// answering sat -- so it is tested here directly instead.
#include "stp/AbsRefineCounterExample/AxiomMemo.h"
#include "stp/STPManager/STPManager.h"
#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif
#include <gtest/gtest.h>

using namespace stp;

#ifdef USE_CADICAL

namespace
{
struct Fixture
{
  STPMgr mgr;
  ASTNode i0, i1, v0, v1;
  ToSATBase::ASTNodeToSATVar satVar;

  Fixture()
  {
    STPMgr* bm = &mgr;
    i0 = bm->CreateSymbol("i0", 0, 8);
    i1 = bm->CreateSymbol("i1", 0, 8);
    v0 = bm->CreateSymbol("v0", 0, 8);
    v1 = bm->CreateSymbol("v1", 0, 8);
  }

  // Give every leaf a real variable vector, as a solve with all four blasted
  // would. Without this getSatVariables mints throwaway variables instead.
  void mapAll(SATSolver& s)
  {
    const ASTNode* leaves[4] = {&i0, &i1, &v0, &v1};
    for (int k = 0; k < 4; k++)
    {
      std::vector<unsigned> bits;
      for (unsigned b = 0; b < 8; b++)
        bits.push_back(s.newVar());
      satVar[*leaves[k]] = bits;
    }
  }

  std::vector<AxiomToBe> one()
  {
    std::vector<AxiomToBe> v;
    v.push_back(AxiomToBe(i0, i1, v0, v1));
    return v;
  }
};
} // namespace

// The point of the whole thing: the same axiom, twice, against one solver.
TEST(AxiomMemo, ASecondEmissionOfTheSameAxiomIsSuppressed)
{
  Fixture f;
  Cadical s;
  f.mapAll(s);

  std::vector<AxiomToBe> a = f.one();
  EXPECT_EQ(1u, applyAxiomsToSolver(f.satVar, a, s));
  const uint64_t after_first = s.submittedClauses();
  EXPECT_GT(after_first, 0u);

  std::vector<AxiomToBe> b = f.one();
  EXPECT_EQ(0u, applyAxiomsToSolver(f.satVar, b, s));
  // and nothing reached the solver: no circuit, no clause
  EXPECT_EQ(after_first, s.submittedClauses());
}

// A different axiom is not suppressed by a similar one. Swapping ONE pair
// denotes a different congruence, so it must still be emitted.
TEST(AxiomMemo, ADifferentAxiomIsStillEmitted)
{
  Fixture f;
  Cadical s;
  f.mapAll(s);

  std::vector<AxiomToBe> a = f.one();
  EXPECT_EQ(1u, applyAxiomsToSolver(f.satVar, a, s));

  std::vector<AxiomToBe> b;
  b.push_back(AxiomToBe(f.i1, f.i0, f.v0, f.v1)); // index pair swapped only
  const uint64_t before = s.submittedClauses();
  EXPECT_EQ(1u, applyAxiomsToSolver(f.satVar, b, s));
  EXPECT_GT(s.submittedClauses(), before);
}

// The safety property. The node->variable map is rebuilt per solve and omits
// symbols the driver eliminated for THAT solve; a leaf can therefore be absent
// once (its axiom landing on throwaway variables) and present later with real
// ones. A memo that only remembered "emitted" would suppress the real axiom in
// favour of the vacuous one, dropping a congruence. It must re-emit instead.
TEST(AxiomMemo, AChangedVariableMappingForcesReEmission)
{
  Fixture f;
  Cadical s;
  f.mapAll(s);

  std::vector<AxiomToBe> a = f.one();
  EXPECT_EQ(1u, applyAxiomsToSolver(f.satVar, a, s));

  // the same leaf, now mapped to different variables
  std::vector<unsigned> rebound;
  for (unsigned b = 0; b < 8; b++)
    rebound.push_back(s.newVar());
  f.satVar[f.v1] = rebound;

  std::vector<AxiomToBe> b = f.one();
  const uint64_t before = s.submittedClauses();
  EXPECT_EQ(1u, applyAxiomsToSolver(f.satVar, b, s));
  EXPECT_GT(s.submittedClauses(), before);
}

// Lifetime: the memo belongs to the solver, so a new solver has never been
// told anything. This is what makes skipping sound at all -- a clause set only
// goes away by destroying the solver.
TEST(AxiomMemo, AFreshSolverHasBeenToldNothing)
{
  Fixture f;
  {
    Cadical first;
    f.mapAll(first);
    std::vector<AxiomToBe> a = f.one();
    EXPECT_EQ(1u, applyAxiomsToSolver(f.satVar, a, first));
    std::vector<AxiomToBe> b = f.one();
    EXPECT_EQ(0u, applyAxiomsToSolver(f.satVar, b, first));
  }

  Cadical second;
  f.satVar.clear();
  f.mapAll(second);
  std::vector<AxiomToBe> c = f.one();
  EXPECT_EQ(1u, applyAxiomsToSolver(f.satVar, c, second));
  EXPECT_GT(second.submittedClauses(), 0u);
}

#endif // USE_CADICAL
