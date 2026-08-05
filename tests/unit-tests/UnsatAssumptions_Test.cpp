// Guards unsatAssumptions, the wrapper query behind get-unsat-assumptions
// and the core-aware verdict cache. The contract: after an unsat
// assumption solve it returns a subset of the assumed literals that is
// itself unsatisfiable with the clauses -- any superset of a genuine core
// qualifies, so the assertions accept supersets but insist the culprit is
// present and that irrelevant assumptions are droppable: solving again
// without the reported literals' complement must stay consistent.
#include "stp/Sat/MinisatCore.h"
#include "stp/Sat/SATSolver.h"
#include <algorithm>
#include <gtest/gtest.h>
#include <vector>

#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif

using stp::SATSolver;

namespace
{

// Three assumptions over a unit-contradicted variable: only the middle
// one can ever be in a genuine core.
template <class Backend> void culpritIsReported()
{
  Backend s;
  bool timed_out = false;
  const uint32_t a = s.newVar();
  const uint32_t b = s.newVar();
  const uint32_t c = s.newVar();

  SATSolver::vec_literals unit;
  unit.push(SATSolver::mkLit(b, true)); // (~b)
  s.addClause(unit);

  SATSolver::vec_literals assumps;
  assumps.push(SATSolver::mkLit(a, false));
  assumps.push(SATSolver::mkLit(b, false)); // contradicts the unit
  assumps.push(SATSolver::mkLit(c, false));
  ASSERT_FALSE(s.solveWithAssumptions(assumps, timed_out));

  std::vector<int> failed;
  s.unsatAssumptions(assumps, failed);

  const int culprit = SATSolver::mkLit(b, false).x;
  EXPECT_TRUE(std::find(failed.begin(), failed.end(), culprit) !=
              failed.end());
  // Every reported literal is one of the assumptions.
  for (const int lit : failed)
  {
    bool known = false;
    for (int i = 0; i < assumps.size(); i++)
      known |= assumps[i].x == lit;
    EXPECT_TRUE(known);
  }
  // Dropping the culprit leaves a satisfiable assumption set.
  SATSolver::vec_literals rest;
  rest.push(SATSolver::mkLit(a, false));
  rest.push(SATSolver::mkLit(c, false));
  EXPECT_TRUE(s.solveWithAssumptions(rest, timed_out));
}

} // namespace

TEST(UnsatAssumptions, MinisatReportsCulprit)
{
  culpritIsReported<stp::MinisatCore>();
}

#ifdef USE_CADICAL
TEST(UnsatAssumptions, CadicalReportsCulprit)
{
  culpritIsReported<stp::Cadical>();
}

// With factor on, failed() must be queried through the same translation
// the assumptions travelled through.
TEST(UnsatAssumptions, CadicalReportsCulpritUnderFactor)
{
  stp::Cadical s;
  s.enableBVA();
  bool timed_out = false;
  const uint32_t a = s.newVar();
  const uint32_t b = s.newVar();
  SATSolver::vec_literals unit;
  unit.push(SATSolver::mkLit(b, true));
  s.addClause(unit);

  SATSolver::vec_literals assumps;
  assumps.push(SATSolver::mkLit(a, false));
  assumps.push(SATSolver::mkLit(b, false));
  ASSERT_FALSE(s.solveWithAssumptions(assumps, timed_out));

  std::vector<int> failed;
  s.unsatAssumptions(assumps, failed);
  EXPECT_TRUE(std::find(failed.begin(), failed.end(),
                        SATSolver::mkLit(b, false).x) != failed.end());
}
#endif
