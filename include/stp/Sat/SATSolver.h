/********************************************************************
 * AUTHORS: Trevor Hansen, Andrew V. Jones
 *
 * BEGIN DATE: Aug, 2010
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

#ifndef SATSOLVER_H_
#define SATSOLVER_H_

#include "SearchBias.h"
#include "minisat/core/SolverTypes.h"
#include "minisat/mtl/Vec.h"
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

// Don't let the defines escape outside.

namespace stp
{
class SATSolver
{
private:
  SATSolver(const SATSolver&);      // no copy
  void operator=(const SATSolver&); // no assign.

public:
  SATSolver() {}

  virtual ~SATSolver() {}

  class vec_literals : public Minisat::vec<Minisat::Lit>
  {
  };

  virtual bool addClause(
      const SATSolver::vec_literals& ps) = 0; // Add a clause to the solver.

  virtual bool okay() const = 0; // FALSE means solver is in a conflicting state

  // Search without assumptions.
  //
  // Not virtual: this enforces the parts of the resource budget that do not
  // depend on the backend, then delegates to solveInternal(). Backends
  // override solveInternal(), not this.
  bool solve(bool& timeout_expired)
  {
    // The budget can already be spent before we ever reach the solver, either
    // because the caller asked for a zero budget or because an earlier
    // refinement iteration used it all up. Don't rely on the backend noticing:
    // a solver that cannot be interrupted mid-search would run to completion,
    // and even one that can only notices when it next polls.
    if (timeLimitExpired())
    {
      timeout_expired = true;
      return false;
    }

    return solveInternal(timeout_expired);
  }

  // Search under assumption literals: each is treated as a unit clause for
  // this call only, and leaves no trace afterwards. This is what makes the
  // solver reusable across (check-sat) calls -- retractable assertions are
  // assumed rather than added. Budget enforcement as in solve().
  //
  // Only meaningful when supportsAssumptions(); the incremental driver
  // selects a backend on that basis.
  bool solveWithAssumptions(const vec_literals& assumps, bool& timeout_expired)
  {
    if (timeLimitExpired())
    {
      timeout_expired = true;
      return false;
    }

    return solveWithAssumptionsInternal(assumps, timeout_expired);
  }

  virtual bool supportsAssumptions() const { return false; }

  typedef uint8_t lbool;

  static inline Minisat::Lit mkLit(uint32_t var, bool sign)
  {
    Minisat::Lit p;
    p.x = var + var + (int)sign;
    return p;
  }

  // Ask the backend to tune its search towards satisfiable or unsatisfiable
  // instances. Only ever called before the first clause is added, because a
  // backend may only accept configuration while it is still empty.
  //
  // FALSE means this backend has nothing corresponding to the requested bias.
  // That isn't an error: the bias is a hint about the workload, and a backend
  // that ignores it is slower rather than wrong.
  virtual bool setSearchBias(SearchBias /*bias*/) { return false; }

  // Ask the backend to turn on bounded variable addition (BVA, CaDiCaL's
  // "factor"). Like setSearchBias this is only ever called before the first
  // clause is added, and FALSE means the backend has no such technique to
  // enable -- a performance hint declined, not an error.
  virtual bool enableBVA() { return false; }

  // Ask the backend to reuse the solver trail across incremental solve
  // calls when consecutive assumption sequences share a prefix, instead of
  // re-deciding and re-propagating from the root every call (CaDiCaL's
  // incremental lazy backtracking). Only correct to rely on when the
  // caller keeps its assumption order prefix-stable across calls, which
  // the incremental driver does: assumptions are emitted in assertion
  // stack order and push/pop only ever change the suffix. FALSE means the
  // backend has no such mechanism -- a performance hint declined, not an
  // error.
  virtual bool enableTrailReuse() { return false; }

  // Whether this backend can turn probe-based inprocessing off, and the
  // switch itself. disableInprobing() is only ever called before the
  // first clause is added (backends may only accept configuration while
  // empty); the capability query is free of that restriction, so a
  // caller can decide about a LIVE solver and apply the choice to the
  // fresh one a rebuild constructs. FALSE from the query means the
  // backend has no such technique to control -- a performance hint
  // declined, not an error.
  virtual bool supportsInprobingControl() const { return false; }
  virtual bool disableInprobing() { return false; }

  // The rest of the recurring-inprocessing retirement, applied alongside
  // disableInprobing under the same configuration-window rule: bounded
  // variable elimination re-eliminates restored variables every solve on
  // a persistent solver whose content churns (retractable encodings
  // mention eliminated variables and CaDiCaL restores them on contact),
  // and learned-clause shrinking taxes every conflict of a many-solve
  // session. Both measured as steady per-solve losses on the sessions
  // that retire inprobing, and their removal composes with it.
  virtual bool disableEliminationAndShrinking() { return false; }

  // Turn off the backend's lucky-phase probing, which re-tries trivial
  // whole-assignment patterns over the entire clause database at every
  // solve call. Worth its price once per formula; on a persistent
  // many-solve solver it is a recurring tax. Configuration-window-only,
  // like the rest; FALSE means nothing to turn off.
  virtual bool disableLuckyPhases() { return false; }

  // After solveWithAssumptions returned false: the subset of the assumed
  // literals that the refutation actually used, in the same 2*var+sign
  // encoding they were passed in. Any superset of a genuine core is a
  // correct answer -- the full assumption set always is one, and that is
  // the default for backends without the query. Only meaningful
  // immediately after an unsatisfiable assumption solve, before anything
  // else touches the solver.
  virtual void unsatAssumptions(const vec_literals& assumps,
                                std::vector<int>& out)
  {
    out.clear();
    for (int i = 0; i < assumps.size(); i++)
      out.push_back(assumps[i].x);
  }

  // Suggest the value the decision heuristic should try first for a
  // variable. Pure search advice: it cannot change any verdict, only
  // which model is found first. The incremental driver uses it to steer
  // the search away from retracted content -- a popped level's
  // activation variable is unconstrained, and a backend whose default
  // phase is positive would otherwise keep dragging the dead level's
  // cone into the search. Backends without a cheap phase interface
  // ignore it.
  virtual void suggestPhase(uint32_t var, bool value)
  {
    (void)var;
    (void)value;
  }

  // ---------------------------------------------------------------------
  // Resource budgets.
  //
  // STP spells "no limit" as -1, and that case is filtered out by the
  // caller, so these are only ever called with a value >= 0. A value of 0
  // therefore means what it says: a budget of zero, i.e. give up without
  // searching. It does not mean "unlimited".
  // ---------------------------------------------------------------------

  virtual void setMaxConflicts(int64_t /*max_confl*/)
  {
    std::cerr
        << "Warning: Max conflict setting is not supported by this SAT solver"
        << std::endl;
  }

  // The time budget belongs to the whole query, not to one solve() call.
  // STP calls solve() once per abstraction-refinement iteration, so a budget
  // re-armed per call would let a query run for an unbounded multiple of it.
  // The deadline is computed once, here, and every backend measures against
  // it; that also makes a budget of 0 fall out for free, as a deadline in the
  // past.
  //
  // Backends that can be interrupted mid-search should override
  // canInterruptSearch() and consult secondsRemaining() / timeLimitExpired().
  // For the rest, solve() still enforces the deadline between calls.
  virtual void setMaxTime(int64_t max_time) // seconds
  {
    assert(max_time >= 0);

    deadline = std::chrono::steady_clock::now() +
               std::chrono::seconds(max_time);
    deadline_set = true;

    if (!canInterruptSearch())
    {
      std::cerr << "Warning: this SAT solver cannot be interrupted during "
                   "search; the time limit is only enforced between solver "
                   "calls"
                << std::endl;
    }
  }

  bool hasTimeLimit() const { return deadline_set; }

  // TRUE once the query's time budget is gone. Always FALSE when no time
  // limit has been set.
  bool timeLimitExpired() const
  {
    return deadline_set && std::chrono::steady_clock::now() >= deadline;
  }

  // Time left on the query's budget, in seconds; never negative. Only
  // meaningful when hasTimeLimit(). Backends that take a duration rather
  // than a deadline should pass this on each solve, so that what remains
  // shrinks across refinement iterations instead of being re-armed.
  double secondsRemaining() const
  {
    assert(deadline_set);

    const std::chrono::duration<double> remaining =
        deadline - std::chrono::steady_clock::now();

    return remaining.count() > 0.0 ? remaining.count() : 0.0;
  }

  virtual uint8_t modelValue(uint32_t x) const = 0;

  virtual uint32_t newVar() = 0;

  virtual unsigned long nVars() const = 0;

  virtual void printStats() const = 0;

  virtual void setVerbosity(int v) = 0;

  virtual lbool true_literal() const = 0;
  virtual lbool false_literal() const = 0;
  virtual lbool undef_literal() const = 0;

  // The simplifying solvers shouldn't eliminate index / value variables.
  virtual void setFrozen(uint32_t /*var*/) {}

  virtual void enableRefinement(const bool /*enable*/) {}

  virtual int nClauses()
  {
    std::cerr << "Not yet implemented.";
    exit(1);
  }

  virtual bool simplify()
  {
    std::cerr << "Not yet implemented.";
    exit(1);
  }

protected:
  // Search without assumptions, having already been given a non-empty share
  // of whatever budget was configured. Implemented by each backend.
  virtual bool solveInternal(bool& timeout_expired) = 0;

  // Search under assumptions. Backends that return true from
  // supportsAssumptions() override this; the default must be unreachable.
  virtual bool solveWithAssumptionsInternal(const vec_literals& /*assumps*/,
                                            bool& /*timeout_expired*/)
  {
    std::cerr << "ERROR: this SAT backend does not support assumptions"
              << std::endl;
    exit(-1);
  }

  // TRUE if the backend can abandon a search that is already running, either
  // through a callback or through a limit of its own. Backends that cannot
  // get a time limit enforced only between solve() calls.
  virtual bool canInterruptSearch() const { return false; }

private:
  std::chrono::steady_clock::time_point deadline;
  bool deadline_set = false;
};
}
#endif
