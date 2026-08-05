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

#ifndef INCREMENTALSOLVER_H_
#define INCREMENTALSOLVER_H_

#include "stp/AST/AST.h"
#include "stp/Globals/Globals.h"
#include <memory>

// The incremental solving driver; docs/incremental-solving.rst tells the
// full story.
//
// One SAT solver, one AIG, and one CNF encoding live for the whole session.
// Everything encoded is a conservative extension -- fresh Tseitin variables
// and definitional clauses -- so it stays valid forever; what changes between
// check-sats is only which root literals are asserted. A base-level (level 0)
// conjunct becomes a permanent unit clause; a conjunct at any pushed level
// has its root literal *assumed* per solve, so a pop retracts it by simply
// not assuming it any more. Learned clauses therefore survive both check-sats
// and pops by construction.
//
// The whole input language is covered -- plain bit-vectors, arrays (lazy
// refinement or --ackermanize), floating point, and --array-equality --
// canHandle() below is the seam should a future construct need excluding.

namespace stp
{

class STPMgr;
class AbsRefine_CounterExample;
class Simplifier;
class ArrayTransformer;

class IncrementalSolver
{
public:
  // `batchSimp` and `batchAT` are the batch pipeline's Simplifier and
  // ArrayTransformer -- the objects `ce` reads eliminated-variable
  // definitions and array read records from when it builds and checks
  // models. The driver seeds them from its own persistent stores
  // just-in-time (its substitutions at model construction, its read
  // registry around array work); the batch pipeline always clears both
  // (resetSolver) before using them itself.
  IncrementalSolver(STPMgr* bm, AbsRefine_CounterExample* ce,
                    Simplifier* batchSimp, ArrayTransformer* batchAT);
  ~IncrementalSolver();

  IncrementalSolver(const IncrementalSolver&) = delete;
  IncrementalSolver& operator=(const IncrementalSolver&) = delete;

  // Whether every assertion currently on the stack is inside the fragment
  // this driver encodes. Verdicts are cached per assertion node.
  // `assertionsSMT2` is what Cpp_interface::checkSat receives: one
  // conjunction per assertion level, base level first.
  bool canHandle(const ASTVec& assertionsSMT2);

  // Solve the current stack: encode what is new, assume what is retractable,
  // and leave everything else in place for the next call. On sat, the
  // counterexample tables are populated exactly as the batch path would.
  //
  // With `assumeLastLevelPerConjunct` the LAST level's conjuncts are
  // assumed one root literal each instead of grouped under an activation
  // literal -- check-sat-assuming passes its assumptions as that level and
  // wants per-assumption failure granularity for get-unsat-assumptions.
  //
  // The driver holds no per-level state: the assumption set is recomputed
  // from `assertionsSMT2` on every call (against permanent encoding caches),
  // so push and pop need no hooks here -- the parser's assertion stack is
  // the single source of truth. Base-level conjuncts become permanent unit
  // clauses, which is sound because the base level only ever grows; it is
  // destroyed only by reset/reset-assertions, which destroy this object.
  SOLVER_RETURN_TYPE checkSat(const ASTVec& assertionsSMT2,
                              bool assumeLastLevelPerConjunct = false);

  // The unsat story of the most recent checkSat, valid until the next one.
  // hasAssumptionGranularity: the last level was assumed per conjunct and
  // the backend reported which assumptions failed -- then
  // lastUnsatAssumptionConjuncts() is the (possibly empty: the
  // unsatisfiability may not need the assumptions at all) subset of that
  // level's conjuncts in the core. Without granularity a caller must fall
  // back to reporting every assumption, which is always a correct core.
  // lastUnsatCoreLevels() is the set of pushed-level indices (into the
  // checkSat argument vector) whose assumed literals the refutation used;
  // an extensionality round is assumed as one block literal, so it
  // reports every level.
  bool lastSolveWasUnsat() const;
  bool lastUnsatHasAssumptionGranularity() const;
  std::vector<ASTNode> lastUnsatAssumptionConjuncts() const;
  std::vector<size_t> lastUnsatCoreLevels() const;

  // Test-only inspection: the (array, index) rows the last refinement-driven
  // check-sat seeded into the batch-side read table. The invariant under
  // test is that rows introduced by popped conjuncts never appear, however
  // many of them the persistent registry keeps: a popped row's defining
  // equations are guarded by a root literal that is no longer assumed, so
  // its SAT variables float, and one such row in the counterexample tables
  // makes the model checker reject every candidate.
  std::vector<std::pair<ASTNode, ASTNode>> seededReadsForTesting() const;

  // Public only so the ToSATBase adapter in the implementation file can
  // name it; the definition never leaves IncrementalSolver.cpp.
  struct Impl;

private:
  // The body of checkSat. The public method runs it on a worker thread
  // with a large explicit stack: several passes walk formulas by
  // recursion, and parse-time inlining of chained define-funs builds
  // nodes deep enough (tens of thousands of levels from flat input) to
  // exhaust a default-sized stack.
  SOLVER_RETURN_TYPE checkSatOnCurrentStack(const ASTVec& assertionsSMT2,
                                            bool assumeLastLevelPerConjunct);

  std::unique_ptr<Impl> impl;
};

} // namespace stp

#endif
