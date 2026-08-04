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

// The incremental solving driver (INCREMENTAL-DESIGN.md sections 4.3-4.4).
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
// The driver refuses queries it cannot yet encode (arrays, floating point,
// array equality); the caller then runs the ordinary batch pipeline for that
// check-sat, and the driver resumes when the stack is back inside its
// fragment.

namespace stp
{

class STPMgr;
class AbsRefine_CounterExample;
class Simplifier;

class IncrementalSolver
{
public:
  // `batchSimp` is the batch pipeline's Simplifier -- the one `ce` reads
  // eliminated-variable definitions from when it builds a model. The driver
  // seeds it with its own eliminations at model-construction time; the
  // batch pipeline always clears it (resetSolver) before using it itself.
  IncrementalSolver(STPMgr* bm, AbsRefine_CounterExample* ce,
                    Simplifier* batchSimp);
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
  // The driver holds no per-level state: the assumption set is recomputed
  // from `assertionsSMT2` on every call (against permanent encoding caches),
  // so push and pop need no hooks here -- the parser's assertion stack is
  // the single source of truth. Base-level conjuncts become permanent unit
  // clauses, which is sound because the base level only ever grows; it is
  // destroyed only by reset/reset-assertions, which destroy this object.
  SOLVER_RETURN_TYPE checkSat(const ASTVec& assertionsSMT2);

private:
  struct Impl;
  std::unique_ptr<Impl> impl;
};

} // namespace stp

#endif
