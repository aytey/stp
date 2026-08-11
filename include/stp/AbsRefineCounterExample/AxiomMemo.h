// -*- c++ -*-
/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

#ifndef AXIOMMEMO_H_
#define AXIOMMEMO_H_

// The array-refinement congruence axiom, and the memo that stops one being
// emitted twice against the same solver.
//
// Declared here rather than kept file-local so the memo can be tested
// directly. It has to be: the only situation that exercises it is a
// refinement round re-deriving axioms the solver already holds, which in
// normal operation does not happen -- no file in the query corpus reaches it
// -- and in abnormal operation means the encoding and the word-level
// evaluation already disagree. Code whose sole execution path is unreachable
// from the suite, in a layer where a mistake drops a constraint and turns an
// unsat query sat, does not get to ship untested.

#include "stp/AST/AST.h"
#include "stp/Sat/SATSolver.h"
#include "stp/ToSat/ToSATBase.h"

namespace stp
{

struct AxiomToBe
{
  AxiomToBe(ASTNode i0, ASTNode i1, ASTNode v0, ASTNode v1)
  {
    index0 = i0;
    index1 = i1;
    value0 = v0;
    value1 = v1;
  }
  ASTNode index0, index1;
  ASTNode value0, value1;

  int numberOfConstants() const
  {
    return ((index0.isConstant() ? 1 : 0) + (index1.isConstant() ? 1 : 0) +
            (index0.isConstant() ? 1 : 0) + (index1.isConstant() ? 1 : 0));
  }
};

// Emit each axiom that this solver has not already been given, and return how
// many were actually emitted. Callers re-solve only on a non-zero count: a
// round that emitted nothing has changed nothing, so solving again would burn
// a search before the no-progress guard could notice. `toBe` is cleared.
size_t applyAxiomsToSolver(ToSATBase::ASTNodeToSATVar& satVar,
                           std::vector<AxiomToBe>& toBe, SATSolver& SatSolver);

} // namespace stp

#endif
