/********************************************************************
 * AUTHORS: Michael Katelman, Trevor Hansen, Stephen McCamant, Vijay Ganesh
 *
 * BEGIN DATE: Februrary, 2010
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

/* This is ABSOLUTELY DISGUSTING!
 * These globals used by the library should
 * be encapsulated in a "Context" class
 * to allow concurrent usage of the STP library
 */

#ifndef GLOBALS_H
#define GLOBALS_H
#include "stp/Util/Attributes.h"
#include <vector>

/* FIXME: Clients who import this header file have to have
 * ASTNode already declarted (eurgh)
 *
 */

namespace stp
{
// FIXME: We don't need all these forward declarations here!
class STPMgr;
class ASTNode;
class ASTInternal;
class ASTInterior;
class ASTSymbol;
class ASTBVConst;
class BVSolver;
class STP;
class Cpp_interface;

enum inputStatus
{
  NOT_DECLARED = 0, // Not included in the input file / stream
  TO_BE_SATISFIABLE,
  TO_BE_UNSATISFIABLE,
  TO_BE_UNKNOWN // Specified in the input file as unknown.
};

// return types for the GetType() function in ASTNode class.
// FLOATINGPOINT_TYPE is appended after UNKNOWN_TYPE, not slotted in sort
// order. The legacy prefix of the C API's type_t mirrors these values
// numerically, preserving values compiled into pre-floating-point clients.
// Source-only sorts such as RoundingMode are intentionally absent here:
// GetType() describes the carrier used by the bit-vector pipeline.
enum types
{
  BOOLEAN_TYPE = 0,
  BITVECTOR_TYPE,
  ARRAY_TYPE,
  UNKNOWN_TYPE,
  FLOATINGPOINT_TYPE
};

enum SOLVER_RETURN_TYPE
{
  SOLVER_INVALID = 0,
  SOLVER_VALID = 1,
  SOLVER_UNDECIDED = 2,
  SOLVER_TIMEOUT = 3,
  // No answer for a reason that is not a budget the SAT solver enforces:
  // either the method STP would have used is incomplete for this input, or
  // something stopped before the solver was reached, so neither verdict may
  // be reported. Appended, and nothing switches exhaustively on this enum, so
  // a consumer that has not heard of it compares unequal to every case it
  // knows -- which is the right default for "no answer".
  //
  // Which of the two a no-answer leaves as is STPMgr::noAnswerVerdict: this
  // one for UnknownReason::Incomplete, SOLVER_TIMEOUT for the clock and the
  // conflict budget. The split is coarse on purpose -- the clock and the
  // conflict budget genuinely share a verdict, and (get-info :reason-unknown)
  // or vc_getReasonUnknown is what separates those two. What it does buy is
  // that nothing is called a timeout that no clock could have caused, which
  // matters to a caller holding only the verdict: vc_query is one, and until
  // vc_getReasonUnknown existed it was the only thing such a caller had.
  SOLVER_UNKNOWN = 4,
  SOLVER_ERROR = -100,
  SOLVER_UNSATISFIABLE = 1,
  SOLVER_SATISFIABLE = 0
};

// Why the last solve had no answer, for (get-info :reason-unknown). The two
// spellings are the ones SMT-LIB 2 predefines for the flag beyond a free-form
// s-expression; `incomplete` is exactly its meaning here -- the encoding STP
// would have solved cannot represent every model of the input.
enum class UnknownReason
{
  None,
  Timeout,
  // The conflict budget (--max-num-confl) ran out. Told apart from the clock
  // because a caller acts differently on the two: a wall-clock timeout may
  // succeed with more time on the same machine, while a conflict budget is
  // deterministic and will not.
  ConflictBudget,
  Incomplete
};

// Empty vector. Useful commonly used ASTNodes
DLL_PUBLIC extern std::vector<ASTNode> _empty_ASTVec;

extern THREAD_LOCAL_IE enum inputStatus
    input_status; // Needed by the SMTLIB printer

// Useful global variables. Use for parsing only
DLL_PUBLIC extern THREAD_LOCAL_IE STP* GlobalSTP;
DLL_PUBLIC extern THREAD_LOCAL_IE STPMgr* GlobalParserBM;
DLL_PUBLIC extern THREAD_LOCAL_IE Cpp_interface* GlobalParserInterface;

// Function that computes various kinds of statistics for the phases
// of STP
void CountersAndStats(const char* functionname, STPMgr *bm);
}
#endif
