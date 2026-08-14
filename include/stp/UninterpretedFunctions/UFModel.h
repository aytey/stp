/********************************************************************
 * Certified public models for durable uninterpreted applications.
 ********************************************************************/
#ifndef STP_UFMODEL_H
#define STP_UFMODEL_H

#include "stp/UninterpretedFunctions/UFChecker.h"
#include <iosfwd>
#include <string>

namespace stp
{

class AbsRefine_CounterExample;
class STPMgr;
class UFTheoryAdapter;

// The only boundary from UFCHK's representation-independent values to host
// ASTs and public output. Lowered result/name symbols never cross it.
class DLL_PUBLIC UFModel final
{
public:
  // Build a source-sort-correct Bool/BV constant in manager.
  static ASTNode concreteValue(STPMgr* manager,
                               const UFConcreteValue& value);

  // Evaluate one context-owned, active, registered durable application from
  // the most recently certified solve map. Failures are nonfatal and leave
  // value undefined.
  static bool evaluateApplication(STPMgr* manager,
                                  const UFTheoryAdapter* adapter,
                                  const ASTNode& durableHandle,
                                  ASTNode& value,
                                  std::string& diagnostic);

  // Complete every durable application in the preserved public root with its
  // certified value. This is used for the final pointwise model replay; the
  // returned root contains no UF_APPLY and no solve-local symbol.
  static bool completePublicRoot(STPMgr* manager,
                                 const UFTheoryAdapter& adapter,
                                 ASTNode& completed,
                                 std::string& diagnostic);

  static bool replayPublicRoot(AbsRefine_CounterExample& counterexample,
                               const UFTheoryAdapter& adapter,
                               std::string& diagnostic);

  // Vacuous certified interpretation for active declarations when the
  // completed root contains no UF application at all.
  static UFFunctionModelSeedSet
  defaultSeed(const std::vector<const UFDecl*>& declarations);

  // Emit one valid deterministic SMT-LIB2 define-fun per active declaration,
  // including declarations with no active observations.
  static void printSMTLIB2(std::ostream& os,
                           const UFFunctionModelSeedSet& seed);
};

} // namespace stp

#endif
