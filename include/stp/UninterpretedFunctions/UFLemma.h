/********************************************************************
 * Side-effect-free congruence lemma canonicalization/validation.
 ********************************************************************/
#ifndef STP_UFLEMMA_H
#define STP_UFLEMMA_H

#include "stp/UninterpretedFunctions/UFChecker.h"

namespace stp
{

struct DLL_PUBLIC UFEqualityAtom
{
  ASTNode left;
  ASTNode right;
  SourceSort sort;
  size_t originalPosition = 0;
};

struct DLL_PUBLIC UFAbstractLemma
{
  std::vector<UFEqualityAtom> premise;
  UFEqualityAtom conclusion;
  uint64_t candidateVersion = 0;

  // The final implication clause has one negated literal per premise and one
  // positive conclusion literal. This evaluates it from already observed
  // equality truth values without constructing an AST or touching SAT.
  bool evaluate(bool conclusionEquality,
                const std::vector<bool>& premiseEqualities) const;
};

class DLL_PUBLIC UFLemmaOracle final
{
public:
  // Produces the canonical abstract layer and proves it rejects the
  // certificate's unchanged candidate before either host adapter may mutate
  // SAT. A false return is an internal error and carries a diagnostic.
  static bool buildAndValidate(const UFCongruenceConflict& conflict,
                               UFAbstractLemma& lemma,
                               std::string& diagnostic);
};

} // namespace stp

#endif
