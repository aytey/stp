/********************************************************************
 * Replace a fully symmetric distinct with a strict chain.
 ********************************************************************/
#ifndef STP_DISTINCTORDERING_H
#define STP_DISTINCTORDERING_H

#include "stp/AST/AST.h"
#include <vector>

namespace stp
{

class STPMgr;

// One (distinct t1 ... tn) as the parser saw it, before it was dissolved into
// pairwise disequalities: the operands in source order, and the node the
// dissolution produced.
struct DLL_PUBLIC DistinctGroup
{
  ASTVec operands;
  ASTNode emitted;
};

// If the operands of a recorded distinct are variables that occur nowhere
// else, every permutation of them maps the formula to itself, so requiring
// them to be strictly increasing loses no models up to that symmetry --
// and n-1 comparisons replace n(n-1)/2 disequalities.
//
// The gain is not marginal. Three hundred unconstrained 32-bit variables
// under one distinct take 88s pairwise and 0.06s chained, because the
// pairwise form asks a bit-blaster to discover an ordering that the chain
// simply states.
//
// Returns `root` unchanged unless it rewrote something, and reports through
// `ordered` how many groups it took. Sound in the direction that matters
// unconditionally: the chain implies the distinct, so every model of the
// result is a model of `root` and published models never need qualifying --
// which is also why only positive occurrences are taken. The converse -- that
// rewriting cannot turn satisfiable into unsatisfiable -- is what the
// occurrence guard buys, and it is checked against `root` itself rather than
// assumed from the parse.
ASTNode applyDistinctOrdering(STPMgr* manager, const ASTNode& root,
                              const std::vector<DistinctGroup>& groups,
                              size_t* ordered = NULL);

} // namespace stp

#endif
