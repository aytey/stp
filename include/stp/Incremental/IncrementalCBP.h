/********************************************************************
 * AUTHORS: Andrew V. Jones, Trevor Hansen
 *
 * BEGIN DATE: August, 2026
 *
 * Per-call constant-bit propagation over the incremental driver's
 * lowered conjuncts.
 *
 * A worklist engine around the batch transfer functions
 * (ConstantBitPropagation::dispatchToTransferFunctions), fed one
 * level at a time in stack order:
 *
 *   feedLevel(lowered_level_conjunction)
 *     Extends the DAG with the level's lowered form, assumes the
 *     conjunction TRUE (each level is asserted for the whole call, so
 *     its truth is a sound assumption for every consequence drawn
 *     this call), and propagates to a fixpoint.  Facts discovered
 *     while feeding level L therefore depend only on levels <= L --
 *     the same prefix discipline as the pushed-definition context,
 *     and for the same reason: it keeps a conjunct's rewritten form
 *     stable as the stack grows underneath it, and a fact can never
 *     outlive the shallowest level it was drawn from (it is attached
 *     at the level whose feed discovered it, and stack discipline
 *     pops deeper levels first).
 *
 *   takeNewlyFixed()
 *     The nodes that became fully determined during the last feed --
 *     the per-level fact delta, without rescanning the whole map.
 *
 *   fixedConstants()
 *     {node -> constant} for every fully-determined non-constant
 *     node seen so far.
 *
 * The instance lives for ONE check-sat call.  Persistence across
 * calls was deliberately rejected: an earlier prototype's undo-log
 * rollback (branch incremental-cbp-prototype) traded correctness
 * hazards and bookkeeping for a phase this per-call engine spends
 * milliseconds in.
 ********************************************************************/

#ifndef INCREMENTALCBP_H_
#define INCREMENTALCBP_H_

#include "stp/AST/AST.h"
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/constantBitP/MultiplicationStats.h"
#include "stp/Simplifier/constantBitP/NodeToFixedBitsMap.h"

#include <map>
#include <set>
#include <vector>

namespace stp
{
class STPMgr;

class IncrementalCBP
{
public:
  IncrementalCBP(STPMgr* mgr, NodeFactory* nf);
  ~IncrementalCBP();

  IncrementalCBP(const IncrementalCBP&) = delete;
  IncrementalCBP& operator=(const IncrementalCBP&) = delete;

  /// Extend the DAG with one level's lowered conjunction, assume it
  /// true, and propagate to a fixpoint. Returns false on conflict --
  /// the live stack up to this level is unsatisfiable.
  bool feedLevel(const ASTNode& conjunction);

  /// Nodes that became fully determined during the last feedLevel call
  /// (cleared by the call itself). Constants excluded.
  const std::vector<ASTNode>& takeNewlyFixed() const { return newlyFixed; }

  /// The constant a fully-determined node is fixed to, or the null node.
  ASTNode constantOf(const ASTNode& n) const;

  /// Was a conflict detected?
  bool inConflict() const { return conflict; }

private:
  void extendParentMap(const ASTNode& root);
  void seedWorklist(const ASTNode& n);
  void pushWork(const ASTNode& n);
  ASTNode popWork();
  bool workEmpty() const;
  simplifier::constantBitP::FixedBits* getOrCreate(const ASTNode& n);
  void scheduleParents(const ASTNode& n, const ASTNode& except);
  void propagate();

  STPMgr* mgr;
  NodeFactory* nf;

  simplifier::constantBitP::NodeToFixedBitsMap* fixedMap;
  simplifier::constantBitP::MultiplicationStatsMap* msm;
  bool conflict;

  // Growable parent overlay: child -> parents, extended per feed.
  std::map<uint64_t, std::vector<ASTNode>> parentMap;
  ASTNodeSet depsVisited;

  // Two-tier worklist: cheap transfer functions drain before the
  // expensive arithmetic ones run (the batch WorkList's discipline).
  std::set<ASTNode> cheapWork;
  std::set<ASTNode> expensiveWork;

  // Fully-determined transitions of the current feed.
  std::vector<ASTNode> newlyFixed;

  // Reused per propagate step.
  std::vector<simplifier::constantBitP::FixedBits*> childBits;
  std::vector<unsigned> prevChildCounts;
};

} // namespace stp

#endif
