/********************************************************************
 * Incremental constant-bit propagation with push/pop rollback.
 *
 * Operates on post-FP-lowered, post-array-transformed formulas (pure
 * BV).  Designed to be called incrementally:
 *
 *   addConstraints(lowered_conjunction)
 *     Extends the DAG, propagates only from new nodes.
 *
 *   push() / pop()
 *     Snapshots / restores FixedBits via an undo log.
 *
 *   getAllFixed()
 *     Returns {node -> constant} for all fully-determined nodes.
 ********************************************************************/

#ifndef INCREMENTALCBP_H_
#define INCREMENTALCBP_H_

#include "stp/NodeFactory/HashingNodeFactory.h"
#include "stp/AST/AST.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/constantBitP/MultiplicationStats.h"
#include "stp/Simplifier/constantBitP/NodeToFixedBitsMap.h"
#include "extlib-unordered-dense/ankerl/unordered_dense.h"

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

  /// Extend the DAG with a new conjunction and propagate.
  /// Returns false on conflict (UNSAT detected).
  bool addConstraints(const ASTNode& conjunction);

  /// Push: start recording an undo log for rollback.
  void push();

  /// Pop: replay the undo log, restoring pre-push state.
  void pop();

  /// Return {node -> constant} for every fully-determined node.
  ASTNodeMap getAllFixed();

  /// Was a conflict detected?
  bool isConflict() const { return conflict; }

  /// Number of pushed levels (0 = base).
  size_t depth() const { return undoStack.size(); }

private:
  STPMgr* mgr;
  NodeFactory* nf;

  // The persistent state across push/pop.
  simplifier::constantBitP::NodeToFixedBitsMap* fixedMap;
  simplifier::constantBitP::MultiplicationStatsMap* msm;
  bool conflict;

  // ── Growable parent map ──────────────────────────────────────────
  // Maps each child node id to its parent nodes.  Grows as new
  // sub-DAGs arrive via addConstraints.
  typedef ankerl::unordered_dense::map<uint64_t, std::vector<ASTNode>>
      ParentMap;
  ParentMap parentMap;
  ASTNodeSet depsVisited;  // nodes already in the parent map

  void extendParentMap(const ASTNode& root);

  // ── Worklist ─────────────────────────────────────────────────────
  typedef ankerl::unordered_dense::set<ASTNode, ASTNode::ASTNodeHasher,
                                       ASTNode::ASTNodeEqual>
      WorkSet;
  WorkSet cheapWork;
  WorkSet expensiveWork;

  void pushWork(const ASTNode& n);
  ASTNode popWork();
  bool workEmpty() const;
  void seedWorklist(const ASTNode& n);

  // ── Undo log ─────────────────────────────────────────────────────
  struct UndoEntry
  {
    ASTNode node;
    simplifier::constantBitP::FixedBits oldBits;
    bool wasNew;  // true if node was absent from fixedMap before
  };
  std::vector<std::vector<UndoEntry>> undoStack;
  std::vector<UndoEntry>* currentLog;

  // ── Core operations ──────────────────────────────────────────────
  simplifier::constantBitP::FixedBits* getOrCreate(const ASTNode& n);
  void recordBefore(const ASTNode& n,
                    simplifier::constantBitP::FixedBits* bits);
  void propagate();
  void scheduleParents(const ASTNode& n);
  void scheduleParentsExcept(const ASTNode& child, const ASTNode& except);

  // Scratch vectors reused per propagation step.
  std::vector<unsigned> prevChildCounts;
  std::vector<simplifier::constantBitP::FixedBits*> childBits;
};

} // namespace stp

#endif // INCREMENTALCBP_H_
