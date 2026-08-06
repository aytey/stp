/********************************************************************
 * AUTHORS: Andrew Teylu, Claude
 *
 * BEGIN DATE: Aug, 2026
 *
 * Incremental constant-bit propagation with push/pop rollback.
 *
 * Wraps the CBP machinery so that:
 *   - addConstraints(node) extends the existing fixedMap/dependencies
 *     and propagates only from the newly-constrained nodes.
 *   - push() snapshots the current state via an undo log.
 *   - pop() replays the undo log to restore the prior state.
 *
 * This avoids re-running CBP on the entire formula for every
 * check-sat in an incremental session.
 ********************************************************************/

#ifndef INCREMENTALCBP_H_
#define INCREMENTALCBP_H_

#include "stp/AST/AST.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/constantBitP/NodeToFixedBitsMap.h"

#include <utility>
#include <vector>

#include "stp/NodeFactory/NodeFactory.h"

namespace stp
{
class STPMgr;
class Simplifier;
}

namespace simplifier
{
namespace constantBitP
{
class Dependencies;
class WorkList;
class MultiplicationStatsMap;
}
}

namespace stp
{

// An undo-log entry: the state of one node's FixedBits before it was
// modified during propagation at the current level.
struct CBPUndoEntry
{
  ASTNode node;
  simplifier::constantBitP::FixedBits oldBits;  // copy of the bits before mutation
  bool wasNew;                       // true if the node was not in the map before
};

class IncrementalCBP
{
public:
  IncrementalCBP(STPMgr* mgr, Simplifier* simp, NodeFactory* nf);
  ~IncrementalCBP();

  // No copies.
  IncrementalCBP(const IncrementalCBP&) = delete;
  IncrementalCBP& operator=(const IncrementalCBP&) = delete;

  // Add new constraints (a conjunction of assertions) and propagate
  // only from the newly-affected nodes.  Returns true if no conflict;
  // false if UNSAT was detected.
  bool addConstraints(const ASTNode& conjunction);

  // Set the top-level node to true and propagate.  Used after all
  // constraints at a level have been added.
  bool setTopTrue(const ASTNode& top);

  // Push: start recording an undo log for the new level.
  void push();

  // Pop: replay the undo log to restore the prior level's state.
  void pop();

  // Return {node -> constant} for every fully-determined node.
  ASTNodeMap getAllFixed();

  // Was a conflict detected?
  bool isConflict() const;

  // Current depth (number of pushed levels, 0 = base).
  size_t depth() const { return undoStack.size(); }

private:
  STPMgr* mgr;
  Simplifier* simplifier;
  NodeFactory* nf;

  // The persistent CBP state — survives across push/pop.
  simplifier::constantBitP::NodeToFixedBitsMap* fixedMap;
  simplifier::constantBitP::WorkList* workList;
  simplifier::constantBitP::Dependencies* dependencies;
  simplifier::constantBitP::MultiplicationStatsMap* msm;

  bool conflict;
  bool topFixed;

  // Stack of undo logs.  undoStack[i] holds the entries to replay
  // when popping level i.
  std::vector<std::vector<CBPUndoEntry>> undoStack;

  // The currently-recording undo log (top of undoStack), or nullptr
  // at the base level where no rollback is needed.
  std::vector<CBPUndoEntry>* currentLog;

  // Reused per-propagation scratch vectors.
  std::vector<unsigned> previousChildrenFixedCount;
  std::vector<simplifier::constantBitP::FixedBits*> childrenBits;

  // Get or create a FixedBits entry, recording an undo entry if this
  // is a new node and we're inside a pushed level.
  simplifier::constantBitP::FixedBits* getOrCreate(const ASTNode& n);

  // Record the current state of a node before mutation.
  void recordBeforeMutation(const ASTNode& n, simplifier::constantBitP::FixedBits* bits);

  // Run the worklist-based propagation loop.
  void propagate();

  // Extend the dependency graph with a new sub-DAG.
  void extendDependencies(const ASTNode& n);

  // Seed the worklist with nodes from a new sub-DAG.
  void seedWorklist(const ASTNode& n);
};

} // namespace stp

#endif // INCREMENTALCBP_H_
