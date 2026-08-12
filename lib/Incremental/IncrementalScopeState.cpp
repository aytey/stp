/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "stp/Incremental/IncrementalScopeState.h"

#include <algorithm>
#include <cassert>
#include <limits>

namespace stp
{

IncrementalScopeState::IncrementalScopeState()
    : nextFrameId(1), lastCommonPrefixValue(0), promotedDepthValue(0),
      promotionDriftPending(false), wholeStackActive(false)
{
}

void IncrementalScopeState::clearCurrentPreprocessing()
{
  wholeStackActive = false;
  wholeStackPreprocessing = PreprocessingTransaction();
  currentEliminations.clear();
  currentEliminatedVariables.clear();
  currentSemanticKeys.clear();
  for (Frame& frame : frames)
    frame.activePreprocessing =
        PreprocessingTransaction(PreprocessingMode::Raw,
                                 frame.rawConjunction);
}

void IncrementalScopeState::aggregate(
    const PreprocessingTransaction& transaction)
{
  currentSemanticKeys.insert(currentSemanticKeys.end(),
                             transaction.conjuncts.begin(),
                             transaction.conjuncts.end());
  for (const ScopedElimination& e : transaction.eliminated)
  {
    currentEliminations.push_back(e);
    if (e.symbol.GetKind() == SYMBOL)
      currentEliminatedVariables.insert(e.symbol);
  }
}

IncrementalScopeState::ReconcileResult
IncrementalScopeState::reconcile(const ASTVec& rawStack)
{
  size_t lcp = 0;
  while (lcp < frames.size() && lcp < rawStack.size() &&
         frames[lcp].rawConjunction == rawStack[lcp])
    ++lcp;

  bool demote = promotionDriftPending;
  promotionDriftPending = false;
  if (!demote && promotedDepthValue >= lcp && promotedDepthValue != 0)
    demote = true;

  for (size_t i = 0; i < lcp; ++i)
  {
    if (frames[i].stableSolves != std::numeric_limits<size_t>::max())
      ++frames[i].stableSolves;
  }
  frames.erase(frames.begin() + lcp, frames.end());
  for (size_t i = lcp; i < rawStack.size(); ++i)
    frames.push_back(Frame(nextFrameId++, rawStack[i]));

  if (demote)
    clearPromotions();

  lastCommonPrefixValue = lcp;
  clearCurrentPreprocessing();
  return ReconcileResult{lcp, demote};
}

void IncrementalScopeState::commitLevel(
    size_t level, const PreprocessingTransaction& transaction)
{
  assert(!wholeStackActive);
  assert(level < frames.size());
  assert(transaction.accepted);
  assert(transaction.source.IsNull() ||
         transaction.source == frames[level].rawConjunction);
  frames[level].activePreprocessing = transaction;
  aggregate(transaction);
}

void IncrementalScopeState::commitWholeStack(
    const PreprocessingTransaction& transaction)
{
  assert(transaction.accepted);
  currentEliminations.clear();
  currentEliminatedVariables.clear();
  currentSemanticKeys.clear();
  wholeStackPreprocessing = transaction;
  wholeStackActive = true;
  aggregate(transaction);
}

bool IncrementalScopeState::promotedConjunctsChanged(
    size_t level, const ASTVec& conjuncts) const
{
  if (level >= frames.size() || !frames[level].promoted)
    return true;
  return frames[level].promotedConjuncts != conjuncts;
}

void IncrementalScopeState::promote(size_t level, const ASTVec& conjuncts)
{
  assert(level < frames.size());
  assert(level == promotedDepthValue + 1);
  frames[level].promoted = true;
  frames[level].promotedConjuncts = conjuncts;
  promotedDepthValue = level;
}

void IncrementalScopeState::clearPromotions()
{
  for (Frame& frame : frames)
  {
    frame.promoted = false;
    frame.promotedConjuncts.clear();
  }
  promotedDepthValue = 0;
}

size_t IncrementalScopeState::cbpFedCommonPrefix() const
{
  size_t lcp = 0;
  while (lcp < cbpFedLevels.size() && lcp < frames.size() &&
         cbpFedLevels[lcp].scopeId == frames[lcp].id)
  {
    assert(cbpFedLevels[lcp].rawConjunction ==
           frames[lcp].rawConjunction);
    ++lcp;
  }
  return lcp;
}

void IncrementalScopeState::markCbpFed(size_t level)
{
  assert(level == cbpFedLevels.size());
  assert(level < frames.size());
  cbpFedLevels.push_back(
      ConsumerFrame(frames[level].id, frames[level].rawConjunction));
}

void IncrementalScopeState::rollbackCbpFedTo(size_t depth)
{
  assert(depth <= cbpFedLevels.size());
  cbpFedLevels.erase(cbpFedLevels.begin() + depth, cbpFedLevels.end());
}

void IncrementalScopeState::releaseEpochStorage()
{
  assert(!wholeStackActive);
  assert(currentEliminations.empty());
  assert(currentEliminatedVariables.empty());
  assert(currentSemanticKeys.empty());

  // Copying the live frames deliberately drops capacity retained by a much
  // deeper, now-popped stack, including capacity in cleared promotion and
  // preprocessing vectors. Scope identity and stability counters survive.
  std::vector<Frame>(frames).swap(frames);

  // clear()/resize(0) retain vector and hash-table high-water storage. A
  // relief epoch is a reclamation boundary, so release both the independent
  // CBP consumer and the already-reconciled transaction aggregates rather
  // than merely making them logically empty.
  std::vector<ConsumerFrame>().swap(cbpFedLevels);
  std::vector<CbpMemo>().swap(cbpMemos);
  std::vector<ScopedElimination>().swap(currentEliminations);
  ASTNodeSet().swap(currentEliminatedVariables);
  ASTVec().swap(currentSemanticKeys);
  wholeStackPreprocessing = PreprocessingTransaction();
}

size_t IncrementalScopeState::trimCbpMemoToCurrent()
{
  size_t lcp = 0;
  while (lcp < cbpMemos.size() && lcp < frames.size() &&
         cbpMemos[lcp].rawConjunction == frames[lcp].rawConjunction)
    ++lcp;
  cbpMemos.resize(lcp);
  return lcp;
}

IncrementalScopeState::CbpMemo&
IncrementalScopeState::startCbpMemo(size_t level)
{
  assert(level == cbpMemos.size());
  assert(level < frames.size());
  cbpMemos.push_back(CbpMemo());
  cbpMemos.back().rawConjunction = frames[level].rawConjunction;
  return cbpMemos.back();
}

} // namespace stp
