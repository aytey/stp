/********************************************************************
 * Incremental constant-bit propagation — implementation.
 ********************************************************************/

#include "stp/Incremental/IncrementalCBP.h"

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"

#include "extlib-constbv/constantbv.h"

using simplifier::constantBitP::ConstantBitPropagation;
using simplifier::constantBitP::FixedBits;
using simplifier::constantBitP::MultiplicationStatsMap;
using simplifier::constantBitP::NodeToFixedBitsMap;
using simplifier::constantBitP::Result;

namespace stp
{

// ─── Construction / destruction ──────────────────────────────────────

IncrementalCBP::IncrementalCBP(STPMgr* mgr_, NodeFactory* nf_)
    : mgr(mgr_), nf(nf_),
      fixedMap(new NodeToFixedBitsMap(1000)),
      msm(new MultiplicationStatsMap()),
      conflict(false), currentLog(nullptr)
{
}

IncrementalCBP::~IncrementalCBP()
{
  delete fixedMap;
  delete msm;
}

// ─── Parent map (growable) ───────────────────────────────────────────

void IncrementalCBP::extendParentMap(const ASTNode& root)
{
  std::vector<ASTNode> stack;
  stack.push_back(root);

  while (!stack.empty())
  {
    ASTNode n = stack.back();
    stack.pop_back();

    if (n.isConstant())
      continue;
    if (!depsVisited.insert(n).second)
      continue;

    for (unsigned i = 0; i < n.Degree(); i++)
    {
      const ASTNode& child = n[i];
      if (child.isConstant())
        continue;
      parentMap[child.GetNodeNum()].push_back(n);
    }

    for (unsigned i = 0; i < n.Degree(); i++)
      stack.push_back(n[i]);
  }
}

// ─── Worklist ────────────────────────────────────────────────────────

void IncrementalCBP::pushWork(const ASTNode& n)
{
  if (n.isConstant())
    return;
  switch (n.GetKind())
  {
    case BVMULT: case BVPLUS: case BVDIV: case BVMOD:
    case SBVDIV: case SBVREM: case SBVMOD:
      expensiveWork.insert(n);
      break;
    default:
      cheapWork.insert(n);
      break;
  }
}

ASTNode IncrementalCBP::popWork()
{
  if (!cheapWork.empty())
  {
    ASTNode n = *cheapWork.begin();
    cheapWork.erase(cheapWork.begin());
    return n;
  }
  ASTNode n = *expensiveWork.begin();
  expensiveWork.erase(expensiveWork.begin());
  return n;
}

bool IncrementalCBP::workEmpty() const
{
  return cheapWork.empty() && expensiveWork.empty();
}

// Seed the worklist with nodes from a sub-DAG that have at least one
// constant child (same as the original WorkList::addToWorklist).
void IncrementalCBP::seedWorklist(const ASTNode& n)
{
  ASTNodeSet visited;
  std::vector<ASTNode> stack;
  stack.push_back(n);

  while (!stack.empty())
  {
    ASTNode node = stack.back();
    stack.pop_back();

    if (node.isConstant())
      continue;
    if (!visited.insert(node).second)
      continue;

    bool hasConstChild = false;
    for (unsigned i = 0; i < node.Degree(); i++)
    {
      if (node[i].isConstant())
        hasConstChild = true;
      stack.push_back(node[i]);
    }
    if (hasConstChild)
      pushWork(node);
  }
}

// ─── FixedBits management ────────────────────────────────────────────

FixedBits* IncrementalCBP::getOrCreate(const ASTNode& n)
{
  auto it = fixedMap->map->find(n);
  if (it != fixedMap->map->end())
    return it->second;

  int bw = (n.GetValueWidth() == 0) ? 1 : n.GetValueWidth();
  FixedBits* fb = new FixedBits(bw, (BOOLEAN_TYPE == n.GetType()));

  // Initialize constants.
  if (BVCONST == n.GetKind() || BITVECTOR == n.GetKind())
  {
    CBV cbv = n.GetBVConst();
    for (unsigned j = 0; j < n.GetValueWidth(); j++)
    {
      fb->setFixed(j, true);
      fb->setValue(j, CONSTANTBV::BitVector_bit_test(cbv, j));
    }
  }
  else if (TRUE == n.GetKind())
  {
    fb->setFixed(0, true);
    fb->setValue(0, true);
  }
  else if (FALSE == n.GetKind())
  {
    fb->setFixed(0, true);
    fb->setValue(0, false);
  }

  fixedMap->map->insert(std::make_pair(n, fb));

  // Record as new for undo.
  if (currentLog)
    currentLog->push_back(UndoEntry{n, FixedBits(*fb), true});

  return fb;
}

void IncrementalCBP::recordBefore(const ASTNode& n, FixedBits* bits)
{
  if (currentLog)
    currentLog->push_back(UndoEntry{n, FixedBits(*bits), false});
}

// ─── Scheduling helpers ─────────────────────────────────────────────

void IncrementalCBP::scheduleParents(const ASTNode& n)
{
  auto it = parentMap.find(n.GetNodeNum());
  if (it != parentMap.end())
    for (const ASTNode& p : it->second)
      pushWork(p);
}

void IncrementalCBP::scheduleParentsExcept(const ASTNode& child,
                                           const ASTNode& except)
{
  auto it = parentMap.find(child.GetNodeNum());
  if (it != parentMap.end())
    for (const ASTNode& p : it->second)
      if (!(p == except))
        pushWork(p);
}

// ─── Propagation ─────────────────────────────────────────────────────

void IncrementalCBP::propagate()
{
  if (conflict)
    return;

  while (!workEmpty())
  {
    const ASTNode n = popWork();
    if (n.isConstant())
      continue;

    FixedBits* nBits = getOrCreate(n);
    int previousTop = nBits->countFixed();

    const unsigned degree = n.Degree();
    childBits.clear();
    prevChildCounts.clear();

    for (unsigned i = 0; i < degree; i++)
    {
      FixedBits* cb = getOrCreate(n[i]);
      childBits.push_back(cb);
      prevChildCounts.push_back(cb->countFixed());
    }

    Result status = simplifier::constantBitP::NO_CHANGE;
    if (SYMBOL != n.GetKind())
    {
      // Record before mutation for undo.
      if (currentLog)
      {
        recordBefore(n, nBits);
        for (unsigned i = 0; i < degree; i++)
          recordBefore(n[i], childBits[i]);
      }

      status = ConstantBitPropagation::dispatchToTransferFunctions(
          mgr, n.GetKind(), childBits, *nBits, n, msm);
    }

    if (simplifier::constantBitP::CONFLICT == status)
    {
      conflict = true;
      return;
    }

    int newCount = nBits->countFixed();

    if (status != simplifier::constantBitP::NO_CHANGE)
    {
      if (newCount != previousTop)
        scheduleParents(n);

      for (unsigned i = 0; i < degree; i++)
      {
        if ((int)childBits[i]->countFixed() != (int)prevChildCounts[i])
        {
          scheduleParentsExcept(n[i], n);
          pushWork(n[i]);
        }
      }
    }
  }
}

// ─── Public API ──────────────────────────────────────────────────────

bool IncrementalCBP::addConstraints(const ASTNode& conjunction)
{
  if (conflict)
    return false;

  // Extend the parent map with the new sub-DAG.
  extendParentMap(conjunction);

  // Seed the worklist from the new nodes. Only propagate bottom-up
  // from constants and structural constraints — do NOT set the
  // conjunction itself to true (see addConstraintsAggressive for
  // the speculative variant that does).
  seedWorklist(conjunction);

  propagate();
  return !conflict;
}

bool IncrementalCBP::addConstraintsAggressive(const ASTNode& conjunction)
{
  if (conflict)
    return false;

  extendParentMap(conjunction);
  seedWorklist(conjunction);

  // AGGRESSIVE: set the conjunction to true and propagate.
  // This discovers more constants than bottom-up propagation alone,
  // but the results are only valid IF this conjunction actually holds.
  // The caller must validate the SAT result against the original
  // formula to ensure soundness.
  FixedBits* topFB = getOrCreate(conjunction);
  if (currentLog)
    recordBefore(conjunction, topFB);
  topFB->setFixed(0, true);
  topFB->setValue(0, true);
  pushWork(conjunction);

  propagate();
  return !conflict;
}

void IncrementalCBP::push()
{
  undoStack.push_back(std::vector<UndoEntry>());
  currentLog = &undoStack.back();
}

void IncrementalCBP::pop()
{
  assert(!undoStack.empty());

  // Replay in reverse.
  std::vector<UndoEntry>& log = undoStack.back();
  for (auto it = log.rbegin(); it != log.rend(); ++it)
  {
    if (it->wasNew)
    {
      auto mapIt = fixedMap->map->find(it->node);
      if (mapIt != fixedMap->map->end())
      {
        delete mapIt->second;
        fixedMap->map->erase(mapIt);
      }
    }
    else
    {
      auto mapIt = fixedMap->map->find(it->node);
      if (mapIt != fixedMap->map->end())
        *(mapIt->second) = it->oldBits;
    }
  }

  undoStack.pop_back();
  currentLog = undoStack.empty() ? nullptr : &undoStack.back();
  conflict = false;
}

ASTNodeMap IncrementalCBP::getAllFixed()
{
  ASTNodeMap result;

  for (auto it = fixedMap->map->begin(); it != fixedMap->map->end(); ++it)
  {
    const ASTNode& node = it->first;
    const FixedBits& bits = *it->second;

    if (node.isConstant())
      continue;
    if (BVCONCAT == node.GetKind())
      continue;
    if (node.GetType() != BOOLEAN_TYPE && node.GetType() != BITVECTOR_TYPE)
      continue;

    if (bits.isTotallyFixed())
    {
      ASTNode constNode;
      if (node.GetType() == BOOLEAN_TYPE)
        constNode = bits.getValue(0) ? mgr->ASTTrue : mgr->ASTFalse;
      else
        constNode = nf->CreateConstant(bits.GetBVConst(), node.GetValueWidth());

      result.insert(std::make_pair(node, constNode));
    }
  }

  return result;
}

} // namespace stp
