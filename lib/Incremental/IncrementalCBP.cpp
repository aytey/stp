/********************************************************************
 * AUTHORS: Andrew Teylu, Claude
 *
 * BEGIN DATE: Aug, 2026
 ********************************************************************/

#include "stp/Incremental/IncrementalCBP.h"

#include "stp/AST/AST.h"
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/NodeFactory/HashingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/Dependencies.h"
#include "stp/Simplifier/constantBitP/MultiplicationStats.h"
#include "stp/Simplifier/constantBitP/WorkList.h"

// For dispatchToTransferFunctions.
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"

#include <algorithm>
#include <cassert>

using namespace simplifier::constantBitP;

namespace stp
{

// ─── Growable parent map ─────────────────────────────────────────────
// Dependencies uses a CSR format that can't be extended after
// construction.  This overlay stores parent edges for nodes added
// after the initial Dependencies was built, and delegates to the
// original for everything else.
class GrowableDependencies
{
  Dependencies* original;  // may be null if no base formula yet
  typedef ankerl::unordered_dense::map<uint64_t,
      std::vector<ASTNode>> OverlayMap;
  OverlayMap overlay;
  ASTNodeSet visited;

public:
  GrowableDependencies() : original(nullptr) {}
  ~GrowableDependencies() { delete original; }

  void setOriginal(Dependencies* d) { original = d; }

  // Add parent edges for a new sub-DAG.
  void extend(const ASTNode& root)
  {
    std::vector<ASTNode> stack;
    stack.push_back(root);

    while (!stack.empty())
    {
      ASTNode n = stack.back();
      stack.pop_back();

      if (n.isConstant())
        continue;
      if (!visited.insert(n).second)
        continue;

      for (unsigned i = 0; i < n.Degree(); i++)
      {
        const ASTNode& child = n[i];
        if (child.isConstant())
          continue;
        overlay[child.GetNodeNum()].push_back(n);
      }

      for (unsigned i = 0; i < n.Degree(); i++)
        stack.push_back(n[i]);
    }
  }

  // Get all parents of a node (original + overlay).
  // Returns a temporary vector — callers iterate immediately.
  std::vector<ASTNode> getParents(const ASTNode& n) const
  {
    std::vector<ASTNode> result;

    // From the original CSR dependencies.
    if (original)
    {
      auto range = original->getDependents(n);
      result.insert(result.end(), range.begin(), range.end());
    }

    // From the overlay.
    auto it = overlay.find(n.GetNodeNum());
    if (it != overlay.end())
      result.insert(result.end(), it->second.begin(), it->second.end());

    return result;
  }
};

// ─── IncrementalCBP implementation ───────────────────────────────────

IncrementalCBP::IncrementalCBP(STPMgr* mgr_, Simplifier* simp_,
                               NodeFactory* nf_)
    : mgr(mgr_), simplifier(simp_), nf(nf_),
      fixedMap(new NodeToFixedBitsMap(1000)),
      workList(nullptr),
      dependencies(nullptr),
      msm(new MultiplicationStatsMap()),
      conflict(false), topFixed(false), currentLog(nullptr)
{
}

IncrementalCBP::~IncrementalCBP()
{
  delete fixedMap;
  delete workList;
  // dependencies is owned by growableDeps in practice, but we
  // allocated it raw here, so delete it.
  delete dependencies;
  delete msm;
}

FixedBits* IncrementalCBP::getOrCreate(const ASTNode& n)
{
  auto it = fixedMap->map->find(n);
  if (it != fixedMap->map->end())
    return it->second;

  // Create a new entry.
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

  // Record that this is a new entry for the undo log.
  if (currentLog)
    currentLog->push_back(CBPUndoEntry{n, FixedBits(*fb), true});

  return fb;
}

void IncrementalCBP::recordBeforeMutation(const ASTNode& n, FixedBits* bits)
{
  if (currentLog)
    currentLog->push_back(CBPUndoEntry{n, FixedBits(*bits), false});
}

void IncrementalCBP::propagate()
{
  if (conflict)
    return;
  if (!workList)
    return;

  while (!workList->isEmpty())
  {
    const ASTNode& n = workList->pop();

    if (n.isConstant())
      continue;

    FixedBits* nBits = getOrCreate(n);
    int previousTop = nBits->countFixed();

    const unsigned degree = n.GetChildren().size();
    childrenBits.clear();
    previousChildrenFixedCount.clear();

    for (unsigned i = 0; i < degree; i++)
    {
      FixedBits* cb = getOrCreate(n[i]);
      childrenBits.push_back(cb);
      previousChildrenFixedCount.push_back(cb->countFixed());
    }

    Result status = NO_CHANGE;
    if (SYMBOL != n.GetKind())
    {
      // Record before mutation so we can undo.
      if (currentLog)
      {
        recordBeforeMutation(n, nBits);
        for (unsigned i = 0; i < degree; i++)
          recordBeforeMutation(n[i], childrenBits[i]);
      }

      status = ConstantBitPropagation::dispatchToTransferFunctions(
          mgr, n.GetKind(), childrenBits, *nBits, n, msm);
    }

    if (CONFLICT == status)
    {
      conflict = true;
      return;
    }

    int newCount = nBits->countFixed();

    if (status != NO_CHANGE)
    {
      if (newCount != previousTop)
      {
        // Schedule all parents of n.
        if (dependencies)
        {
          auto range = dependencies->getDependents(n);
          for (const ASTNode& p : range)
            workList->push(p);
        }
      }

      for (unsigned i = 0; i < degree; i++)
      {
        if ((int)childrenBits[i]->countFixed() !=
            (int)previousChildrenFixedCount[i])
        {
          // Schedule all parents of this child except n.
          if (dependencies)
          {
            auto range = dependencies->getDependents(n[i]);
            for (const ASTNode& parent : range)
              if (!(parent == n))
                workList->push(parent);
          }
          workList->push(n[i]);
        }
      }
    }
  }
}

bool IncrementalCBP::addConstraints(const ASTNode& conjunction)
{
  if (conflict)
    return false;

  // Build dependencies and worklist for the new sub-DAG.
  // On first call, these are null; create them.
  if (!dependencies)
    dependencies = new Dependencies(conjunction);
  // TODO: extend dependencies for subsequent calls.
  // For now, rebuild from scratch if new nodes appear.

  if (!workList)
  {
    workList = new WorkList(conjunction);
  }
  else
  {
    // Seed the worklist with nodes from the new conjunction.
    workList->initWorkList(conjunction);
  }

  // Propagate from the newly-seeded nodes.
  propagate();

  return !conflict;
}

bool IncrementalCBP::setTopTrue(const ASTNode& top)
{
  if (conflict)
    return false;

  FixedBits* topFB = getOrCreate(top);

  if (currentLog)
    recordBeforeMutation(top, topFB);

  topFB->setFixed(0, true);
  topFB->setValue(0, true);

  if (workList)
    workList->push(top);

  propagate();
  return !conflict;
}

void IncrementalCBP::push()
{
  undoStack.push_back(std::vector<CBPUndoEntry>());
  currentLog = &undoStack.back();
}

void IncrementalCBP::pop()
{
  assert(!undoStack.empty());

  // Replay the undo log in reverse.
  std::vector<CBPUndoEntry>& log = undoStack.back();
  for (auto it = log.rbegin(); it != log.rend(); ++it)
  {
    if (it->wasNew)
    {
      // This node was created during this level — remove it.
      auto mapIt = fixedMap->map->find(it->node);
      if (mapIt != fixedMap->map->end())
      {
        delete mapIt->second;
        fixedMap->map->erase(mapIt);
      }
    }
    else
    {
      // Restore the old bits.
      auto mapIt = fixedMap->map->find(it->node);
      if (mapIt != fixedMap->map->end())
        *(mapIt->second) = it->oldBits;
    }
  }

  undoStack.pop_back();
  currentLog = undoStack.empty() ? nullptr : &undoStack.back();
  conflict = false;  // conflict at a pushed level doesn't infect the parent
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
      // Build the constant node.
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

bool IncrementalCBP::isConflict() const
{
  return conflict;
}

} // namespace stp
