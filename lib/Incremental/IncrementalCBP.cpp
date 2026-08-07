/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
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

/* Per-call constant-bit propagation for the incremental driver; see
 * the header for the contract. The worklist scheme follows the batch
 * WorkList (cheap transfer functions drain before expensive ones);
 * the transfer functions themselves ARE the batch ones, reached
 * through ConstantBitPropagation::dispatchToTransferFunctions, so the
 * bit-level reasoning is shared with the batch pipeline verbatim.
 */

#include "stp/Incremental/IncrementalCBP.h"

#include "stp/AST/AST.h"
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"

#include "extlib-constbv/constantbv.h"

using simplifier::constantBitP::ConstantBitPropagation;
using simplifier::constantBitP::FixedBits;
using simplifier::constantBitP::MultiplicationStatsMap;
using simplifier::constantBitP::NodeToFixedBitsMap;
using simplifier::constantBitP::Result;

namespace stp
{

IncrementalCBP::IncrementalCBP(STPMgr* mgr_, NodeFactory* nf_)
    : mgr(mgr_), nf(nf_), fixedMap(new NodeToFixedBitsMap(1000)),
      msm(new MultiplicationStatsMap()), conflict(false)
{
}

IncrementalCBP::~IncrementalCBP()
{
  delete fixedMap;
  delete msm;
}

void IncrementalCBP::extendParentMap(const ASTNode& root)
{
  std::vector<ASTNode> stack;
  stack.push_back(root);

  while (!stack.empty())
  {
    const ASTNode n = stack.back();
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

void IncrementalCBP::pushWork(const ASTNode& n)
{
  if (n.isConstant())
    return;
  switch (n.GetKind())
  {
    case BVMULT:
    case BVPLUS:
    case BVDIV:
    case BVMOD:
    case SBVDIV:
    case SBVREM:
    case SBVMOD:
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
    const ASTNode n = *cheapWork.begin();
    cheapWork.erase(cheapWork.begin());
    return n;
  }
  const ASTNode n = *expensiveWork.begin();
  expensiveWork.erase(expensiveWork.begin());
  return n;
}

bool IncrementalCBP::workEmpty() const
{
  return cheapWork.empty() && expensiveWork.empty();
}

// Seed the worklist with the sub-DAG's nodes that have at least one
// KNOWN child: a syntactic constant (the batch WorkList's initial
// population rule), or a node an earlier level's feed already fixed
// bits of. The batch pass sees the whole formula in one feed and
// needs only the syntactic rule; here a deeper level's fresh DAG must
// pick up what the shallower feeds already know, or a cross-level
// fixing would only reach nodes that happen to also carry a constant
// child.
void IncrementalCBP::seedWorklist(const ASTNode& n)
{
  ASTNodeSet visited;
  std::vector<ASTNode> stack;
  stack.push_back(n);

  while (!stack.empty())
  {
    const ASTNode node = stack.back();
    stack.pop_back();

    if (node.isConstant())
      continue;
    if (!visited.insert(node).second)
      continue;

    bool hasKnownChild = false;
    for (unsigned i = 0; i < node.Degree(); i++)
    {
      const ASTNode& child = node[i];
      if (child.isConstant())
        hasKnownChild = true;
      else if (!hasKnownChild)
      {
        NodeToFixedBitsMap::NodeToFixedBitsMapType::const_iterator it =
            fixedMap->map->find(child);
        if (it != fixedMap->map->end() && it->second->countFixed() > 0)
          hasKnownChild = true;
      }
      stack.push_back(child);
    }
    if (hasKnownChild)
      pushWork(node);
  }
}

FixedBits* IncrementalCBP::getOrCreate(const ASTNode& n)
{
  NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it =
      fixedMap->map->find(n);
  if (it != fixedMap->map->end())
    return it->second;

  const int bw = (n.GetValueWidth() == 0) ? 1 : n.GetValueWidth();
  FixedBits* fb = new FixedBits(bw, BOOLEAN_TYPE == n.GetType());

  if (BVCONST == n.GetKind())
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
  return fb;
}

void IncrementalCBP::scheduleParents(const ASTNode& n, const ASTNode& except)
{
  const std::map<uint64_t, std::vector<ASTNode>>::const_iterator it =
      parentMap.find(n.GetNodeNum());
  if (it == parentMap.end())
    return;
  for (const ASTNode& p : it->second)
    if (!(p == except))
      pushWork(p);
}

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
    const unsigned previousTop = nBits->countFixed();
    const bool topWasTotal = nBits->isTotallyFixed();

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
      status = ConstantBitPropagation::dispatchToTransferFunctions(
          mgr, n.GetKind(), childBits, *nBits, n, msm);

    if (simplifier::constantBitP::CONFLICT == status)
    {
      conflict = true;
      return;
    }

    if (status == simplifier::constantBitP::NO_CHANGE)
      continue;

    if (nBits->countFixed() != previousTop)
    {
      scheduleParents(n, n);
      if (!topWasTotal && nBits->isTotallyFixed())
        newlyFixed.push_back(n);
    }
    for (unsigned i = 0; i < degree; i++)
    {
      if (childBits[i]->countFixed() != prevChildCounts[i])
      {
        scheduleParents(n[i], n);
        pushWork(n[i]);
        const bool wasTotal = prevChildCounts[i] == childBits[i]->getWidth();
        if (!wasTotal && childBits[i]->isTotallyFixed() &&
            !n[i].isConstant())
          newlyFixed.push_back(n[i]);
      }
    }
  }
}

bool IncrementalCBP::feedLevel(const ASTNode& conjunction)
{
  if (conflict)
    return false;

  newlyFixed.clear();

  extendParentMap(conjunction);
  seedWorklist(conjunction);

  // The level is asserted for the whole call, so its truth is a sound
  // assumption for every consequence drawn this call. The AND transfer
  // function pushes the truth down to every conjunct from here.
  FixedBits* topBits = getOrCreate(conjunction);
  if (conjunction.GetType() == BOOLEAN_TYPE && !topBits->isTotallyFixed())
  {
    topBits->setFixed(0, true);
    topBits->setValue(0, true);
    // The assumption is a fixing like any other: a single-conjunct
    // level's conjunction IS the conjunct (a bare flag, say), and its
    // deep occurrences fold only if the caller sees it. The caller's
    // slot protection and fed-conjunct fact rules handle the rest.
    newlyFixed.push_back(conjunction);
  }
  pushWork(conjunction);

  propagate();
  return !conflict;
}

ASTNode IncrementalCBP::constantOf(const ASTNode& n) const
{
  if (n.isConstant())
    return ASTNode();
  if (n.GetType() != BOOLEAN_TYPE && n.GetType() != BITVECTOR_TYPE)
    return ASTNode();
  const NodeToFixedBitsMap::NodeToFixedBitsMapType::const_iterator it =
      fixedMap->map->find(n);
  if (it == fixedMap->map->end() || !it->second->isTotallyFixed())
    return ASTNode();

  const FixedBits& bits = *it->second;
  // The conversion bitsToNode performs, on this engine's factory.
  if (n.GetType() == BOOLEAN_TYPE)
    return bits.getValue(0) ? nf->getTrue() : nf->getFalse();
  return nf->CreateConstant(bits.GetBVConst(), n.GetValueWidth());
}

} // namespace stp
