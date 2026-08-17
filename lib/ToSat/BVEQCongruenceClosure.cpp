#include "stp/ToSat/BVEQCongruenceClosure.h"

namespace stp
{

void BVEQCongruenceClosure::init(unsigned n)
{
  parent_.resize(n);
  rank_.resize(n, 0);
  parentEdge_.resize(n, -1);
  for (unsigned i = 0; i < n; ++i)
    parent_[i] = i;
}

unsigned BVEQCongruenceClosure::find(unsigned x)
{
  while (parent_[x] != x)
    x = parent_[x];
  return x;
}

void BVEQCongruenceClosure::unite(unsigned x, unsigned y, unsigned eqIdx)
{
  unsigned rx = find(x);
  unsigned ry = find(y);
  if (rx == ry)
    return;
  if (rank_[rx] < rank_[ry])
  {
    parent_[rx] = ry;
    parentEdge_[rx] = eqIdx;
  }
  else if (rank_[rx] > rank_[ry])
  {
    parent_[ry] = rx;
    parentEdge_[ry] = eqIdx;
  }
  else
  {
    parent_[ry] = rx;
    parentEdge_[ry] = eqIdx;
    rank_[rx]++;
  }
}

void BVEQCongruenceClosure::pathToRoot(unsigned x, std::vector<unsigned>& path)
{
  while (parent_[x] != x)
  {
    path.push_back(parentEdge_[x]);
    x = parent_[x];
  }
}

unsigned BVEQCongruenceClosure::check(
    const std::vector<EqInfo>& equalities, SATSolver& solver)
{
  if (equalities.empty())
    return 0;

  unsigned maxNode = 0;
  for (const auto& eq : equalities)
  {
    if (eq.left > maxNode) maxNode = eq.left;
    if (eq.right > maxNode) maxNode = eq.right;
  }
  init(maxNode + 1);

  for (unsigned i = 0; i < equalities.size(); ++i)
  {
    if (equalities[i].modelTrue)
      unite(equalities[i].left, equalities[i].right, i);
  }

  unsigned conflicts = 0;
  for (unsigned i = 0; i < equalities.size(); ++i)
  {
    if (equalities[i].modelTrue)
      continue;

    unsigned rl = find(equalities[i].left);
    unsigned rr = find(equalities[i].right);
    if (rl != rr)
      continue;

    std::vector<unsigned> pathL, pathR;
    pathToRoot(equalities[i].left, pathL);
    pathToRoot(equalities[i].right, pathR);

    SATSolver::vec_literals cl;
    for (unsigned idx : pathL)
      cl.push(SATSolver::mkLit(equalities[idx].satVar, true));
    for (unsigned idx : pathR)
      cl.push(SATSolver::mkLit(equalities[idx].satVar, true));
    cl.push(SATSolver::mkLit(equalities[i].satVar, false));
    solver.addClause(cl);

    conflicts++;
  }
  return conflicts;
}

} // namespace stp
