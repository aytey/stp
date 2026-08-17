#ifndef BVEQ_CONGRUENCE_CLOSURE_H
#define BVEQ_CONGRUENCE_CLOSURE_H

#include "stp/Sat/SATSolver.h"
#include <vector>

namespace stp
{

class BVEQCongruenceClosure
{
public:
  struct EqInfo
  {
    unsigned left;
    unsigned right;
    unsigned satVar;
    bool modelTrue;
  };

  unsigned check(const std::vector<EqInfo>& equalities, SATSolver& solver);

private:
  std::vector<unsigned> parent_;
  std::vector<unsigned> rank_;
  std::vector<int> parentEdge_;

  void init(unsigned n);
  unsigned find(unsigned x);
  void unite(unsigned x, unsigned y, unsigned eqIdx);
  void pathToRoot(unsigned x, std::vector<unsigned>& path);
};

} // namespace stp

#endif
