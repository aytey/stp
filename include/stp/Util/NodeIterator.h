/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Jan, 2012
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

#ifndef NODEITERATOR_H_
#define NODEITERATOR_H_

#include "stp/AST/ASTNode.h"
#include "stp/STPManager/STPManager.h"
#include <limits>
#include <vector>

namespace stp
{
// Returns each node once, then returns the sentinel.
// NB if the sentinel is contained in the node that's passed, then it'll be
// wrong.
class NodeIterator // not copyable
{
  struct Frame
  {
    ASTNode node;
    // `unentered` means the node itself has not been returned yet. Once it
    // has, this is the number of children still to visit, in reverse order
    // to retain NodeIterator's historical LIFO traversal.
    size_t nextChild = unentered;

    static constexpr size_t unentered =
        std::numeric_limits<size_t>::max();

    explicit Frame(const ASTNode& n) : node(n) {}
  };
  static_assert(sizeof(Frame) <= 2 * sizeof(void*),
                "NodeIterator frames must contain only traversal state");

  // Continuations retain one frame per active ancestor. The former pending
  // node stack retained every unvisited sibling along the frontier, which
  // made a shallow, very wide node allocate in proportion to its degree.
  std::vector<Frame> path;

  const ASTNode& sentinel;
  uint8_t iteration;

protected:
  // The generic iterator retains its historical virtual `ok` hook. Known
  // built-in filters call this templated core directly, letting their
  // predicate inline into the walk instead of paying an indirect call for
  // every node.
  template <typename Accept>
  ASTNode nextIf(Accept&& accept)
  {
    while (!path.empty())
    {
      Frame& frame = path.back();
      if (frame.nextChild == Frame::unentered)
      {
        frame.nextChild = frame.node.Degree();
        ASTNode result = frame.node;

        if (!accept(result) || result.getIteration() == iteration)
        {
          path.pop_back();
          continue;
        }

        if (result == sentinel)
        {
          path.pop_back();
          return result;
        }

        result.setIteration(iteration);
        return result;
      }

      if (frame.nextChild == 0)
      {
        path.pop_back();
        continue;
      }

      const ASTNode& child = frame.node[--frame.nextChild];
      if (child.getIteration() != iteration)
        path.emplace_back(child);
    }

    return sentinel;
  }

public:
  NodeIterator(const ASTNode& n, const ASTNode& _sentinel, STPMgr& stpMgr)
      : sentinel(_sentinel), iteration(stpMgr.getNextIteration())
  {
    path.emplace_back(n);
  }

  ASTNode next()
  {
    return nextIf([this](const ASTNode& n) { return ok(n); });
  }

  ASTNode end() { return sentinel; }

  virtual bool ok(const ASTNode& /*n*/) { return true; }
};

// Iterator that omits return atoms.
class NonAtomIterator final : public NodeIterator
{
  bool ok(const ASTNode& n) override { return !n.isAtom(); }

public:
  NonAtomIterator(const ASTNode& n, const ASTNode& uf, STPMgr& stpMgr)
      : NodeIterator(n, uf, stpMgr)
  {
  }

  ASTNode next()
  {
    return nextIf([](const ASTNode& n) { return !n.isAtom(); });
  }
};
}

#endif /* NODEITERATOR_H_ */
