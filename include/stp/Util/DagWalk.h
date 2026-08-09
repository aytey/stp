/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

#ifndef DAGWALK_H_
#define DAGWALK_H_

#include "stp/AST/ASTNode.h"
#include <deque>

namespace stp
{

// Rebuild a DAG bottom up, without putting the walk on the call stack.
//
// How deeply a formula nests is the input's choice, and inputs that nest
// thousands deep exist, so a pass that recurses once per level dies on them.
// This is the shape most of those passes have: visit a node's children, hand
// the node and its rebuilt children to `combine`, and use what comes back in
// place of the node. Frames live on the heap, so depth costs memory rather
// than stack.
//
// `combine(node, children)` returns the replacement for `node`. It is called
// once per node, after all of that node's children have been combined, and in
// left-to-right order, so it sees exactly what the equivalent recursive
// function saw and may call the node factory freely.
//
// `cache` maps a node to its replacement. A node reached twice is combined
// once, and a cache that outlives the call carries answers between calls. It
// needs find(), end() and insert(pair), which both ASTNodeMap and
// DenseNodeMap provide. Leaves have nothing to rebuild: they are returned as
// they are and are not cached.
//
// `combine` is a template parameter rather than a std::function so that it
// inlines: this runs once per node, and an indirect call per node would be a
// real cost on ordinary shallow input.
// What primeMemo should do with a node it has reached.
enum class Walk
{
  Descend, // walk this node's children, then hand it to visit
  Visit,   // hand it to visit without walking its children
  Skip     // ignore it: already done, or the pass never looks at it
};

// Fill a memoised pass's table from the bottom up, so that the pass itself
// stops recursing.
//
// The alternative to rewriting a pass as a state machine. A pass that
// answers from a memo at its first line, and reaches other nodes only by
// calling itself on their children, will find every child already answered
// if the table is filled bottom up first -- so its recursion never goes more
// than one level, whatever the input nests to, and not one line of it has to
// change. That is worth having for the passes that are too large to restate:
// BitBlaster::BBTerm dispatches on kind over 450 lines and calls itself from
// 24 of them.
//
// It is only sound where the pass would have visited these nodes anyway, in
// this order. Three things to check before using it:
//
//   * the memo is keyed on the node alone -- not on the node plus a flag,
//     the way the Simplifier keys on pushNeg as well;
//   * the pass has no early exit that skips children, or priming does work
//     it would not have done, building nodes that do not otherwise exist and
//     shifting every node number after them;
//   * `classify` returns Descend for exactly the nodes whose children the
//     pass looks at, and Skip for the ones it never passes down -- a
//     constant index operand, say, that its kind ignores.
//
// Get those right and the pass sees the same nodes built by the same factory
// calls in the same sequence. Check it with the generated CNF, which is
// sensitive to all three.
//
// Self-calls on nodes the pass builds itself, rather than on children, are
// fine and need nothing here: their operands are already primed, so those
// walks are shallow.
template <class Classify, class Visit>
void primeMemo(const ASTNode& top, Classify classify, Visit visit)
{
  if (classify(top) != Walk::Descend)
    return; // the caller does it: there is nothing below to get ahead of.

  struct Frame
  {
    ASTNode n;
    size_t i = 0;
  };

  // A deque, so descending never moves the frame being worked on.
  std::deque<Frame> stack;
  stack.push_back(Frame{top, 0});

  while (!stack.empty())
  {
    Frame& current = stack.back();

    if (current.i < current.n.Degree())
    {
      const ASTNode child = current.n[current.i++];

      switch (classify(child))
      {
        case Walk::Descend:
          stack.push_back(Frame{child, 0});
          break;
        case Walk::Visit:
          visit(child);
          break;
        case Walk::Skip:
          break;
      }
      continue;
    }

    // Children are all answered, so this returns after one level.
    visit(current.n);
    stack.pop_back();
  }
}

template <class Cache, class Combine>
ASTNode postOrderRebuild(const ASTNode& top, Cache& cache, Combine combine)
{
  // One node's progress: the children combined so far, and how far along its
  // own child list it has got.
  struct Frame
  {
    ASTNode n;
    ASTVec children;
    size_t i = 0;
    bool waiting = false; // a child is being combined below.

    Frame(const ASTNode& node) : n(node) { children.reserve(node.Degree()); }
  };

  ASTNode result;

  // Answers that need no frame, which is what the recursive form answered
  // without a call.
  auto known = [&cache, &result](const ASTNode& n) -> bool {
    if (n.Degree() == 0)
    {
      result = n;
      return true;
    }

    const auto it = cache.find(n);
    if (it != cache.end())
    {
      result = it->second;
      return true;
    }
    return false;
  };

  if (known(top))
    return result;

  // A deque, so descending never moves the frames above it: `current` stays
  // valid across a push.
  std::deque<Frame> stack;
  stack.emplace_back(top);

  while (true)
  {
    Frame& current = stack.back();

    if (current.waiting)
    {
      current.waiting = false;
      current.children.push_back(result);
      current.i++;
    }

    bool descended = false;
    while (current.i < current.n.Degree())
    {
      if (known(current.n[current.i]))
      {
        current.children.push_back(result);
        current.i++;
        continue;
      }

      // Nothing above may be read after this push.
      current.waiting = true;
      stack.emplace_back(current.n[current.i]);
      descended = true;
      break;
    }

    if (descended)
      continue;

    result = combine(current.n, current.children);
    cache.insert({current.n, result});

    stack.pop_back();
    if (stack.empty())
      return result;
  }
}
}

#endif /* DAGWALK_H_ */
