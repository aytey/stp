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
#include <cassert>
#include <cstdint>
#include <deque>
#include <iostream>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

namespace stp
{

// What primeMemo should do with a node it has reached.
enum class Walk
{
  Descend, // walk this node's children, then hand it to visit
  Visit,   // hand it to visit without walking its children
  Skip     // ignore it: already done, or the pass never looks at it
};

// Whether a pass whose memo is primed still nests with its input.
//
// That is the whole of what priming buys: the pass's calls on its operands
// answer from the memo, so its own recursion is a couple of levels whatever
// the input nests to. It buys it only where the walk reaches the nodes the
// pass reaches, and nothing in the type system says a pass qualifies -- the
// preconditions live in a comment on primeMemo below and in whoever reads it.
//
// So the pass reports the nodes it runs, and the depth they reach is held
// against what the pass claims. A classify() or an operands() that stops
// short of a subtree does not stop the pass going there: it goes down its own
// call stack for it, one frame per level, which is the crash priming exists
// to prevent -- and which nothing in the output can show, because the answer
// is the same. This is the check for that, and it runs on every query an
// assertions build sees rather than on the ones somebody remembers to
// measure.
//
// The depth a pass is allowed is its own claim, made where it declares its
// audit. It is not one or two: a pass legitimately re-enters on nodes it has
// just built -- a rewritten node, a pulled-up if-then-else -- and those calls
// nest as deeply as the rewriting does, which is a property of the rules and
// not of the input. What it may not do is nest in proportion to the input,
// and the gap between those two is wide enough to sit a limit in.
//
// What this does not check is the other half: priming that reaches more than
// the pass would have, which costs nodes that do not otherwise exist rather
// than stack. That one is invisible from inside a primed run -- priming *is*
// the pass running, so every node primed has, by then, been reached -- and it
// belongs to tests/prime-memos-differential.py, which solves each query both
// ways and compares the CNF. Its weakness is known and written down there.
#ifndef NDEBUG
class PrimeAudit
{
  const char* pass;
  size_t limit;

  size_t running = 0; // how deep the pass's own calls are nested
  size_t deepest = 0;

public:
  // `pass_` names the pass in a report, `limit_` is how deeply it says it
  // nests once its memo is primed.
  PrimeAudit(const char* pass_, const size_t limit_)
      : pass(pass_), limit(limit_)
  {
  }

  // The pass is running `n`, from whatever it was running before. One of
  // these at the head of the pass's own entry point is the whole instrument.
  class Running
  {
    PrimeAudit& audit;
    bool active;

  public:
    // `active_` is false only for the deliberately recursive side of the
    // on/off differential: that run is a baseline, not a failed priming.
    Running(PrimeAudit& audit_, const ASTNode&, bool active_ = true)
        : audit(audit_), active(active_)
    {
      if (!active)
        return;
      audit.running++;
      if (audit.running > audit.deepest)
        audit.deepest = audit.running;
    }

    Running(const Running&) = delete;
    Running& operator=(const Running&) = delete;

    ~Running()
    {
      if (!active)
        return;
      audit.running--;
      if (audit.running == 0)
        audit.finished();
    }
  };

  // Empty while the pass is within its claim. Public so that a test can drive
  // the audit directly rather than by breaking a pass.
  std::string disagreement() const
  {
    std::ostringstream out;

    if (deepest > limit)
      out << pass << " nested " << deepest << " deep, over its claim of "
          << limit << ": priming is not answering the calls it makes on its "
          << "operands, so the input's depth is back on the stack\n";

    return out.str();
  }

  size_t depth() const { return deepest; }

  void clear() { deepest = 0; }

private:
  void finished()
  {
    const std::string bad = disagreement();
    if (!bad.empty())
    {
      std::cerr << "primeMemo preconditions violated (stp/Util/DagWalk.h):\n"
                << bad;
      assert(false && "a primed pass nests with its input after all");
    }
    clear();
  }
};
#else
// Release: the same shape, doing nothing, so the passes read the same in
// both builds.
class PrimeAudit
{
public:
  PrimeAudit(const char*, size_t) {}
  void clear() {}

  class Running
  {
  public:
    Running(PrimeAudit&, const ASTNode&, bool = true) {}
  };
};
#endif

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
// Self-calls on nodes the pass builds itself, rather than on children, get
// nothing from this: those nodes do not exist when the walk runs. Usually
// that costs nothing, because their operands are primed and the walk is one
// level -- but it is an assumption about the pass's own rewriting and not
// something priming secures, and it does not always hold. The simplifier's
// float arm builds a term thousands of levels deep and walks down it: see the
// note on Simplifier::termAudit, and the depth check below, which is what
// found it.
// A pass normally recurses into all of a node's children, in order. The few
// exceptions in STP recurse into a contiguous subrange, or into all children
// in reverse order. WalkOperands describes those cases without copying an
// ASTNode or allocating an operand vector. `operands(n)` returns the view for
// n; the three-argument primeMemo below supplies WalkOperands::all(n).
class WalkOperands
{
  uint32_t first_ = 0;
  uint32_t count_ = 0;
  bool reversed_ = false;

  WalkOperands(const size_t first, const size_t count, const bool reversed)
      : first_(static_cast<uint32_t>(first)),
        count_(static_cast<uint32_t>(count)), reversed_(reversed)
  {
    assert(first == first_ && count == count_);
  }

public:
  static WalkOperands all(const ASTNode& n) { return range(0, n.Degree()); }

  static WalkOperands range(const size_t first, const size_t pastLast)
  {
    assert(first <= pastLast);
    return WalkOperands(first, pastLast - first, false);
  }

  static WalkOperands reversed(const ASTNode& n)
  {
    return reversedRange(0, n.Degree());
  }

  static WalkOperands reversedRange(const size_t first, const size_t pastLast)
  {
    assert(first <= pastLast);
    return WalkOperands(first, pastLast - first, true);
  }

  size_t size() const { return count_; }

  const ASTNode& at(const ASTNode& n, const size_t i) const
  {
    assert(i < count_ && static_cast<size_t>(first_) + count_ <= n.Degree());
    return n[first_ + (reversed_ ? count_ - 1 - i : i)];
  }
};

// Proof supplied to visit that classify admitted this node. A memoised pass
// may use it as a known-miss token when (as all current primed passes do) its
// classifier returns Visit or Descend only after finding no memo entry. That
// removes the otherwise duplicate lookup at the pass's first line.
//
// The contract is deliberately explicit: processing descendants must not
// memoise an ancestor as a side effect. A bottom-up pass over an acyclic AST
// normally only records the node it was handed, which is exactly that case.
struct PrimeMemoReady
{
};

template <class Classify, class Operands, class Visit>
void primeMemo(const ASTNode& top, Classify classify, Operands operands,
               Visit visit)
{
  if (classify(top) != Walk::Descend)
    return; // the caller does it: there is nothing below to get ahead of.

  struct Frame
  {
    ASTNode n;
    WalkOperands operands;
    uint32_t i = 0;

    Frame(const ASTNode& node, const WalkOperands view)
        : n(node), operands(view)
    {
    }
  };

  auto open = [&](const ASTNode& n) { return Frame(n, operands(n)); };

  // Keep the current frame inline. The parent vector is not allocated at all
  // when the root's operands are leaves or memo hits, which is the common
  // shallow case; deep input still grows geometrically on the heap.
  Frame current = open(top);
  std::vector<Frame> parents;

  while (true)
  {
    if (current.i < current.operands.size())
    {
      const ASTNode& child = current.operands.at(current.n, current.i++);

      switch (classify(child))
      {
        case Walk::Descend:
          parents.push_back(std::move(current));
          current = open(child);
          break;
        case Walk::Visit:
          visit(child, PrimeMemoReady{});
          break;
        case Walk::Skip:
          break;
      }
      continue;
    }

    // Operands are all answered, so this returns after one level.
    visit(current.n, PrimeMemoReady{});
    if (parents.empty())
      return;

    current = std::move(parents.back());
    parents.pop_back();
  }
}

// The usual case: a pass recurses into a node's own children.
template <class Classify, class Visit>
void primeMemo(const ASTNode& top, Classify classify, Visit visit)
{
  primeMemo(
      top, classify, [](const ASTNode& n) { return WalkOperands::all(n); },
      visit);
}

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
