/********************************************************************
 * AUTHORS: Trevor Hansen
 *
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

#include "stp/Simplifier/Flatten.h"
#include <list>
#include <deque>
#include <vector>

namespace stp
{

  ASTNode Flatten::topLevel(ASTNode& n)
  {
    stpMgr->GetRunTimes()->start(RunTimes::Flatten);
    
    removed=0;
    top_removed = 0;

    buildShareCount(n);
    

    // If the top level is an AND, we want to flatten it irrespective of sharing.
    ASTNode result = flatten(n, (AND == n.GetKind()));
    
    if (stpMgr->UserFlags.stats_flag)
    {
      std::cerr << "{Flatten} Internal nodes removed:" << removed << std::endl;
      std::cerr << "{Flatten} Top nodes removed:" << top_removed << std::endl;
    }

    shareCount.clear();
    fromTo.clear();

    stpMgr->GetRunTimes()->stop(RunTimes::Flatten);
    return result;
  }

  // counter is 1 if the node has one reference in the tree.
  //
  // Iterative for the same reason as Rewriting::buildShareCount, which this
  // mirrors: the input decides the depth, so a call per level of the DAG
  // exhausts the stack. The stack holds pointers into each node's own child
  // storage, which the node above keeps alive for the whole walk.
  void Flatten::buildShareCount(const ASTNode& n)
  {
    std::vector<const ASTNode*> toVisit;
    toVisit.push_back(&n);

    while (!toVisit.empty())
    {
      const ASTNode& current = *toVisit.back();
      toVisit.pop_back();

      if (current.Degree() == 0)
        continue;

      if (shareCount[current.GetNodeNum()]++ > 0) // 0 first time, 1 second.
        continue;

      // Reverse, so children are still visited left to right.
      const ASTChildren children = current.GetChildren();
      for (size_t i = children.size(); i > 0; i--)
        toVisit.push_back(&children[i - 1]);
    }
  }

  // A leaf, or a node already flattened: answered without a frame, exactly
  // as the recursive version answered it without a call.
  bool Flatten::alreadyKnown(const ASTNode& n, ASTNode& answer)
  {
    if (n.Degree() == 0)
    {
      answer = n;
      return true;
    }

    const auto it = fromTo.find(n.GetNodeNum());
    if (it != fromTo.end())
    {
      answer = it->second;
      return true;
    }
    return false;
  }

  // The walk one node is part-way through. Everything here was a local of
  // the recursive flatten(); it lives on the heap because the input decides
  // how many of them are live at once.
  struct Flatten::Frame
  {
    ASTNode n;
    Kind k;
    bool top;
    bool flattenable;
    bool changed = false;

    ASTChildren children;
    unsigned it0 = 0; // original children consumed
    unsigned i = 0;   // position in nextChildren

    ASTVec newChildren;
    ASTVec nextChildren;
    std::unordered_set<uint64_t> seen;

    // Set while this node waits for a child's flatten() to come back.
    ASTNode pending;
    bool waiting = false;

    Frame(const ASTNode& n_, bool top_)
        : n(n_), k(n_.GetKind()), top(top_),
          //TODO STP doesn't currerntly handle >2 arity BVMULT.
          flattenable(OR == k || AND == k || XOR == k || BVXOR == k ||
                      BVOR == k || BVAND == k || BVPLUS == k),
          children(n_.GetChildren())
    {
    }
  };

  ASTNode Flatten::flatten(const ASTNode& n, bool top)
  {
    ASTNode result;
    if (alreadyKnown(n, result))
      return result;

    // A deque, so that descending into a child never moves the frames
    // above it: `current` below stays valid across a push.
    std::deque<Frame> stack;
    stack.emplace_back(n, top);

    // Copy on write.
    auto fill = [](Frame& f)
    {
      assert(0 == f.i);

      f.newChildren.reserve(f.children.size());
      f.newChildren.insert(f.newChildren.end(), f.children.begin(),
                           f.children.begin() + (f.it0 - 1));
      f.changed = true;
    };

    while (true)
    {
      Frame& current = stack.back();

      // Pick up the child this frame descended for. `result` is what its
      // flatten() returned.
      if (current.waiting)
      {
        if (result != current.pending && !current.changed)
          fill(current);
        if (current.changed)
          current.newChildren.push_back(result);
        current.waiting = false;
      }

      bool descended = false;

      while (current.it0 < current.children.size() ||
             current.i < current.nextChildren.size())
      {
        // By value: the flattening branch below appends to nextChildren,
        // which can move what a reference into it points at.
        const ASTNode c = (current.it0 < current.children.size())
                              ? current.children[current.it0++]
                              : current.nextChildren[current.i++];

        if (current.flattenable && c.GetKind() == current.k &&
            (current.top || shareCount[c.GetNodeNum()] == 1))
        {
          assert(c.Degree() > 1);
          if (!current.changed)
            fill(current);

          if (current.top)
            top_removed++;
          else
            removed++;

          for (const auto& e : c.GetChildren())
          {
            if (BVAND == current.k || AND == current.k || BVOR == current.k ||
                OR == current.k)
            {
              if (!current.seen.insert(e.GetNodeNum()).second)
                continue;
            }
            current.nextChildren.push_back(e);
          }
          shareCount[c.GetNodeNum()]--;
        }
        else
        {
          ASTNode r;
          if (alreadyKnown(c, r))
          {
            if (r != c && !current.changed)
              fill(current);
            if (current.changed)
              current.newChildren.push_back(r);
            continue;
          }

          // Where the recursive version called flatten(c). Nothing above
          // may be read after the push.
          current.pending = c;
          current.waiting = true;
          stack.emplace_back(c, false);
          descended = true;
          break;
        }
      }

      if (descended)
        continue;

      Frame& done = stack.back();
      result = done.n;

      if (done.changed)
      {
        assert(done.n.Degree() <= done.newChildren.size());

        if (done.n.GetType() == BOOLEAN_TYPE)
          result = nf->CreateNode(done.k, done.newChildren);
        else
          result = nf->CreateArrayTerm(done.k, done.n.GetIndexWidth(),
                                       done.n.GetValueWidth(),
                                       done.newChildren);

        shareCount[result.GetNodeNum()]++; // I'm guessing it's unusal, but we might make a node we already have.
      }

      if (shareCount[done.n.GetNodeNum()] > 1)
        fromTo.insert({done.n.GetNodeNum(), result});

      stack.pop_back();
      if (stack.empty())
        return result;
    }
  }
}
