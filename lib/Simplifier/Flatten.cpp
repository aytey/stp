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

  ASTNode Flatten::flatten(const ASTNode& n, bool top)
  {
    if (n.Degree() == 0)
      return n;

    if (fromTo.find(n.GetNodeNum()) != fromTo.end())
      return fromTo[n.GetNodeNum()];

    const Kind k = n.GetKind();

    ASTNode result =n;

    bool changed =false;
    
    //TODO STP doesn't currerntly handle >2 arity BVMULT.
    const bool flattenable = (OR==k || AND==k || XOR==k || BVXOR==k ||  BVOR==k || BVAND==k || BVPLUS==k);

    std::unordered_set<uint64_t> seen;

    ASTVec newChildren;

    const ASTChildren children = n.GetChildren();
    auto it0 = children.begin();

    ASTVec nextChildren;
    unsigned i = 0;

    // Copy on write.
    auto fill = [&]
    {
      assert(0 ==i);

      newChildren.reserve(children.size());
      newChildren.insert(newChildren.end(), children.begin(), it0-1);
      changed=true;
    };

    while (it0 != children.end() || i < nextChildren.size())
    {
      const ASTNode c = (it0 != children.end())? *it0++: nextChildren[i++];

      if (flattenable && c.GetKind() == k && (top || shareCount[c.GetNodeNum()] == 1))
      {
         assert(c.Degree() > 1);
         if (!changed)
            fill();

         if (top)
            top_removed++;
         else
           removed++;

         for (const auto&e: c.GetChildren())
         {
            if (BVAND == k || AND == k || BVOR == k || OR == k)
            {
              if (!seen.insert(e.GetNodeNum()).second)
                continue; 
            }
            nextChildren.push_back(e);
         }
        shareCount[c.GetNodeNum()]--;
      }
      else
      {
        const auto r = flatten(c);
        if (r!=c && !changed)
          fill();
        if (changed)   
          newChildren.push_back(r);
      }
    }    

    if (changed)
    {
      assert(n.Degree() <= newChildren.size());

      if (n.GetType() == BOOLEAN_TYPE)
        result = nf->CreateNode(k, newChildren);
      else
        result = nf->CreateArrayTerm(k, n.GetIndexWidth(),n.GetValueWidth(), newChildren);

      shareCount[result.GetNodeNum()]++; // I'm guessing it's unusal, but we might make a node we already have.
    }

    if (shareCount[n.GetNodeNum()] > 1)
      fromTo.insert({n.GetNodeNum(),result});
    return result;
  }
}
