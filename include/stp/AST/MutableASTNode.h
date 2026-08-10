/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Feb 14, 2011
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

/*
 *  This is mutable unlike the normal ASTNode. It can be converted lazily to a
 * ASTNode.
 */

#ifndef MUTABLEASTNODE_H_
#define MUTABLEASTNODE_H_
#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include <deque>

namespace stp
{
class MutableASTNode
{
  static THREAD_LOCAL_IE vector<MutableASTNode*> all;

  // Symbols that must never be reported unconstrained, however few
  // occurrences they have in this graph. The active array-equality solve
  // uses them as proxy/witness/name anchors or as leaves of future
  // refinement lemmas, whose meanings and SAT variables must survive this
  // pass.
  // A caller that rewrites the graph on the strength of
  // isUnconstrained() would delete such a definition, and the
  // substitution map's refusal to record the replacement comes too
  // late to undo it. Installed for the duration of a pass; NULL means
  // no restriction.
  static THREAD_LOCAL_IE const std::set<ASTNode>* untouchable;

public:
  // Scoped installer for the untouchable set; restores the previous
  // value so passes cannot leak the restriction into each other.
  class UntouchableScope
  {
    const std::set<ASTNode>* saved;

  public:
    explicit UntouchableScope(const std::set<ASTNode>* s) : saved(untouchable)
    {
      untouchable = s;
    }
    ~UntouchableScope() { untouchable = saved; }
    UntouchableScope(const UntouchableScope&) = delete;
    UntouchableScope& operator=(const UntouchableScope&) = delete;
  };

  static bool isUntouchable(const ASTNode& n)
  {
    return untouchable != NULL && untouchable->find(n) != untouchable->end();
  }

  typedef std::unordered_set<MutableASTNode*> ParentsType;
  ParentsType parents;

  MutableASTNode(const MutableASTNode&) = delete;  
  MutableASTNode& operator=(const MutableASTNode&) = delete;

private:

  MutableASTNode(const ASTNode& n_) : n(n_) { dirty = false; }

  /* Make a mutable ASTNode graph like the ASTNode one, but with pointers back
   * up too. It's convoluted because we want a post order traversal. The root
   * node of a sub-tree will be created after its children.
   */

  // The walk keeps its frames on the heap. How deeply a formula nests is the
  // input's choice, and deeply nested ones exist, so a call per level of the
  // DAG exhausts the stack: unconstrained-variable elimination builds this
  // graph for every query, and a 30,000-deep alternation of NOT and AND died
  // here. See DeepDag_Test.cpp.
  //
  // A node is answered from `visited` or it is built, and building always
  // records it -- so a frame that has just descended finds its child there on
  // the way round, and no frame has to remember what it was waiting for.
  struct Frame
  {
    ASTNode n;
    size_t i = 0;
    vector<MutableASTNode*> tempChildren;

    Frame(const ASTNode& node) : n(node)
    {
      tempChildren.reserve(node.Degree());
    }
  };

public:
  static MutableASTNode* build(const ASTNode& n,
                               std::unordered_map<uint64_t, MutableASTNode*>& visited)
  {
    MutableASTNode* result = NULL;

    // What the recursive version answered without a call.
    auto known = [&visited, &result](const ASTNode& node) {
      const auto it = visited.find(node.GetNodeNum());
      if (it == visited.end())
        return false;
      result = it->second;
      return true;
    };

    if (known(n))
      return result;

    // A deque, so descending never moves the frames above it: `current`
    // stays valid across a push.
    std::deque<Frame> stack;
    stack.emplace_back(n);

    while (true)
    {
      Frame& current = stack.back();

      bool descended = false;
      while (current.i < current.n.Degree())
      {
        if (known(current.n[current.i]))
        {
          current.tempChildren.push_back(result);
          current.i++;
          continue;
        }

        // Nothing above may be read after this push.
        stack.emplace_back(current.n[current.i]);
        descended = true;
        break;
      }

      if (descended)
        continue;

      // Same order as the recursion: every child built, then the node, then
      // the parent links, then the entry that makes it answerable.
      MutableASTNode* mut = createNode(current.n);

      for (size_t i = 0; i < current.tempChildren.size(); i++)
      {
        current.tempChildren[i]->parents.insert(mut);
      }

      mut->children.insert(mut->children.end(), current.tempChildren.begin(),
                           current.tempChildren.end());
      visited.insert(std::make_pair(current.n.GetNodeNum(), mut));

      result = mut;
      stack.pop_back();
      if (stack.empty())
        return result;
    }
  }

private:
  bool dirty;

public:
  bool checkInvariant()
  {
    // Symbols have no children.
    if (n.GetKind() == SYMBOL)
    {
      assert(children.size() == 0);
    }

    // all my parents have me as a child.
    for (ParentsType::iterator it = parents.begin(); it != parents.end(); it++)
    {
      vector<MutableASTNode*>::iterator it2 = (*it)->children.begin();
      // Only consumed by the assert, which an NDEBUG build compiles out.
      [[maybe_unused]] bool found = false;
      for (; it2 != (*it)->children.end(); it2++)
      {
        assert(*it2 != NULL);
        if (*it2 == this)
          found = true;
      }
      assert(found);
    }

    for (size_t i = 0; i < children.size(); i++)
    {
      // call check on all the children.
      children[i]->checkInvariant();

      // all my children have me as a parent.
      assert(children[i]->parents.find(this) != children[i]->parents.end());
    }

    return true; // ignored.
  }

  MutableASTNode& getParent()
  {
    assert(parents.size() == 1);
    return **(parents.begin());
  }

  ASTNode toASTNode(stp::STPMgr* stpMgr)
  {
    if (!dirty)
      return n;

    if (children.size() == 0)
      return n;

    ASTVec newChildren;
    for (size_t i = 0; i < children.size(); i++)
      newChildren.push_back(children[i]->toASTNode(stpMgr));

    // Don't use the simplifying node factory here. Imagine CreateNode simplified
    // down,
    // from (= 1 ite( x , 1,0)) to x (say). Then this node will become a symbol,
    // but, this object will still have the equal's children. i.e. 1, and the
    // ITE.
    // So it becomes a SYMBOL with children...

    if (n.GetType() == BOOLEAN_TYPE)
    {
      n = stpMgr->hashingNodeFactory->CreateNode(n.GetKind(), newChildren);
    }
    else if (n.GetType() == BITVECTOR_TYPE)
    {
      n = stpMgr->hashingNodeFactory->CreateTerm(n.GetKind(), n.GetValueWidth(),
                                                 newChildren);
    }
    else
    {
      n = stpMgr->hashingNodeFactory->CreateArrayTerm(
          n.GetKind(), n.GetIndexWidth(), n.GetValueWidth(), newChildren);
    }

    dirty = false;
    return n;
  }

  ASTNode n;
  vector<MutableASTNode*> children;

  static MutableASTNode* createNode(ASTNode n)
  {
    MutableASTNode* result = new MutableASTNode(n);
    all.push_back(result);
    return result;
  }

  bool isSymbol() const
  {
    bool result = n.GetKind() == SYMBOL;
    if (result)
    {
      assert(children.size() == 0);
    }
    return result;
  }

  static MutableASTNode* build(ASTNode n)
  {
    std::unordered_map<uint64_t, MutableASTNode*> visited;
    return build(n, visited);
  }

  void propagateUpDirty()
  {
    if (dirty)
      return;

    dirty = true;
    for (ParentsType::iterator it = parents.begin(); it != parents.end(); it++)
      (*it)->propagateUpDirty();
  }

  void replaceWithAnotherNode(MutableASTNode* newN)
  {
    n = newN->n;
    vector<MutableASTNode*> vars;
    removeChildren(vars); // ignore the result
    children.clear();
    children.insert(children.begin(), newN->children.begin(),
                    newN->children.end());
    for (size_t i = 0; i < children.size(); i++)
      children[i]->parents.insert(this);

    propagateUpDirty();
    assert(newN->parents.size() == 0); // we don't copy 'em in you see.
    newN->removeChildren(vars);
  }

  void replaceWithVar(ASTNode newV, vector<MutableASTNode*>& variables)
  {
    assert(newV.GetKind() == SYMBOL);
    n = newV;
    removeChildren(variables);
    children.clear();
    assert(isSymbol());
    if (parents.size() == 1)
      variables.push_back(this);
    propagateUpDirty();
  }

  void removeChildren(vector<MutableASTNode*>& variables)
  {
    for (unsigned i = 0; i < children.size(); i++)
    {
      MutableASTNode* child = children[i];
      ParentsType& children_parents = child->parents;
      children_parents.erase(this);

      if (children_parents.size() == 0)
      {
        child->removeChildren(variables);
      }

      if (child->isUnconstrained())
      {
        variables.push_back(child);
      }
    }
  }

  // Visit the parent before children. So that we hopefully prune parts of the
  // tree. Ie given  ( F(x_1,... x_10000) = v), where v is unconstrained,
  // we don't spend time exploring F(..), but chop it out.
  static void getAllUnconstrainedVariables(vector<MutableASTNode*>& result)
  {
    const int size = all.size();
    for (int i = size - 1; i >= 0; i--)
    {
      if (all[i]->isUnconstrained())
        result.push_back(all[i]);
    }
    return;
  }

  void getAllVariablesRecursively(vector<MutableASTNode*>& result,
                                  std::unordered_set<MutableASTNode*>& visited)
  {
    if (!visited.insert(this).second)
      return;
    if (isSymbol())
      result.push_back(this);
    const int size = children.size();
    for (int i = 0; i < size; i++)
    {
      children[i]->getAllVariablesRecursively(result, visited);
    }
  }

  bool isUnconstrained()
  {
    if (!isSymbol())
      return false;

    // A protected symbol is never free to be given a value here, no
    // matter how it occurs; see the untouchable declaration above.
    if (isUntouchable(n))
      return false;

    return parents.size() == 1;
  }

  static void cleanup()
  {
    for (size_t i = 0; i < all.size(); i++)
      delete all[i];
    all.clear();
  }
};
}

#endif /* MUTABLEASTNODE_H_ */
