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

// AST-depth-recursive traversals: no pass may consume call stack in
// proportion to the depth of the input DAG.
//
// Deeply nested formulas (CPAchecker k-induction traces, ~9,300 nested
// nodes) deterministically segfault STP: Rewriting::rewrite and
// Dependencies::build recurse once per level of the input, so an input
// deep enough to exhaust the stack kills the process. The depth is chosen
// by whoever wrote the input, so no fixed stack size is a fix -- these
// traversals have to keep their working state on the heap.
//
// Each property below is checked twice: once on a shallow chain, which
// says the property itself holds, and once on a chain far deeper than the
// recursive frames fit in, which is what fails today. Two things make the
// deep result a property of STP rather than of the machine it runs on:
//
//   * it runs under a stack rlimit the test sets itself, so the ambient
//     `ulimit -s` (8 MiB here, unlimited on some CI runners) cannot
//     decide the outcome; and
//   * it runs in a forked child, so a stack overflow is one failing test
//     rather than a segfault that takes the rest of the binary with it.
//
// The chains are built with the hashing factory: the simplifying factory
// would fold or reassociate them, and the DAG under test would no longer
// be the deep one the test means to build.

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Flatten.h"
#include "stp/Simplifier/Rewriting.h"
#include "stp/Simplifier/NodeDomainAnalysis.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/StrengthReduction.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/Simplifier/constantBitP/Dependencies.h"
#include <cstdlib>
#include <gtest/gtest.h>
#include <string>

#ifndef _WIN32
#include <sys/resource.h>
#endif

using namespace stp;

namespace
{

// Small enough that a per-level call frame cannot fit these depths, large
// enough for anything a stack-safe traversal legitimately does.
const size_t STACK_BYTES = 1024 * 1024;

// Exit codes of the forked child. Anything else -- in particular a signal
// -- is the failure this file exists to catch.
const int EXIT_OK = 0;
const int EXIT_BAD_RESULT = 2;

// Shallow enough to recurse safely: what the control cases run on.
const unsigned SHALLOW = 50;

// Cap how far this process's stack may grow. Linux applies a lowered
// RLIMIT_STACK to further growth of the main stack, so the check runs
// against a stack of exactly this size whatever the ambient `ulimit -s`
// is -- 8 MiB on a developer box, sometimes unlimited on a CI runner.
// Bounding it is what makes a passing deep case mean "the traversal does
// not use the stack for depth" rather than "this machine had room".
void capStack()
{
#ifndef _WIN32
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl) == 0)
  {
    rl.rlim_cur = STACK_BYTES;
    setrlimit(RLIMIT_STACK, &rl);
  }
#else
  // No setrlimit; MSVC's default main-thread stack is 1 MiB already, which
  // is the size this wants.
#endif
}

// Runs one of the checks below in a child process on a bounded stack.
// `check` returning false -- the pass ran but got the wrong answer -- is
// reported as an exit code distinct from a crash.
//
// The manager is deliberately not destroyed. Releasing a deep DAG is
// itself depth-recursive (~ASTInterior -> CleanUp -> ~ASTInterior, one
// level per node), so tearing these chains down would overflow the stack
// after the traversal under test had already returned, and every case here
// would report the destructor's limit instead of the pass's. That is a
// real defect, but a separate one; the child exits immediately, so leaving
// the DAG alive costs nothing.
#define EXPECT_STACK_SAFE(check, depth)                                     \
  EXPECT_EXIT(                                                              \
      {                                                                     \
        capStack();                                                         \
        Context* c = new Context();                                         \
        std::exit(check(*c, depth) ? EXIT_OK : EXIT_BAD_RESULT);            \
      },                                                                    \
      ::testing::ExitedWithCode(EXIT_OK), "")

struct Context
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* nf; // simplifying factory: what the passes themselves use.
  NodeFactory* hf; // hashing factory: builds the input without folding it.

  // Roots each check hands over, so that returning from it does not drop
  // the last handle on a deep DAG and start the recursive teardown
  // described at EXPECT_STACK_SAFE.
  ASTVec roots;

  Context() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;

    mgr.defaultNodeFactory = &snf;
    nf = &snf;
    hf = mgr.hashingNodeFactory;
  }

  // A chain `depth` symbols long, so `depth`-1 operator nodes nested one
  // inside the next. No rewrite or flattening rule matches a chain of
  // BVXORs or BVMULTs over symbols, so what the passes do here is exactly
  // the traversal.
  ASTNode chain(Kind k, unsigned depth, unsigned width = 8)
  {
    ASTNode n = mgr.CreateSymbol("x0", 0, width);
    for (unsigned i = 1; i < depth; i++)
    {
      const std::string name = "x" + std::to_string(i);
      n = hf->CreateTerm(k, width, n,
                         mgr.CreateSymbol(name.c_str(), 0, width));
    }
    return n;
  }

  // The passes take a formula, and rewrite rules fire on the children of a
  // visited node rather than on the root, so put the chain under one.
  ASTNode formula(const ASTNode& term)
  {
    return hf->CreateNode(EQ, term, mgr.CreateZeroConst(term.GetValueWidth()));
  }

  // The factories order commutative children (constants first, then
  // symbols), so which index holds the chain is not fixed.
  static ASTNode childOfKind(const ASTNode& n, Kind k)
  {
    for (const auto& c : n.GetChildren())
      if (c.GetKind() == k)
        return c;
    return n;
  }
};

// Dependencies::build, the parent map constant-bit propagation runs on.
// Two of the 21 known corpus crashes land here.
bool dependenciesChainOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(top);

  simplifier::constantBitP::Dependencies deps(top);

  // Every link of the chain is read by exactly one parent, the link above
  // it -- and the traversal has to have reached the bottom to know that.
  ASTNode n = Context::childOfKind(top, BVXOR);
  unsigned levels = 0;
  while (n.GetKind() == BVXOR)
  {
    const ASTNode child = n[0].GetKind() == BVXOR ? n[0] : n[1];
    if (deps.getDependents(child).size() != 1)
      return false;
    if (!deps.nodeDependsOn(n, child))
      return false;
    n = child;
    levels++;
  }
  return levels == depth - 1;
}

// Rewriting::rewrite (19 of the 21 known corpus crashes, ~9,300 nested
// frames deep) and, ahead of it in the same pass, the equally unbounded
// Rewriting::buildShareCount.
bool rewritingIdentityOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(top);

  Rewriting r(&c.mgr, c.nf);
  ASTNode f = top;
  // No rule matches a BVXOR chain, so the pass is an identity here; any
  // other answer means the traversal lost part of the DAG.
  return r.topLevel(f) == top;
}

// The second recursion point: when a rule rewrites a child, the result is
// fed back through rewrite(). The rule is `0 = (a + b)` -->
// `(bvuminus a) = b`, placed beside a deep chain so the re-entry happens
// in a traversal that is already deep.
bool rewritingRuleFiresOk(Context& c, unsigned depth)
{
  const unsigned width = 8;
  // The hashing factory orders a node's children by node number, and the
  // rule matches EQ(const, plus): the constant has to exist before the
  // operands do, or the equality comes out as EQ(plus, const) and nothing
  // fires.
  const ASTNode zero = c.mgr.CreateZeroConst(width);
  const ASTNode a = c.mgr.CreateSymbol("a", 0, width);
  const ASTNode b = c.mgr.CreateSymbol("b", 0, width);
  const ASTNode plus = c.hf->CreateTerm(BVPLUS, width, a, b);
  const ASTNode fires = c.hf->CreateNode(EQ, zero, plus);
  if (fires[0].GetKind() != BVCONST || fires[1].GetKind() != BVPLUS)
    return false; // not the shape the rule matches: prove nothing quietly.

  const ASTNode top =
      c.hf->CreateNode(AND, fires, c.formula(c.chain(BVXOR, depth, width)));
  c.roots.push_back(top);

  Rewriting r(&c.mgr, c.nf);
  ASTNode f = top;
  // The equality is rewritten, so the pass must not be an identity.
  return r.topLevel(f) != top;
}

// Flatten::buildShareCount on its own. A chain of same-kind flattenable
// nodes is the one shape flatten() does not recurse on: it appends the
// grandchildren to its own worklist and keeps looping, so the only
// depth-recursive walk this input reaches is the share count built ahead
// of it.
bool flattenShareCountOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVPLUS, depth));
  c.roots.push_back(top);

  Flatten flattener(&c.mgr, c.nf);
  ASTNode f = top;
  const ASTNode result = flattener.topLevel(f);
  c.roots.push_back(result);

  // The whole chain collapses into one BVPLUS over every symbol in it.
  const ASTNode plus = Context::childOfKind(result, BVPLUS);
  return plus.GetKind() == BVPLUS && plus.Degree() == depth;
}

// Flatten carries its own copy of both traversals: an identical
// buildShareCount, and flatten() with the same recursive shape as
// rewrite(). Flattening is off by default since #786, so it is not on the
// observed crash path -- but --flatten puts it back. BVMULT is not a
// flattenable kind, which keeps this a test of the traversal rather than
// of flattening.
bool flattenIdentityOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVMULT, depth));
  c.roots.push_back(top);

  Flatten flattener(&c.mgr, c.nf);
  ASTNode f = top;
  return flattener.topLevel(f) == top;
}

// SubstitutionMap::replace, which rebuilds a DAG with some nodes swapped
// out. Reached from every pass that applies a substitution, and the walk
// is over the whole input.
bool substitutionOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(top);

  // The symbol at the far end of the chain maps to a constant, so the walk
  // has to reach the bottom and every node above it is rebuilt on the way
  // back up.
  ASTNodeMap fromTo, cache;
  fromTo[c.mgr.CreateSymbol("x0", 0, 8)] = c.mgr.CreateBVConst(8, 1);

  const ASTNode result =
      SubstitutionMap::replace(top, fromTo, cache, c.nf);
  c.roots.push_back(result);
  return result != top;
}

// Releasing a DAG. A node that loses its last reference releases its
// children, which can lose theirs: the teardown is as deep as the input,
// and it runs wherever the last handle happens to be dropped.
bool teardownOk(Context& c, unsigned depth)
{
  {
    const ASTNode top = c.formula(c.chain(BVXOR, depth));
    (void)top;
  } // the only handle goes here, and the whole chain follows it.
  return true;
}

// StrengthReduction::visit, which rebuilds the DAG applying whatever the
// domain analyses prove about each node.
bool strengthReductionOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(top);

  StrengthReduction sr(c.nf, &c.mgr.UserFlags);
  NodeDomainAnalysis nda(&c.mgr);
  const ASTNode result = sr.topLevel(top, nda);
  c.roots.push_back(result);

  // Nothing about a chain of unconstrained symbols is reducible, so the
  // pass has to hand back what it was given.
  return result == top;
}

// Simplifier::SimplifyFormula. The AND/OR spine it nests through is walked
// on the heap; the other boolean kinds still recurse into each other.
bool simplifyOk(Context& c, unsigned depth)
{
  // A chain of ANDs: each operand of each one is simplified by coming back
  // through SimplifyFormula.
  ASTNode f = c.hf->CreateNode(EQ, c.mgr.CreateSymbol("s0", 0, 8),
                               c.mgr.CreateZeroConst(8));
  for (unsigned i = 1; i < depth; i++)
  {
    const std::string name = "s" + std::to_string(i);
    const ASTNode leaf = c.hf->CreateNode(
        EQ, c.mgr.CreateSymbol(name.c_str(), 0, 8), c.mgr.CreateZeroConst(8));
    f = c.hf->CreateNode(AND, leaf, f);
  }
  c.roots.push_back(f);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  const ASTNode result = simp.SimplifyFormula_TopLevel(f, false);
  c.roots.push_back(result);
  return result.GetKind() == AND || result.GetKind() == EQ;
}

/* Control cases: the same properties on a chain shallow enough for the
   recursive implementations. These pass today, so a deep case failing is
   about stack depth and nothing else. */
TEST(DeepDag, shallow_dependencies_build)
{
  Context c;
  EXPECT_TRUE(dependenciesChainOk(c, SHALLOW));
}

TEST(DeepDag, shallow_rewriting)
{
  Context c;
  EXPECT_TRUE(rewritingIdentityOk(c, SHALLOW));
}

TEST(DeepDag, shallow_rewriting_rule_fires)
{
  Context c;
  EXPECT_TRUE(rewritingRuleFiresOk(c, SHALLOW));
}

TEST(DeepDag, shallow_flatten)
{
  Context c;
  EXPECT_TRUE(flattenIdentityOk(c, SHALLOW));
}

TEST(DeepDag, shallow_flatten_share_count)
{
  Context c;
  EXPECT_TRUE(flattenShareCountOk(c, SHALLOW));
}

TEST(DeepDag, shallow_substitution)
{
  Context c;
  EXPECT_TRUE(substitutionOk(c, SHALLOW));
}

TEST(DeepDag, shallow_teardown)
{
  Context c;
  EXPECT_TRUE(teardownOk(c, SHALLOW));
}

TEST(DeepDag, shallow_strength_reduction)
{
  Context c;
  EXPECT_TRUE(strengthReductionOk(c, SHALLOW));
}

TEST(DeepDag, shallow_simplify)
{
  Context c;
  EXPECT_TRUE(simplifyOk(c, SHALLOW));
}

/* The same properties on inputs deeper than the call stack can hold.
   Depths are picked so each case reaches the traversal it is named for:
   buildShareCount's frames are far smaller than rewrite's, so it only
   fails first on a much deeper input.

   The cases still marked DISABLED_ are the traversals that have not been
   converted yet; each is enabled by the commit that converts the traversal
   it names. deep_rewriting_share_count needs both buildShareCount and
   rewrite, since topLevel runs them back to back and there is no way in
   from outside to run only the first. */
TEST(DeepDag, deep_dependencies_build)
{
  EXPECT_STACK_SAFE(dependenciesChainOk, 50);
}

TEST(DeepDag, deep_rewriting_share_count)
{
  EXPECT_STACK_SAFE(rewritingIdentityOk, 200000);
}

TEST(DeepDag, deep_rewriting_rewrite)
{
  EXPECT_STACK_SAFE(rewritingIdentityOk, 10000);
}

TEST(DeepDag, deep_rewriting_rule_fires)
{
  EXPECT_STACK_SAFE(rewritingRuleFiresOk, 10000);
}

TEST(DeepDag, deep_flatten_share_count)
{
  EXPECT_STACK_SAFE(flattenShareCountOk, 100000);
}

TEST(DeepDag, deep_flatten)
{
  EXPECT_STACK_SAFE(flattenIdentityOk, 10000);
}

TEST(DeepDag, deep_substitution)
{
  EXPECT_STACK_SAFE(substitutionOk, 20000);
}

TEST(DeepDag, deep_teardown)
{
  EXPECT_STACK_SAFE(teardownOk, 50000);
}

TEST(DeepDag, deep_strength_reduction)
{
  EXPECT_STACK_SAFE(strengthReductionOk, 20000);
}

TEST(DeepDag, deep_simplify)
{
  EXPECT_STACK_SAFE(simplifyOk, 20000);
}

} // namespace
