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

// Whether PrimeAudit catches a pass and its priming walk disagreeing.
//
// Six memoised computations fill their tables from the bottom up so their
// own recursion stops one level down, which is sound only where the walk
// reaches the nodes the pass would have reached anyway. Before the direct
// audit, this was guarded only by tests/prime-memos-differential.py, which
// solves each query with priming on and off and requires the same result and
// CNF -- and it catches a violation only when the violation changes the
// output, which two deliberate ones did not.
//
// So the walk and the pass are compared directly now (stp/Util/DagWalk.h),
// and this is the test of the comparison rather than of any pass: a walk and
// a pass are played against each other by hand, agreeing and then failing to,
// so that the check is known to report what it exists to report. A check
// nobody has seen fail is a check nobody has.
//
// The audit is debug-only, so all of this compiles away under NDEBUG.

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/DagWalk.h"
#include <gtest/gtest.h>
#include <string>


using namespace stp;

namespace
{

struct Context
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* hf; // hashing factory: builds the input without folding it.

  Context() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;

    mgr.defaultNodeFactory = &snf;
    hf = mgr.hashingNodeFactory;
  }

  // BVXOR(BVXOR(x0, x1), x2): two interior nodes, three leaves, and no rule
  // in any factory that rewrites it.
  ASTNode chain() { return chain(3); }

  // The same nested `levels` deep.
  ASTNode chain(unsigned levels)
  {
    ASTNode n = mgr.CreateSymbol(("x" + std::to_string(counter++)).c_str(), 0, 8);
    for (unsigned i = 1; i < levels; i++)
      n = hf->CreateTerm(
          BVXOR, 8, n,
          mgr.CreateSymbol(("x" + std::to_string(counter++)).c_str(), 0, 8));
    return n;
  }

  unsigned counter = 0;

  // The factory orders a commutative node's children, so which index holds
  // the nested one is not fixed.
  static ASTNode interiorChild(const ASTNode& n)
  {
    for (const ASTNode& c : n.GetChildren())
      if (c.Degree() > 0)
        return c;
    return n;
  }

  static ASTNode leafChild(const ASTNode& n)
  {
    for (const ASTNode& c : n.GetChildren())
      if (c.Degree() == 0)
        return c;
    return n;
  }
};

// The manager is deliberately not destroyed, as in DeepDag_Test.cpp: what
// tearing one down does while its nodes are still held is not what these
// cases are about, and the process is about to exit anyway.
Context& fresh()
{
  return *(new Context());
}

#ifndef NDEBUG

// A pass, played by hand: it runs a node, asks for the nodes the test says it
// asks for, and reports both to the audit exactly as a real pass does.
void run(PrimeAudit& audit, const ASTNode& n, const ASTVec& asks)
{
  PrimeAudit::Running running(audit, n);
  for (const ASTNode& child : asks)
  {
    PrimeAudit::Running below(audit, child);
  }
}

// A pass that was not primed: it runs a node and, from inside it, the node
// below -- one level of its own call stack per level of the input, which is
// what priming exists to stop and what the depth claim is about.
void runUnprimed(PrimeAudit& audit, const ASTNode& n, bool active = true)
{
  PrimeAudit::Running running(audit, n, active);

  const ASTNode below = Context::interiorChild(n);
  if (below != n) // the bottom of the chain answers with itself.
    runUnprimed(audit, below, active);
}

// Holds the audit open while a case reads its verdict. The check runs when
// the pass's outermost call returns, and where the pass is past its claim it
// stops the process -- which is what it is for, and is checked below by a case
// that lets it happen, but is not a thing to read a string out of.
struct Held
{
  PrimeAudit& audit;
  PrimeAudit::Running running;

  Held(PrimeAudit& audit_, const ASTNode& sentinel)
      : audit(audit_), running(audit_, sentinel)
  {
  }

  // Cleared before the sentinel is dropped, so the comparison it triggers
  // has nothing left to disagree about.
  ~Held() { audit.clear(); }
};

// A primed pass: it runs a node, its operands answer from the memo, and its
// own calls go one level. Whatever the input nests to.
TEST(PrimeAudit, a_pass_within_its_claim_is_silent)
{
  Context& c = fresh();
  const ASTNode top = c.chain(12);
  const ASTNode inner = Context::interiorChild(top);
  const ASTNode leaf = Context::leafChild(top);

  PrimeAudit audit("test", 8);

  {
    PrimeAudit::Running running(audit, top);
    run(audit, inner, ASTVec{inner[0], inner[1]});
    PrimeAudit::Running below(audit, leaf);
  }

  EXPECT_EQ(audit.disagreement(), "");
}

// What priming getting it wrong looks like from here: the walk misses a
// subtree, the pass reaches it anyway -- down its own call stack, one frame
// per level, which is the crash priming exists to prevent. Nothing in the
// output moves, so the CNF comparison cannot see it; the depth can.
TEST(PrimeAudit, a_pass_that_nests_past_its_claim_is_reported)
{
  Context& c = fresh();
  const ASTNode top = c.chain(12);

  PrimeAudit audit("test", 4);

  std::string bad;
  {
    Held held(audit, c.mgr.CreateSymbol("sentinel", 0, 8));
    runUnprimed(audit, top); // nothing was primed, so it goes all the way.
    bad = audit.disagreement();
  }

  EXPECT_NE(bad.find("nested 12 deep"), std::string::npos)
      << "audit said: " << bad;
  EXPECT_NE(bad.find("over its claim of 4"), std::string::npos)
      << "audit said: " << bad;
}

// The differential deliberately turns priming off to recover the old
// recursive implementation. That run is the baseline, not a violation of
// the primed-depth claim, so instrumentation must be dormant with the flag.
TEST(PrimeAudit, a_pass_with_priming_disabled_is_not_audited)
{
  Context& c = fresh();
  PrimeAudit audit("test", 4);

  runUnprimed(audit, c.chain(12), false);

  EXPECT_EQ(0u, audit.depth());
  EXPECT_EQ("", audit.disagreement());
}

// ... and it stops the process rather than reporting quietly, which is the
// only way an assertions build has of insisting.
TEST(PrimeAuditDeath, nesting_past_the_claim_stops_the_process)
{
  EXPECT_DEATH(
      {
        Context& c = fresh();
        PrimeAudit audit("test", 4);
        runUnprimed(audit, c.chain(12));
      },
      "nested 11 deep");
}


// Re-entering on a node the pass has just built is allowed, and is why the
// claim is a small number rather than one or two: the operands of such a node
// are already primed, so the nesting is a property of the rewriting and not
// of the input.
TEST(PrimeAudit, re_entering_on_a_built_node_is_within_the_claim)
{
  Context& c = fresh();
  const ASTNode top = c.chain();
  const ASTNode inner = Context::interiorChild(top);
  const ASTNode leaf = Context::leafChild(top);

  PrimeAudit audit("test", 8);

  const ASTNode built = c.hf->CreateTerm(BVNOT, 8, top);

  {
    PrimeAudit::Running running(audit, top);
    run(audit, inner, ASTVec{inner[0], inner[1]});
    PrimeAudit::Running below(audit, leaf);
    PrimeAudit::Running newer(audit, built); // asked for, never primed.
  }

  EXPECT_EQ(audit.disagreement(), "");
}


#endif // NDEBUG

} // namespace
