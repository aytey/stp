/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
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

#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BVEQCongruenceClosure.h"
#include "stp/ToSat/BVExactEncoder.h"

#include <algorithm>
#include <iostream>
#include <unordered_map>

namespace stp
{

// Both families in one call, equalities first: theirs is the cheaper scan,
// and the congruence phase inside it can refute a candidate at word level
// without reading a single bit. A round that refined an equality stops
// there rather than going on to the terms -- the term scan reads the same
// model, and what it would find in it has already been ruled out.
unsigned BVAbstractionRefiner::refine(
    SATSolver& solver, const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  unsigned refined = 0;
  if (hasEqualities())
    refined = refineEqualities(solver, nodeToSATVar);
  if (refined == 0 && hasTerms())
  {
    try
    {
      refined = refineTerms(solver, nodeToSATVar);
    }
    catch (const AIGBudgetExhausted& e)
    {
      if (bm->UserFlags.stats_flag)
        std::cerr << "AIG node budget exhausted during exact BV refinement at "
                  << e.nodeCount << " nodes" << std::endl;
      bm->noteAIGBudgetExhausted(e.nodeCount);
      return 0;
    }
  }
  if (refined > 0)
  {
    refinements_ += refined;
    bm->UserFlags.coverage.bv_refinement_rounds++;
    if (bm->UserFlags.stats_flag)
      std::cerr << "BV abstraction: refined " << refined << " operations"
                << std::endl;
  }
  return refined;
}

// Which variables carry a term record's result: its own, where the lowering
// filed them, and otherwise whatever the AST-keyed map holds for its term.
// NULL when neither has an answer.
//
// Both readers of a result go through here, and that is the point. They are
// entitled to different things -- freezing runs before the first solve and
// tolerates a record whose bits are not encoded yet, refinement runs after it
// and does not -- but neither is entitled to its own opinion about WHICH
// variables the result is. A record frozen at one set and checked at another
// is the shape of the bug the record-owned result exists to close, rebuilt
// inside this file.
static const std::vector<unsigned>*
resultVarsOf(const BVTermAbstraction& abstraction,
             const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  if (!abstraction.resultSATVars.empty())
    return &abstraction.resultSATVars;

  const auto it = nodeToSATVar.find(abstraction.termNode);
  return it == nodeToSATVar.end() ? NULL : &it->second;
}

void BVAbstractionRefiner::freezeVariables(
    SATSolver& satSolver,
    const ToSATBase::ASTNodeToSATVar& nodeToSATVar) const
{
  // Every variable a future refinement lemma can be written over: the
  // records' own inputs, and the operand bits the pinning clauses name.
  // A simplifying backend is free to eliminate anything not frozen, and a
  // clause added later over an eliminated variable is exactly the write
  // the simplifying MiniSat family cannot take back -- backends that
  // restore an eliminated variable on contact make every one of these
  // calls a deliberate no-op instead (see Cadical::setFrozen).
  //
  // Best effort, and the one place a record's variables may be absent
  // without anything being wrong: this runs before the first solve, so it
  // is not the party entitled to a complete encoding. Refinement is, and
  // says so itself. Freezing what is not there would be a write against a
  // variable the backend does not have.
  for (const auto& a : eqs_)
  {
    if (a.abstractionSATVar != BV_ABSTRACTION_NO_VAR)
      satSolver.setFrozen(a.abstractionSATVar);
    // The equality's lemmas are Tseitin clauses over the operands' bits,
    // so those bits need freezing exactly as a term record's operands do.
    const ASTNode* sides[2] = {&a.leftSymbol, &a.rightSymbol};
    for (const ASTNode* side : sides)
    {
      auto sideIt = nodeToSATVar.find(*side);
      if (sideIt != nodeToSATVar.end())
        for (unsigned v : sideIt->second)
          if (v != BV_ABSTRACTION_NO_VAR)
            satSolver.setFrozen(v);
    }
  }

  for (const auto& a : terms_)
  {
    const std::vector<unsigned>* result = resultVarsOf(a, nodeToSATVar);
    if (result != NULL)
      for (unsigned v : *result)
        if (v != BV_ABSTRACTION_NO_VAR)
          satSolver.setFrozen(v);
    for (unsigned i = 0; i < a.numOperands; i++)
    {
      auto opIt = nodeToSATVar.find(a.operands[i]);
      if (opIt != nodeToSATVar.end())
        for (unsigned v : opIt->second)
          if (v != BV_ABSTRACTION_NO_VAR)
            satSolver.setFrozen(v);
    }
    if (a.condSATVar != BV_ABSTRACTION_NO_VAR)
      satSolver.setFrozen(a.condSATVar);
  }
}

// The SAT variables one operand of a record was encoded into, ready to be
// read out of a candidate or written into a clause. A record's own result
// does not come through here: it is the record's to name, and resultVarsOf
// answers for it.
//
// Three things have to hold for the record to be checkable at all, and all
// three hold by construction.
//
// The node is in the map. The blaster registers every node it abstracts and
// every operand it abstracts one over, through ensureProxyCIs or the
// assignment beside the record, and both lowerings carry the whole of that
// registry across: fill_node_to_var for the batch pipeline, and
// addAbstractionOperand for the incremental driver, which harvests records
// and operands from the one blaster and drops both together on a rebuild.
//
// The vector is at least as wide as the record. Both widths are the same
// node's GetValueWidth(), and an operation and its operands have the width
// STP's type checker gave them.
//
// And every bit in that range is a variable the CNF has. ~0u marks one that
// is not, which is how a symbol only partly bit-blasted is reported; the
// nodes here are either whole symbols or vectors of proxy inputs minted a
// bit at a time, so none of them is partial.
//
// So none of this fires -- across the in-tree corpus under both drivers and
// all five CNF generators, some 450,000 record checks, not once. It is here
// because all three fail quietly and none of them is checked anywhere else.
// Reading past the vector is an out-of-bounds read: a record one bit wider
// than its operand segfaulted on an eight-bit equality and, on the term
// path, quietly answered from whatever followed the allocation. Reading ~0u
// asks the SAT backend for the value of a variable it never had. And
// skipping the record -- which is what returning "no bits" used to lead to
// at every one of these call sites -- is worse than either, because an
// abstraction is an over-approximation until refinement pins it to its
// operands: a record left unchecked is a record no candidate can contradict,
// so the search is free to satisfy the query by giving it whatever value it
// likes. With the operands of `a = 1 and b = 2 and a = b` taken out of the
// map, that unsatisfiable query came back sat, with exit status 0 and no
// diagnostic at all.
//
// There is no conservative way to carry on from any of the three, so say
// which one happened instead.
static const std::vector<unsigned>&
encodedBitsOf(const ASTNode& node, unsigned width,
              const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  const auto it = nodeToSATVar.find(node);
  if (it == nodeToSATVar.end())
    FatalError("BV abstraction: an abstracted operation names a node that "
               "the bit-blast did not encode, so no candidate can be "
               "checked against it: ",
               node);

  const std::vector<unsigned>& vars = it->second;
  if (vars.size() < width)
    FatalError("BV abstraction: an abstracted operation is recorded wider "
               "than the bits the bit-blast encoded for it; the record's "
               "width is: ",
               node, (int)width);

  for (unsigned i = 0; i < width; ++i)
    if (vars[i] == BV_ABSTRACTION_NO_VAR)
      FatalError("BV abstraction: an abstracted operation names a bit that "
                 "never reached the CNF; the bit is: ",
                 node, (int)i);

  return vars;
}

// The same result, for refinement: every bit a variable the CNF has, or the
// call does not come back. The three things checked here are the three
// encodedBitsOf checks for an operand, and hold for the same reasons.
static const std::vector<unsigned>&
encodedResultBitsOf(const BVTermAbstraction& abstraction,
                    const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  const std::vector<unsigned>* vars = resultVarsOf(abstraction, nodeToSATVar);
  if (vars == NULL)
    FatalError("BV abstraction: an abstracted operation has no result the "
               "bit-blast encoded, so no candidate can be checked against "
               "it: ",
               abstraction.termNode);

  if (vars->size() < abstraction.width)
    FatalError("BV abstraction: an abstracted operation is recorded wider "
               "than the result the bit-blast gave it; the record's width "
               "is: ",
               abstraction.termNode, (int)abstraction.width);

  for (unsigned i = 0; i < abstraction.width; ++i)
    if ((*vars)[i] == BV_ABSTRACTION_NO_VAR)
      FatalError("BV abstraction: an abstracted operation's result names a "
                 "bit that never reached the CNF; the bit is: ",
                 abstraction.termNode, (int)i);

  return *vars;
}

// A record's own variable: the Boolean an equality became, or the condition
// input of a comparison or an if-then-else. ~0u is both "the family has none"
// and "the one it has never reached the solver", and neither is a state any
// caller can go on from -- see encodedBitsOf above for why skipping is not an
// option.
//
// Called where a round first reads the variable, which is always the scan; the
// clause phases below run only over the records that scan accepted, so what
// they write over has been through here already.
static unsigned recordedVar(unsigned var, const ASTNode& node,
                            const char* what)
{
  if (var == BV_ABSTRACTION_NO_VAR)
    FatalError(what, node);
  return var;
}

unsigned BVAbstractionRefiner::refineEqualities(
    SATSolver& solver, const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  // Phase 1: Congruence closure — detect transitivity conflicts at word level.
  //
  // Defined records take part too. A defined equality's Boolean is exact --
  // its clauses force it to the operands' bits -- so its model value is a
  // fact about the candidate, chains are free to run through it, and an
  // explanation clause naming it stays a theorem. Leaving defined records
  // out breaks exactly the chains that mature first: a conflict whose path
  // crosses one would fall through to the bit-level scan and be rediscovered
  // a definition at a time. A conflict can still never be built from defined
  // records alone -- their Booleans mirror real bit-vectors, and equality of
  // bit-vectors is transitive -- so every clause this phase emits constrains
  // at least one undefined record, and blocks the candidate it was read from.
  {
    std::unordered_map<ASTNode, unsigned, ASTNode::ASTNodeHasher,
                       ASTNode::ASTNodeEqual> symbolToIdx;
    unsigned nextIdx = 0;
    for (const auto& abs : eqs_)
    {
      if (symbolToIdx.find(abs.leftSymbol) == symbolToIdx.end())
        symbolToIdx[abs.leftSymbol] = nextIdx++;
      if (symbolToIdx.find(abs.rightSymbol) == symbolToIdx.end())
        symbolToIdx[abs.rightSymbol] = nextIdx++;
    }

    std::vector<BVEQCongruenceClosure::EqInfo> eqInfos;
    for (const auto& abs : eqs_)
    {
      // Read once and checked once: the closure both reads this variable's
      // value and writes the explanation clause over it.
      const unsigned eqVar = recordedVar(
          abs.abstractionSATVar, abs.eqNode,
          "BV abstraction: an abstracted equality's own variable never "
          "reached the solver: ");
      bool modelTrue = (solver.modelValue(eqVar) == solver.true_literal());
      eqInfos.push_back({symbolToIdx[abs.leftSymbol],
                          symbolToIdx[abs.rightSymbol],
                          eqVar,
                          modelTrue});
    }

    BVEQCongruenceClosure cc;
    unsigned ccConflicts = cc.check(eqInfos, solver);
    if (ccConflicts > 0)
      return ccConflicts;
  }

  // Phase 2: Bit-level Tseitin encoding for remaining inconsistencies.
  // Scan phase: identify inconsistent EQs (model reads only).
  const unsigned refineWidth = bm->UserFlags.bv_eq_refine_width;

  struct InconsistentEQ {
    size_t absIdx;
    unsigned newEnd;
    const std::vector<unsigned>* leftVars;
    const std::vector<unsigned>* rightVars;
    // The candidate said unequal while the operands' bits agree. The
    // prefix clauses below say nothing to such a candidate -- they are all
    // conditioned on the Boolean being true -- so the clause phase owes it
    // a blocking lemma of its own, written over the one value both sides
    // share, which is cached here because phase 2 must not read the model.
    bool saidUnequal;
    std::vector<bool> sharedValue;
  };
  std::vector<InconsistentEQ> incEQs;

  for (size_t idx = 0; idx < eqs_.size(); ++idx)
  {
    auto& abs = eqs_[idx];
    if (abs.defined)
      continue;

    const unsigned eqVar = recordedVar(
        abs.abstractionSATVar, abs.eqNode,
        "BV abstraction: an abstracted equality's own variable never "
        "reached the solver: ");
    bool absTrue = (solver.modelValue(eqVar) == solver.true_literal());

    // Both sides, whatever their kind: the blaster registers a constant
    // operand as a vector of inputs pinned to it, so there is nothing to
    // fold in here and the clause phase below has real variables to write
    // its Tseitin encoding over.
    const std::vector<unsigned>& leftVars =
        encodedBitsOf(abs.leftSymbol, abs.width, nodeToSATVar);
    const std::vector<unsigned>& rightVars =
        encodedBitsOf(abs.rightSymbol, abs.width, nodeToSATVar);

    bool actualEqual = true;
    for (unsigned bit = 0; bit < abs.width; ++bit)
    {
      if (solver.modelValue(leftVars[bit]) != solver.modelValue(rightVars[bit]))
      {
        actualEqual = false;
        break;
      }
    }

    if (absTrue == actualEqual)
      continue;

    unsigned newEnd;
    if (refineWidth == 0 || refineWidth >= abs.width)
      newEnd = abs.width;
    else if (abs.refinedBits == 0)
      newEnd = std::min(refineWidth, abs.width);
    else
      newEnd = std::min(abs.refinedBits * 2, abs.width);

    InconsistentEQ inc{idx, newEnd, &leftVars, &rightVars, !absTrue, {}};
    if (inc.saidUnequal && newEnd < abs.width)
    {
      inc.sharedValue.resize(abs.width);
      for (unsigned bit = 0; bit < abs.width; ++bit)
        inc.sharedValue[bit] =
            (solver.modelValue(leftVars[bit]) == solver.true_literal());
    }
    incEQs.push_back(std::move(inc));
  }

  // Clause phase: add Tseitin encoding (no model reads).
  unsigned refined = 0;
  for (auto& inc : incEQs)
  {
    auto& abs = eqs_[inc.absIdx];

    // A candidate that said unequal over agreeing bits satisfies every
    // prefix clause vacuously -- each one is conditioned on the Boolean
    // being true -- so left to the prefix alone the search could hand the
    // identical candidate back until the definition completes, one full
    // solve per doubling. Rule the candidate out now instead: if both
    // sides hold the one value this candidate gave them, the equality is
    // true. That is the definition's own consequence at a single point,
    // so asserting it early is as sound as asserting the definition, and
    // it is one clause against a round of solving. A round that completes
    // the definition needs none of this: its closing clause already forces
    // the Boolean once every helper agrees.
    if (inc.saidUnequal && !inc.sharedValue.empty())
    {
      SATSolver::vec_literals cl;
      cl.push(SATSolver::mkLit(abs.abstractionSATVar, false));
      for (unsigned bit = 0; bit < abs.width; ++bit)
      {
        cl.push(SATSolver::mkLit((*inc.leftVars)[bit],
                                 inc.sharedValue[bit]));
        cl.push(SATSolver::mkLit((*inc.rightVars)[bit],
                                 inc.sharedValue[bit]));
      }
      solver.addClause(cl);
    }

    for (unsigned bit = abs.refinedBits; bit < inc.newEnd; ++bit)
    {
      unsigned lv = (*inc.leftVars)[bit];
      unsigned rv = (*inc.rightVars)[bit];
      unsigned h = solver.newVar();
      solver.setFrozen(h);
      abs.xnorHelpers.push_back(h);

      SATSolver::vec_literals cl;

      cl.clear();
      cl.push(SATSolver::mkLit(lv, true));
      cl.push(SATSolver::mkLit(rv, true));
      cl.push(SATSolver::mkLit(h, false));
      solver.addClause(cl);

      cl.clear();
      cl.push(SATSolver::mkLit(lv, false));
      cl.push(SATSolver::mkLit(rv, false));
      cl.push(SATSolver::mkLit(h, false));
      solver.addClause(cl);

      cl.clear();
      cl.push(SATSolver::mkLit(lv, false));
      cl.push(SATSolver::mkLit(rv, true));
      cl.push(SATSolver::mkLit(h, true));
      solver.addClause(cl);

      cl.clear();
      cl.push(SATSolver::mkLit(lv, true));
      cl.push(SATSolver::mkLit(rv, false));
      cl.push(SATSolver::mkLit(h, true));
      solver.addClause(cl);

      cl.clear();
      cl.push(SATSolver::mkLit(abs.abstractionSATVar, true));
      cl.push(SATSolver::mkLit(h, false));
      solver.addClause(cl);
    }

    abs.refinedBits = inc.newEnd;

    if (abs.refinedBits >= abs.width)
    {
      SATSolver::vec_literals cl;
      for (unsigned h : abs.xnorHelpers)
        cl.push(SATSolver::mkLit(h, true));
      cl.push(SATSolver::mkLit(abs.abstractionSATVar, false));
      solver.addClause(cl);

      abs.defined = true;
    }

    refined++;
  }
  return refined;
}

static void getOperandBits(
    const ASTNode& operand, unsigned width,
    const ToSATBase::ASTNodeToSATVar& nodeToSATVar, SATSolver& solver,
    std::vector<bool>& bits)
{
  bits.resize(width);
  if (operand.GetKind() == BVCONST)
  {
    CBV val = operand.GetBVConst();
    for (unsigned i = 0; i < width; ++i)
      bits[i] = CONSTANTBV::BitVector_bit_test(val, i);
    return;
  }
  const std::vector<unsigned>& satVars =
      encodedBitsOf(operand, width, nodeToSATVar);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = (solver.modelValue(satVars[i]) == solver.true_literal());
}

static void getOperandVars(
    const ASTNode& operand, unsigned width,
    const ToSATBase::ASTNodeToSATVar& nodeToSATVar, SATSolver& solver,
    std::vector<unsigned>& vars)
{
  // The registry first, constants included. The blaster proxies every
  // operand it abstracts a multiplication, division or if-then-else over
  // -- a constant gets a vector of inputs pinned to it by biconditionals
  // -- and those variables are already in the solver and already frozen.
  // Minting a fresh pinned vector here instead, which is what the
  // constant short-circuit ahead of the lookup used to do, said the same
  // thing over new variables on every round the record was refined: a
  // multiplication enumerating blocking lemmas paid width variables and
  // width unit clauses per round for a value the CNF already carried.
  if (nodeToSATVar.find(operand) != nodeToSATVar.end())
  {
    vars = encodedBitsOf(operand, width, nodeToSATVar);
    return;
  }

  // A constant the blaster deliberately left out of the registry: BVPLUS
  // folds constant operands into the record rather than proxying them.
  // Its record defines itself in a single round, so this mints once.
  if (operand.GetKind() == BVCONST)
  {
    vars.resize(width);
    CBV val = operand.GetBVConst();
    for (unsigned i = 0; i < width; ++i)
    {
      vars[i] = solver.newVar();
      solver.setFrozen(vars[i]);
      SATSolver::vec_literals cl;
      cl.push(SATSolver::mkLit(vars[i],
              !CONSTANTBV::BitVector_bit_test(val, i)));
      solver.addClause(cl);
    }
    return;
  }

  // Neither registered nor a constant: refused, naming which of the three
  // registry guarantees broke.
  vars = encodedBitsOf(operand, width, nodeToSATVar);
}

static bool isBVCompare(Kind k)
{
  return k == BVLE || k == BVGE || k == BVGT || k == BVLT ||
         k == BVSLE || k == BVSGE || k == BVSGT || k == BVSLT;
}

static bool computeBVLE(const std::vector<bool>& left,
                        const std::vector<bool>& right,
                        bool isSigned)
{
  unsigned w = left.size();
  if (isSigned)
  {
    bool aSign = left[w - 1];
    bool bSign = right[w - 1];
    if (aSign && !bSign) return true;
    if (!aSign && bSign) return false;
  }
  for (int i = (int)w - 1; i >= 0; --i)
  {
    if (isSigned && i == (int)w - 1) continue;
    if (!left[i] && right[i]) return true;
    if (left[i] && !right[i]) return false;
  }
  return true;
}

// Every comparison is `<=` under some combination of swapping the operands,
// negating the answer, and reading the top bit as a sign. Named once, because
// the model check below and the clauses that pin the abstraction both need it
// and must not disagree: they did, over BVLT, and a lemma that pins an
// abstraction to a > b for a query that asked a < b is not a weaker claim than
// the right one but the opposite of it.
struct CompareForm
{
  bool swapOps;
  bool negateResult;
  bool isSigned;
};

static CompareForm comparisonForm(Kind k)
{
  switch (k)
  {
    case BVLE:  return {false, false, false};
    case BVGE:  return {true,  false, false};
    case BVGT:  return {false, true,  false};
    case BVLT:  return {true,  true,  false};
    case BVSLE: return {false, false, true};
    case BVSGE: return {true,  false, true};
    case BVSGT: return {false, true,  true};
    case BVSLT: return {true,  true,  true};
    default:    return {false, false, false};
  }
}

static bool computeBVCompare(Kind k, const std::vector<bool>& aBits,
                             const std::vector<bool>& bBits)
{
  const CompareForm form = comparisonForm(k);
  const bool le = form.swapOps ? computeBVLE(bBits, aBits, form.isSigned)
                               : computeBVLE(aBits, bBits, form.isSigned);
  return form.negateResult ? !le : le;
}

// The gates the refinement's own lemmas are built from, so that nothing here
// is a hand-written clause block; each is written out of the row of the truth
// table it rules out. mkLit(v, sign) is false exactly when v equals sign, so
// a literal at `bit` is false exactly when that input is `bit`, and a clause
// listing one row is falsified only on that row.

static unsigned freshVar(SATSolver& solver)
{
  const unsigned v = solver.newVar();
  solver.setFrozen(v);
  return v;
}

static unsigned pinnedVar(SATSolver& solver, bool value)
{
  const unsigned v = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.push(SATSolver::mkLit(v, !value));
  solver.addClause(cl);
  return v;
}

// z <-> x | y
static unsigned mkOr(SATSolver& solver, unsigned x, unsigned y)
{
  const unsigned z = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(y, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(y, false)); cl.push(SATSolver::mkLit(z, true)); solver.addClause(cl);
  return z;
}

// z <-> x ^ y
static unsigned mkXor(SATSolver& solver, unsigned x, unsigned y)
{
  const unsigned z = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(y, true));  cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(y, false)); cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(y, false)); cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(y, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  return z;
}

// The bits of -x. Two's complement negation is ~x + 1, and the whole of that
// carry is a prefix OR: bit j comes out flipped exactly when some bit below
// j is set. Below the lowest set bit nothing flips, at it the 1 survives,
// and above it every bit is complemented -- which is the same three cases
// read off the addition.
static std::vector<unsigned> encodeNegate(SATSolver& solver,
                                          const std::vector<unsigned>& x,
                                          unsigned width)
{
  std::vector<unsigned> neg(width);
  unsigned lower = pinnedVar(solver, false);
  for (unsigned j = 0; j < width; ++j)
  {
    neg[j] = mkXor(solver, x[j], lower);
    if (j + 1 < width)
      lower = mkOr(solver, lower, x[j]);
  }
  return neg;
}

// Where the highest set bit is, or -1 for zero. `2^topSetBit(v) <=u v`, and
// it is the largest exponent for which that holds.
static int topSetBit(const std::vector<bool>& bits)
{
  for (int i = (int)bits.size() - 1; i >= 0; --i)
    if (bits[i])
      return i;
  return -1;
}

// The exponent of a power of two, or -1 for anything else. Exactly one bit
// set: zero has none and is not one.
static int powerOfTwoExponent(const std::vector<bool>& bits)
{
  int found = -1;
  for (unsigned i = 0; i < bits.size(); ++i)
    if (bits[i])
    {
      if (found >= 0)
        return -1;
      found = (int)i;
    }
  return found;
}

// The same negation encodeNegate() builds, over values rather than
// variables, so that the scan can decide whether the schema applies without
// putting a single clause in the solver.
static std::vector<bool> negatedValue(const std::vector<bool>& bits)
{
  std::vector<bool> out(bits.size());
  bool lower = false;
  for (unsigned j = 0; j < bits.size(); ++j)
  {
    out[j] = (bits[j] != lower);
    lower = lower || bits[j];
  }
  return out;
}

// Trailing zeros, which is the whole width when nothing is set.
static unsigned trailingZeros(const std::vector<bool>& bits)
{
  for (unsigned i = 0; i < bits.size(); ++i)
    if (bits[i])
      return i;
  return bits.size();
}

// Does the candidate's product agree with `other` shifted up by `shift`?
static bool productIsShift(const std::vector<bool>& other, unsigned shift,
                           const std::vector<bool>& tBits)
{
  for (unsigned j = 0; j < tBits.size(); ++j)
  {
    const bool shifted = (j >= shift) && other[j - shift];
    if (tBits[j] != shifted)
      return false;
  }
  return true;
}

// The MulLemma facts, in the order the chooser offers them: by how often
// they fired in the solver they come from, as with the quotient facts.
static const MulLemma MUL_LEMMAS[] = {
    MulLemma::FactorUnchangedByMaskedShift, // 75 firings
    MulLemma::FactorAndProductNotOr,        // 5

    // The rest of the source's general registry, which fired at most four
    // times apiece and is behind `mul-extra`, off. Source order, there
    // being no count worth sorting by.
    MulLemma::Mul5,
    MulLemma::Mul7,
    MulLemma::Mul9,
    MulLemma::Mul10,
    MulLemma::Mul11,
    MulLemma::Mul12,
    MulLemma::Mul13,
    MulLemma::Mul14,
    MulLemma::Mul15,
    MulLemma::Mul16,
    MulLemma::Mul17,
    MulLemma::Mul18,
    MulLemma::Mul19};

static const unsigned MUL_LEMMA_COUNT =
    sizeof(MUL_LEMMAS) / sizeof(MUL_LEMMAS[0]);

const MulLemma* mulLemmaTable(unsigned& count)
{
  count = MUL_LEMMA_COUNT;
  return MUL_LEMMAS;
}

// The ADD facts, in the source's order. There is no firing count to sort by
// -- none of them fired -- and no reason to invent one.
static const AddLemma ADD_LEMMAS[] = {
    AddLemma::AddZero,    AddLemma::AddSame,    AddLemma::AddInv,
    AddLemma::AddOverflow, AddLemma::AddNoOverflow, AddLemma::AddOr,
    AddLemma::AddRef6,    AddLemma::AddRef7,    AddLemma::AddRef8,
    AddLemma::AddRef9,    AddLemma::AddRef10,   AddLemma::AddRef11,
    AddLemma::AddRef12};

static const unsigned ADD_LEMMA_COUNT =
    sizeof(ADD_LEMMAS) / sizeof(ADD_LEMMAS[0]);

const AddLemma* addLemmaTable(unsigned& count)
{
  count = ADD_LEMMA_COUNT;
  return ADD_LEMMAS;
}

// The record's operands as it actually adds them: a syntactic negation is
// folded into the record, so the fact is about the two's complement.
static std::vector<bool> effectiveOperand(const std::vector<bool>& bits,
                                          bool negated)
{
  if (!negated)
    return bits;

  std::vector<bool> r(bits.size());
  bool carry = true;
  for (unsigned i = 0; i < bits.size(); ++i)
  {
    const bool inverted = !bits[i];
    r[i] = inverted ^ carry;
    carry = inverted && carry;
  }
  return r;
}

AddSchemaChoice chooseAddSchema(const std::vector<bool>& aBits,
                                const std::vector<bool>& bBits,
                                const std::vector<bool>& tBits, bool aNegated,
                                bool bNegated, uint64_t installedSchemas,
                                uint32_t enabledGroups)
{
  const std::vector<bool> a = effectiveOperand(aBits, aNegated);
  const std::vector<bool> b = effectiveOperand(bBits, bNegated);
  const std::vector<bool>* ops[2] = {&a, &b};
  const unsigned width = (unsigned)tBits.size();

  if (bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::ADD))
    for (unsigned i = 0; i < ADD_LEMMA_COUNT; ++i)
    {
      if (!addLemmaApplicable(ADD_LEMMAS[i], width))
        continue;
      for (unsigned op = 0; op < 2; ++op)
      {
        if ((installedSchemas & addLemmaInstalledBit(i, op)) != 0)
          continue;
        if (!addLemmaHolds(ADD_LEMMAS[i], *ops[op], *ops[1 - op], tBits))
          return {AddSchema::Lemma, ADD_LEMMAS[i], op, i, BVSchemaGroup::ADD};
      }
    }

  const unsigned prefix = lowPrefixWidth(width);
  if (bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::LOW_PREFIX) &&
      (installedSchemas & SCHEMA_INSTALLED_LOW_PREFIX) == 0 &&
      !exactLowPrefixHolds(BVPLUS, a, b, tBits, prefix))
    return {AddSchema::LowPrefix, AddLemma::AddZero, 0, 0,
            BVSchemaGroup::LOW_PREFIX};

  return AddSchemaChoice();
}

// Which family each fact belongs to. Written as a switch with no default so
// that a fact added to the enum and forgotten here is a compile error rather
// than a lemma silently charged to `base` and silently enabled with it.
static BVSchemaGroup mulLemmaGroup(MulLemma lemma)
{
  switch (lemma)
  {
    case MulLemma::FactorUnchangedByMaskedShift: return BVSchemaGroup::MUL8;
    case MulLemma::FactorAndProductNotOr: return BVSchemaGroup::MUL6;

    case MulLemma::Mul5:
    case MulLemma::Mul7:
    case MulLemma::Mul9:
    case MulLemma::Mul10:
    case MulLemma::Mul11:
    case MulLemma::Mul12:
    case MulLemma::Mul13:
    case MulLemma::Mul14:
    case MulLemma::Mul15:
    case MulLemma::Mul16:
    case MulLemma::Mul17:
    case MulLemma::Mul18:
    case MulLemma::Mul19:
      return BVSchemaGroup::MUL_EXTRA;
  }
  return BVSchemaGroup::BASE;
}

MulSchemaChoice chooseMulSchema(const std::vector<bool>& aBits,
                                const std::vector<bool>& bBits,
                                const std::vector<bool>& tBits,
                                uint64_t installedSchemas,
                                uint32_t enabledGroups)
{
  const std::vector<bool>* ops[2] = {&aBits, &bBits};

  // The four schemas below are what merged master already had, so they move
  // together under one name.
  const bool base = bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::BASE);

  // a = 2^k -> t = b << k, and the same read the other way round. Where it
  // applies it says the most of the four: the shift *is* the product for
  // that operand value, so one lemma settles every b at once where a
  // blocking lemma settles one pair. It therefore also always fires when it
  // applies -- this is only ever called over a candidate whose product is
  // already known wrong, and for a power-of-two operand "wrong" and
  // "disagrees with the shift" are the same statement.
  for (unsigned i = 0; base && i < 2; ++i)
  {
    const int k = powerOfTwoExponent(*ops[i]);
    if (k >= 0 && !productIsShift(*ops[1 - i], (unsigned)k, tBits))
      return {MulSchema::Pow2, i, (unsigned)k, 0};
  }

  // a = -2^k -> t = (-b) << k. A power of two is skipped rather than
  // excluded by name: that covers the minimum signed value, which is its own
  // negation and which the schema above has already taken.
  for (unsigned i = 0; base && i < 2; ++i)
  {
    if (powerOfTwoExponent(*ops[i]) >= 0)
      continue;
    const int k = powerOfTwoExponent(negatedValue(*ops[i]));
    if (k >= 0 &&
        !productIsShift(negatedValue(*ops[1 - i]), (unsigned)k, tBits))
      return {MulSchema::NegPow2, i, (unsigned)k, 0};
  }

  // The product carries at least as many trailing zeros as either operand.
  // Check operand 1 before operand 0 so schema selection remains
  // deterministic for this commutative operator.
  static const uint64_t tzInstalled[2] = {
      MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0,
      MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1};
  for (unsigned pass = 0; base && pass < 2; ++pass)
  {
    const unsigned i = 1 - pass;
    if ((installedSchemas & tzInstalled[i]) != 0)
      continue;
    const unsigned zeros = trailingZeros(*ops[i]);
    for (unsigned bit = 0; bit < zeros; ++bit)
      if (tBits[bit])
        return {MulSchema::TrailingZeros, i, 0, 0};
  }

  // t[0] = a[0] & b[0].
  if (base && (installedSchemas & MUL_SCHEMA_INSTALLED_ODD) == 0 &&
      tBits[0] != (aBits[0] && bBits[0]))
    return {MulSchema::Odd, 0, 0, 0};

  // Then the wider facts, first one the candidate breaks. Each is written
  // over an `x` and an `s` the operation does not distinguish, so both
  // readings are offered and each carries its own installed-flag.
  const unsigned width = (unsigned)tBits.size();
  for (unsigned i = 0; i < MUL_LEMMA_COUNT; ++i)
  {
    const BVSchemaGroup group = mulLemmaGroup(MUL_LEMMAS[i]);
    if (!bvSchemaGroupEnabled(enabledGroups, group))
      continue;
    if (!mulLemmaApplicable(MUL_LEMMAS[i], width))
      continue;
    for (unsigned op = 0; op < 2; ++op)
    {
      if ((installedSchemas & mulLemmaInstalledBit(i, op)) != 0)
        continue;
      if (!mulLemmaHolds(MUL_LEMMAS[i], *ops[op], *ops[1 - op], tBits))
        return {MulSchema::Lemma, op, 0, i, group};
    }
  }

  // Last, the exact low bits, which say something narrow and certain where
  // everything above says something wide and loose.
  const unsigned prefix = lowPrefixWidth(width);
  if (bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::LOW_PREFIX) &&
      (installedSchemas & SCHEMA_INSTALLED_LOW_PREFIX) == 0 &&
      !exactLowPrefixHolds(BVMULT, aBits, bBits, tBits, prefix))
    return {MulSchema::LowPrefix, 0, 0, 0, BVSchemaGroup::LOW_PREFIX};

  return MulSchemaChoice();
}

std::vector<int> divSchemaSources(Kind opKind, unsigned width,
                                  const DivSchemaChoice& choice)
{
  std::vector<int> source(width, DIV_SOURCE_ZERO);

  if (choice.schema == DivSchema::DivisorZero)
  {
    // What the unabstracted BBDivMod answers over a zero divisor, and what
    // SMT-LIB says: the quotient is all ones and the remainder is the
    // dividend. The two are not the same value, so each is written out.
    for (unsigned i = 0; i < width; ++i)
      source[i] = (opKind == BVDIV) ? DIV_SOURCE_ONE : (int)i;
    return source;
  }

  if (choice.schema != DivSchema::Pow2Divisor)
    return source;

  const unsigned shift = choice.shift;
  if (opKind == BVDIV)
  {
    // a >> shift. The bits above the shift come down and zeros arrive at
    // the top, which is what the vector was filled with.
    for (unsigned i = 0; i + shift < width; ++i)
      source[i] = (int)(i + shift);
  }
  else
  {
    // a & (2^shift - 1). The bits below the shift stay where they are and
    // everything at or above it goes.
    for (unsigned i = 0; i < shift && i < width; ++i)
      source[i] = (int)i;
  }
  return source;
}

// Does the candidate's result already say what these sources say it must?
// A schema the candidate satisfies is no use as a refinement: it would let
// the search offer the same model again, and the round would be spent for
// nothing.
static bool resultMatchesSources(const std::vector<int>& source,
                                 const std::vector<bool>& aBits,
                                 const std::vector<bool>& tBits)
{
  for (unsigned i = 0; i < source.size(); ++i)
  {
    const bool want = (source[i] == DIV_SOURCE_ZERO)  ? false
                      : (source[i] == DIV_SOURCE_ONE) ? true
                                                      : aBits[source[i]];
    if (tBits[i] != want)
      return false;
  }
  return true;
}

// Unsigned comparison over the bit vectors a candidate holds, least
// significant bit first. Written here rather than reusing computeBVLE
// because that one is about the operands of an abstracted comparison and
// this one is about a result the abstraction chose.
static bool valueLessOrEqual(const std::vector<bool>& left,
                             const std::vector<bool>& right)
{
  for (int i = (int)left.size() - 1; i >= 0; --i)
  {
    if (left[i] != right[i])
      return right[i];
  }
  return true;
}

// `bits >> by`, zeros arriving at the top: the value the shift bound holds
// the quotient under.
static std::vector<bool> shiftedRight(const std::vector<bool>& bits,
                                      unsigned by)
{
  const unsigned W = (unsigned)bits.size();
  std::vector<bool> out(W, false);
  for (unsigned i = 0; i + by < W; ++i)
    out[i] = bits[i + by];
  return out;
}

// Every schema lemma is counted here and nowhere else, so the total and its
// partition cannot drift: a family that forgets to charge itself shows up as
// a total that no longer equals the sum, which a test checks.
static void countSchemaLemma(STPMgr* bm, BVSchemaGroup group)
{
  bm->UserFlags.coverage.bv_schema_lemmas++;
  bm->UserFlags.coverage.bv_schema_group_lemmas[(unsigned)group]++;
}

static bool valueIsZero(const std::vector<bool>& bits)
{
  for (unsigned i = 0; i < bits.size(); ++i)
    if (bits[i])
      return false;
  return true;
}

// The DivLemma facts, in the order the chooser offers them: by how often
// they fired in the solver they come from, measured over the queries this
// is for. A candidate usually breaks more than one, so the order decides
// which round buys which fact, and buying the most productive first is the
// cheapest guess available.
static const DivLemma DIV_LEMMAS[] = {
    DivLemma::DivisorAboveShiftedDividend,           // 280 firings
    DivLemma::QuotientBelowNegatedDivisor,           // 200
    DivLemma::DividendAboveNegatedAnd,               // 187
    // Not the source's, so it has no firing count. Placed here on the other
    // measure: what it rules out that the rest of the table does not, which
    // at six bits is 2.42% against 2.75% for the best fact above it and
    // 0.00% for five of the ones below.
    DivLemma::QuotientIsOne,
    DivLemma::DividendZero,                          // 171
    DivLemma::DivisorEqualsDividend,                 // 162
    DivLemma::DivisorLessOneAboveShiftedDividend,    // 161
    DivLemma::DividendAboveShiftedDoubleQuotient,    // 125
    DivLemma::QuotientNotNegatedAnd,                 // 62
    DivLemma::DivisorAllOnes,                        // 59
    DivLemma::DividendAboveDoubledShiftedDivisor,    // 54
    DivLemma::DividendNotTwiceQuotientPlusOr,        // 26
    DivLemma::QuotientAboveDoubledShiftedDividend,   // 14
    DivLemma::DividendAboveOrAndDoubledDivisor,      // 10
    DivLemma::MaskedDividendAboveDivisorAndQuotient, // 9
    DivLemma::DividendAboveQuotientXorShifted,       // 3
    DivLemma::ShiftedDividendNotOr,                  // 3
    DivLemma::DividendAboveOrAndDoubledQuotient,     // 2
    DivLemma::DividendAboveDivisorXorShifted,        // 2

    // The rest of the source's registry, which fired nothing on the corpus
    // the counts above come from and is behind `udiv-extra`, off. No count
    // to sort by, so this tail keeps the source's own order and
    // reconciliation against it stays mechanical.
    DivLemma::Udiv10,
    DivLemma::Udiv11,
    DivLemma::Udiv20,
    DivLemma::Udiv21,
    DivLemma::Udiv22,
    DivLemma::Udiv23,
    DivLemma::Udiv24,
    DivLemma::Udiv27,
    DivLemma::Udiv28,
    DivLemma::Udiv29,
    DivLemma::Udiv30,
    DivLemma::Udiv31,
    DivLemma::Udiv33,
    DivLemma::Udiv34,
    DivLemma::Udiv36};

static const unsigned DIV_LEMMA_COUNT =
    sizeof(DIV_LEMMAS) / sizeof(DIV_LEMMAS[0]);

const DivLemma* divLemmaTable(unsigned& count)
{
  count = DIV_LEMMA_COUNT;
  return DIV_LEMMAS;
}

// The RemLemma facts, in the order the chooser offers them. Not a firing
// count this time -- nothing fired, because the family these were measured
// on has no remainders to speak of -- but the order they are published in,
// which puts the three that settle the operation outright ahead of the
// eight synthesised inequalities.
static const RemLemma REM_LEMMAS[] = {
    RemLemma::DividendZero,
    RemLemma::DivisorEqualsDividend,
    RemLemma::DividendBelowDivisor,
    // Ours rather than the source's, and next because it settles the
    // operation outright the way the three above it do: 2.70% beyond the rest
    // of the table at six bits, which is third of the twelve.
    RemLemma::RemainderIsDifference,
    RemLemma::DividendWithinDivisorOrRemainder,
    RemLemma::DividendAboveRemainderOrAnd,
    RemLemma::RemainderOutsideOperandsNotOne,
    RemLemma::RemainderNotOrOfComplements,
    RemLemma::RemainderInOperandsAboveLowBit,
    RemLemma::DividendNotOrOfNegations,
    RemLemma::DifferenceAboveRemainder,
    RemLemma::XorAboveRemainder,
    // Last, and off: the source defines it and does not enable it, and STP
    // carries the same bound as a schema. See `urem7`.
    RemLemma::Urem7};

static const unsigned REM_LEMMA_COUNT =
    sizeof(REM_LEMMAS) / sizeof(REM_LEMMAS[0]);

const RemLemma* remLemmaTable(unsigned& count)
{
  count = REM_LEMMA_COUNT;
  return REM_LEMMAS;
}

// Which family each fact belongs to, as for the product facts above: a
// switch with no default, so a new fact has to say where it goes.
static BVSchemaGroup divLemmaGroup(DivLemma lemma)
{
  switch (lemma)
  {
    // What merged master already had.
    case DivLemma::DividendZero:
    case DivLemma::DivisorEqualsDividend:
    case DivLemma::DivisorAllOnes:
    case DivLemma::QuotientBelowNegatedDivisor:
    case DivLemma::DividendAboveNegatedAnd:
    case DivLemma::DivisorAboveShiftedDividend:
    case DivLemma::DivisorLessOneAboveShiftedDividend:
      return BVSchemaGroup::BASE;

    // Ours, and paired with the remainder reading of the same premise.
    case DivLemma::QuotientIsOne: return BVSchemaGroup::QUOTIENT_ONE;

    // The rest of the imported facts that fired on the ranking corpus.
    case DivLemma::DividendAboveShiftedDoubleQuotient:
    case DivLemma::QuotientNotNegatedAnd:
    case DivLemma::DividendAboveDoubledShiftedDivisor:
    case DivLemma::DividendNotTwiceQuotientPlusOr:
    case DivLemma::QuotientAboveDoubledShiftedDividend:
    case DivLemma::DividendAboveOrAndDoubledDivisor:
    case DivLemma::MaskedDividendAboveDivisorAndQuotient:
    case DivLemma::DividendAboveQuotientXorShifted:
    case DivLemma::ShiftedDividendNotOr:
    case DivLemma::DividendAboveOrAndDoubledQuotient:
    case DivLemma::DividendAboveDivisorXorShifted:
      return BVSchemaGroup::UDIV;

    // The imported tail that fired nothing.
    case DivLemma::Udiv10:
    case DivLemma::Udiv11:
    case DivLemma::Udiv20:
    case DivLemma::Udiv21:
    case DivLemma::Udiv22:
    case DivLemma::Udiv23:
    case DivLemma::Udiv24:
    case DivLemma::Udiv27:
    case DivLemma::Udiv28:
    case DivLemma::Udiv29:
    case DivLemma::Udiv30:
    case DivLemma::Udiv31:
    case DivLemma::Udiv33:
    case DivLemma::Udiv34:
    case DivLemma::Udiv36:
      return BVSchemaGroup::UDIV_EXTRA;
  }
  return BVSchemaGroup::BASE;
}

static BVSchemaGroup remLemmaGroup(RemLemma lemma)
{
  switch (lemma)
  {
    case RemLemma::RemainderIsDifference: return BVSchemaGroup::QUOTIENT_ONE;
    case RemLemma::Urem7: return BVSchemaGroup::UREM7;

    case RemLemma::DividendZero:
    case RemLemma::DivisorEqualsDividend:
    case RemLemma::DividendBelowDivisor:
    case RemLemma::DividendWithinDivisorOrRemainder:
    case RemLemma::DividendAboveRemainderOrAnd:
    case RemLemma::RemainderOutsideOperandsNotOne:
    case RemLemma::RemainderNotOrOfComplements:
    case RemLemma::RemainderInOperandsAboveLowBit:
    case RemLemma::DividendNotOrOfNegations:
    case RemLemma::DifferenceAboveRemainder:
    case RemLemma::XorAboveRemainder:
      return BVSchemaGroup::UREM;
  }
  return BVSchemaGroup::UREM;
}

DivSchemaChoice chooseDivSchema(Kind opKind, const std::vector<bool>& aBits,
                                const std::vector<bool>& bBits,
                                const std::vector<bool>& tBits,
                                uint64_t installedSchemas,
                                uint32_t enabledGroups)
{
  const unsigned width = (unsigned)tBits.size();
  const bool divisorZero = valueIsZero(bBits);
  // The divisor-value schemas and the three bounds are what merged master
  // already had, so they move together.
  const bool base = bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::BASE);

  // The divisor-guarded facts first, where they apply: each says what the
  // operation *is* for that divisor, which is more than any bound can say.
  // Zero is not a power of two, so the two never contend and the order
  // between them is a formality.
  if (base && divisorZero)
  {
    const DivSchemaChoice choice{DivSchema::DivisorZero, 0};
    if (!resultMatchesSources(divSchemaSources(opKind, width, choice), aBits,
                              tBits))
      return choice;
  }
  else if (base)
  {
    const int k = powerOfTwoExponent(bBits);
    if (k >= 0)
    {
      const DivSchemaChoice choice{DivSchema::Pow2Divisor, (unsigned)k};
      if (!resultMatchesSources(divSchemaSources(opKind, width, choice), aBits,
                                tBits))
        return choice;
    }
  }

  // Then the bounds, which name no divisor and so are the ones a candidate
  // over a wide random divisor actually runs into. Each is offered only
  // once: they are unconditional, so once installed no candidate can
  // contradict them again and re-emitting one would spend a round on a
  // clause the solver already has.
  if (opKind == BVMOD)
  {
    // r <=u a, with no premise at all -- it holds over a zero divisor too,
    // where the remainder is the dividend.
    if (base &&
        (installedSchemas &
         DIV_SCHEMA_INSTALLED_REMAINDER_AT_MOST_DIVIDEND) == 0 &&
        !valueLessOrEqual(tBits, aBits))
      return {DivSchema::RemainderAtMostDividend, 0};

    // b != 0 -> r <u b.
    if (base &&
        (installedSchemas & DIV_SCHEMA_INSTALLED_REMAINDER_BELOW_DIVISOR) ==
            0 &&
        !divisorZero && valueLessOrEqual(bBits, tBits))
      return {DivSchema::RemainderBelowDivisor, 0};

    // Then the wider facts about `t = a urem b`, first one the candidate
    // breaks. Same loop as the quotient's below and for the same reasons;
    // only the table differs.
    for (unsigned i = 0; i < REM_LEMMA_COUNT; ++i)
    {
      const BVSchemaGroup group = remLemmaGroup(REM_LEMMAS[i]);
      if (!bvSchemaGroupEnabled(enabledGroups, group))
        continue;
      if ((installedSchemas & divLemmaInstalledBit(i)) != 0)
        continue;
      if (!remLemmaApplicable(REM_LEMMAS[i], width))
        continue;
      if (!remLemmaHolds(REM_LEMMAS[i], aBits, bBits, tBits))
        return {DivSchema::Lemma, 0, i, group};
    }
  }
  else if (opKind == BVDIV)
  {
    // b != 0 -> t <=u a, which is the shift bound below at k = 0 and is kept
    // separate because it is the one reading of it that needs no shift.
    if (base &&
        (installedSchemas &
         DIV_SCHEMA_INSTALLED_QUOTIENT_AT_MOST_DIVIDEND) == 0 &&
        !divisorZero && !valueLessOrEqual(tBits, aBits))
      return {DivSchema::QuotientAtMostDividend, 0, 0};


    // Then the wider facts, first one the candidate breaks. Quotients only:
    // every one of them is about `t = a udiv b`.
    for (unsigned i = 0; i < DIV_LEMMA_COUNT; ++i)
    {
      const BVSchemaGroup group = divLemmaGroup(DIV_LEMMAS[i]);
      if (!bvSchemaGroupEnabled(enabledGroups, group))
        continue;
      if ((installedSchemas & divLemmaInstalledBit(i)) != 0)
        continue;
      // A fact the source marks as restricted is skipped at the widths it
      // does not hold at, rather than left out of the table: the width that
      // reaches here is whatever --bv-abstraction-width was set to.
      if (!divLemmaApplicable(DIV_LEMMAS[i], width))
        continue;
      if (!divLemmaHolds(DIV_LEMMAS[i], aBits, bBits, tBits))
        return {DivSchema::Lemma, 0, i, group};
    }

    // Then b >=u 2^k -> t <=u (a >> k), at the largest k the guard allows,
    // which is where the candidate divisor's top bit sits.
    //
    // Behind the tables because it is the one fact here that a candidate can
    // break over and over: the guard names a magnitude, and a search that
    // has been told about one magnitude answers with another. Offered ahead
    // of the wider facts it fired 28 times on a query those facts settle in
    // six rounds, and they never got a turn. Behind them it is what it
    // should be -- the thing that is tried when nothing sharper applies.
    //
    // But ahead of the thresholds below, and that ordering is not a
    // preference. This family has an allowance of two per abstraction and
    // the thresholds have none: there is a k for every bit, and a candidate
    // that keeps moving its quotient's magnitude keeps supplying one. Tried
    // second, this bound can be starved outright -- with both families on,
    // the query pinned for it goes from five rounds to not finishing inside
    // a minute, because the allowance is gone before its turn arrives. The
    // capped family cannot do the same to the uncapped one: after two
    // instances it stops offering.
    //
    // `a >> k` only falls as k rises, so a candidate that breaks the bound at
    // any k breaks it at every k above, and the smallest of those has the
    // broadest guard -- which looks like the better buy and measures as the
    // worse one. Each round installs one k, and a search that has been told
    // `b >=u 2` moves to a quotient that only breaks the bound at k = 2, then
    // at k = 3: it walks the exponent upward one round at a time and wants k
    // rounds to settle a query about 2^k. At 64 bits that converges in 23
    // rounds; at 128 it does not, because the round allowance runs out first.
    //
    // The top bit costs one round for a divisor whose magnitude the query
    // pins, which is the case this is for.
    //
    // A zero divisor has no top bit and the fact says nothing about it.
    const int top = divisorZero ? -1 : topSetBit(bBits);
    if (bvSchemaGroupEnabled(enabledGroups,
                             BVSchemaGroup::DIVISOR_MAGNITUDE) &&
        top >= 1 && divShiftBoundsLeft(installedSchemas) &&
        !valueLessOrEqual(tBits, shiftedRight(aBits, (unsigned)top)))
      return {DivSchema::DivisorAtLeastPow2, (unsigned)top, 0,
              BVSchemaGroup::DIVISOR_MAGNITUDE};

    // q >=u 2^k  <->  s <=u (a >> k), at the two k around the candidate
    // quotient's top bit.
    //
    // Every k at or below the quotient's highest set bit has a true left
    // side and every k above it a false one, and the true quotient has that
    // same shape. So if the candidate's magnitude band and the divisor
    // disagree, one of the two k on the boundary of the candidate's band
    // witnesses it, and checking only those two is not a heuristic -- it is
    // where the disagreement has to be. k = 0 is skipped: `q >=u 1` is
    // `q != 0`, which the facts above already carry.
    if (bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::QUOTIENT_THRESHOLDS))
    {
      const auto bandDisagrees = [&](unsigned k) {
        std::vector<bool> shifted = shiftedRight(aBits, k);
        bool quotientAtLeast = false;
        for (unsigned i = k; i < width; ++i)
          quotientAtLeast = quotientAtLeast || tBits[i];
        return quotientAtLeast != valueLessOrEqual(bBits, shifted);
      };

      int quotientTop = -1;
      for (int i = (int)width - 1; i >= 0; --i)
        if (tBits[i]) { quotientTop = i; break; }

      if (quotientTop > 0 && bandDisagrees((unsigned)quotientTop))
        return {DivSchema::QuotientPow2Threshold, (unsigned)quotientTop, 0,
                BVSchemaGroup::QUOTIENT_THRESHOLDS};

      const unsigned above =
          (quotientTop < 1) ? 1u : (unsigned)quotientTop + 1;
      if (above < width && bandDisagrees(above))
        return {DivSchema::QuotientPow2Threshold, above, 0,
                BVSchemaGroup::QUOTIENT_THRESHOLDS};
    }
  }

  return DivSchemaChoice();
}

static const char* divSchemaName(DivSchema schema)
{
  switch (schema)
  {
    case DivSchema::DivisorZero: return "zero-divisor";
    case DivSchema::Pow2Divisor: return "power-of-two-divisor";
    case DivSchema::DivisorAtLeastPow2:
      return "divisor-at-least-power-of-two";
    case DivSchema::QuotientPow2Threshold:
      return "quotient-power-of-two-threshold";
    case DivSchema::RemainderAtMostDividend: return "remainder-at-most-dividend";
    case DivSchema::RemainderBelowDivisor: return "remainder-below-divisor";
    case DivSchema::QuotientAtMostDividend: return "quotient-at-most-dividend";
    case DivSchema::Lemma: return "lemma";
    case DivSchema::None: break;
  }
  return "none";
}

// How far past the lowest wrong bit a piece-at-a-time escalation reaches.
// A fixed 32-bit step; there is no measurement behind this value, which is
// part of why the flag that reaches it is off.
static const unsigned BV_INC_BITBLAST_STEP = 32;

// The operation again, narrowed to its low `upto` bits.
//
// The low bits of a truncated product depend only on the low bits of its
// operands, so `t[u:0] = (a[u:0] * b[u:0])[u:0]` is a theorem about the
// whole multiplication rather than an approximation of it -- which is what
// lets a piece of the encoding be installed and the rest left for later.
// The narrowed operands are real extracts and not merely a smaller width
// passed alongside the same node, because the multiplier reads its operands
// for constant detection and Booth recoding and would read the wrong values
// out of the wider ones.
//
// A null node comes back where the narrowing does not leave a
// multiplication standing -- the factory folds a product of two constants,
// which cannot reach here from a query the simplifier has been over, but
// costs one branch to be sure of. The caller encodes the whole width
// instead.
static ASTNode narrowedProduct(STPMgr* bm, const ASTNode& term, unsigned upto)
{
  NodeFactory* nf = bm->defaultNodeFactory;
  const ASTNode high = bm->CreateBVConst(32, upto - 1);
  const ASTNode low = bm->CreateZeroConst(32);

  ASTNode operands[2];
  for (unsigned i = 0; i < 2; ++i)
    operands[i] = (term[i].GetValueWidth() == upto)
                      ? term[i]
                      : nf->CreateTerm(BVEXTRACT, upto, term[i], high, low);

  const ASTNode narrowed =
      nf->CreateTerm(BVMULT, upto, operands[0], operands[1]);
  return narrowed.GetKind() == BVMULT ? narrowed : ASTNode();
}

unsigned valueLemmaAllowance(const UserDefinedFlags& uf, unsigned width)
{
  const unsigned ceiling = uf.bv_term_abstraction_rounds;
  if (ceiling == 0)
    return 0; // never escalate: enumerate without limit

  const unsigned divisor = uf.bv_term_abstraction_value_divisor;
  if (divisor == 0)
    return ceiling; // the flat allowance this replaced

  // At least one. A rate that rounds to nothing would escalate before the
  // abstraction has been given a single chance to pay, which is not what
  // "scale it with the width" is meant to mean at narrow widths -- and
  // width zero does not occur, since the type checker gives every operation
  // a width and the abstraction has a floor besides.
  const unsigned scaled = width / divisor;
  return std::min(ceiling, scaled == 0 ? 1u : scaled);
}

static const char* mulSchemaName(MulSchema schema)
{
  switch (schema)
  {
    case MulSchema::Odd: return "odd";
    case MulSchema::TrailingZeros: return "trailing-zeros";
    case MulSchema::Pow2: return "power-of-two";
    case MulSchema::NegPow2: return "negated-power-of-two";
    case MulSchema::LowPrefix: return "exact-low-prefix";
    // Named by mulLemmaName instead; the caller asks that when it has one.
    case MulSchema::Lemma:
    case MulSchema::None: break;
  }
  return "none";
}

// result[0] <-> a[0] & b[0].
static void encodeMulOdd(SATSolver& solver, const std::vector<unsigned>& a,
                         const std::vector<unsigned>& b,
                         const std::vector<unsigned>& result)
{
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(result[0], true));  cl.push(SATSolver::mkLit(a[0], false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(result[0], true));  cl.push(SATSolver::mkLit(b[0], false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(result[0], false)); cl.push(SATSolver::mkLit(a[0], true)); cl.push(SATSolver::mkLit(b[0], true)); solver.addClause(cl);
}

// result[i] -> some bit of `op` at or below i, one clause per bit. The
// product cannot have fewer trailing zeros than an operand, and truncating
// it to the width does not change its low bits, so this holds of the
// truncated product too.
static void encodeMulTrailingZeros(SATSolver& solver,
                                   const std::vector<unsigned>& op,
                                   const std::vector<unsigned>& result,
                                   unsigned width)
{
  for (unsigned bit = 0; bit < width; ++bit)
  {
    SATSolver::vec_literals cl;
    cl.push(SATSolver::mkLit(result[bit], true));
    for (unsigned j = 0; j <= bit; ++j)
      cl.push(SATSolver::mkLit(op[j], false));
    solver.addClause(cl);
  }
}

// fixed = fixedBits -> result = source << shift.
//
// The premise is the very disjunction a blocking lemma opens with -- false
// exactly on the candidate's own operand value -- and that is the whole
// difference between the two: this leaves the other operand free, so it
// rules out 2^W pairs where the blocking lemma rules out one.
static void encodeMulShiftUnderValue(SATSolver& solver,
                                     const std::vector<unsigned>& fixedVars,
                                     const std::vector<bool>& fixedBits,
                                     const std::vector<unsigned>& source,
                                     const std::vector<unsigned>& result,
                                     unsigned width, unsigned shift)
{
  const auto guard = [&](SATSolver::vec_literals& cl) {
    cl.clear();
    for (unsigned i = 0; i < width; ++i)
      cl.push(SATSolver::mkLit(fixedVars[i], fixedBits[i]));
  };

  SATSolver::vec_literals cl;
  for (unsigned bit = 0; bit < width; ++bit)
  {
    if (bit < shift)
    {
      // Shifted in from below: zero, whatever the source holds.
      guard(cl);
      cl.push(SATSolver::mkLit(result[bit], true));
      solver.addClause(cl);
      continue;
    }

    const unsigned src = source[bit - shift];
    guard(cl);
    cl.push(SATSolver::mkLit(result[bit], true));
    cl.push(SATSolver::mkLit(src, false));
    solver.addClause(cl);

    guard(cl);
    cl.push(SATSolver::mkLit(result[bit], false));
    cl.push(SATSolver::mkLit(src, true));
    solver.addClause(cl);
  }
}

// divisor = divisorBits -> every result bit is a constant or a bit of the
// dividend, as `source` says.
//
// The premise is the blocking lemma's opening disjunction, exactly as the
// multiplication schemas use it: false only on the candidate's own divisor,
// and leaving the dividend entirely free. That is what makes one of these
// worth 2^W blocking lemmas over the same divisor.
// A variable that holds exactly when `lv <= rv`, over the operand bits
// already in the solver.
//
// From the least significant bit up, so that the most significant
// *differing* bit is the one that decides. Each step keeps the accumulator
// when the two bits agree and overrides it when they differ, so whichever
// bit is visited last among the differing ones settles the answer -- which
// is the top one only in this direction. Run downwards, as this once was,
// the bottom differing bit won instead, and the chain answered something
// that is not a comparison at all: it disagreed with `a <= b` on 31616 of
// the 65536 pairs of eight-bit values. The lemma then pinned the abstraction
// to that, and a query whose comparison the pinned value contradicted came
// back unsat.
//
// The sign bit is therefore also the last step, which is where flipping its
// sense belongs: for a signed comparison a leading 1 is the smaller side, so
// the roles of the two operands invert at that bit alone.
//
// The accumulator starts true, which is what makes this `<=` rather than
// `<`: two equal operands never reach a differing bit, so nothing overrides
// it.
unsigned encodeLessOrEqual(SATSolver& solver, const std::vector<unsigned>& lv,
                           const std::vector<unsigned>& rv, unsigned width,
                           bool isSigned)
{
  unsigned carryVar = solver.newVar();
  solver.setFrozen(carryVar);
  {
    SATSolver::vec_literals cl;
    cl.push(SATSolver::mkLit(carryVar, false));
    solver.addClause(cl);
  }

  for (int bit = 0; bit < (int)width; ++bit)
  {
    unsigned a = lv[bit];
    unsigned b = rv[bit];
    bool flipSign = (isSigned && bit == (int)width - 1);

    auto xP = SATSolver::mkLit(a, !flipSign);
    auto xN = SATSolver::mkLit(a, flipSign);
    auto yP = SATSolver::mkLit(b, flipSign);
    auto yN = SATSolver::mkLit(b, !flipSign);
    auto zP = SATSolver::mkLit(carryVar, false);
    auto zN = SATSolver::mkLit(carryVar, true);

    unsigned nc = solver.newVar();
    solver.setFrozen(nc);

    SATSolver::vec_literals cl;
    cl.clear(); cl.push(xN); cl.push(yN); cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(xN); cl.push(zN); cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(yN); cl.push(zN); cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(xP); cl.push(yP); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);
    cl.clear(); cl.push(xP); cl.push(zP); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);
    cl.clear(); cl.push(yP); cl.push(zP); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);

    carryVar = nc;
  }

  return carryVar;
}

// The three bounds, each written straight onto the comparison chain.
//
// Where a bound carries the premise `b != 0`, it is spent as its
// contrapositive rather than through a fresh variable standing for the
// premise: `b != 0 -> P` is `not P -> b = 0`, and `b = 0` is a conjunction,
// so what goes in is one binary clause per divisor bit. No definition, no
// extra variable, and the solver sees the premise on every bit rather than
// behind one literal it has to reason through.
static unsigned mkAnd(SATSolver& solver, unsigned x, unsigned y)
{
  const unsigned z = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(z, true));  cl.push(SATSolver::mkLit(x, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(z, true));  cl.push(SATSolver::mkLit(y, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(z, false)); cl.push(SATSolver::mkLit(x, true)); cl.push(SATSolver::mkLit(y, true)); solver.addClause(cl);
  return z;
}

static void addEquivalence(SATSolver& solver, unsigned x, unsigned y)
{
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(y, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(y, true));  solver.addClause(cl);
}

unsigned lowPrefixWidth(unsigned width)
{
  return width < 3 ? width : 3;
}

bool exactLowPrefixHolds(Kind opKind, const std::vector<bool>& aBits,
                         const std::vector<bool>& bBits,
                         const std::vector<bool>& resultBits,
                         unsigned prefixBits)
{
  assert(opKind == BVPLUS || opKind == BVMULT);
  assert(prefixBits > 0 && prefixBits <= resultBits.size());

  std::vector<bool> expected(prefixBits, false);
  if (opKind == BVPLUS)
  {
    bool carry = false;
    for (unsigned i = 0; i < prefixBits; ++i)
    {
      expected[i] = (aBits[i] != bBits[i]) != carry;
      carry =
          (aBits[i] && bBits[i]) || (carry && (aBits[i] || bBits[i]));
    }
  }
  else
  {
    // Each low shifted copy of b, added into the prefix. No operand bit at
    // or above prefixBits can reach a product bit below it, which is the
    // whole reason this is a theorem about the multiplication rather than
    // about the low bits of one.
    for (unsigned i = 0; i < prefixBits; ++i)
    {
      if (!aBits[i])
        continue;
      bool carry = false;
      for (unsigned j = 0; i + j < prefixBits; ++j)
      {
        const unsigned bit = i + j;
        const bool addend = bBits[j];
        const bool sum = (expected[bit] != addend) != carry;
        carry = (expected[bit] && addend) || (carry && (expected[bit] || addend));
        expected[bit] = sum;
      }
    }
  }

  for (unsigned i = 0; i < prefixBits; ++i)
    if (expected[i] != resultBits[i])
      return false;
  return true;
}

// The low `prefixBits` of the sum, a full-adder row at a time.
//
// The carry into bit zero is a constant: an operand the record negates
// contributes `~v + 1`, and the blaster refuses to abstract an addition
// whose operands are both negated, so exactly one increment is ever
// outstanding. Above the prefix nothing is emitted -- the carry out of the
// top row is dropped and the result's high bits stay free.
void encodeAddLowPrefix(SATSolver& solver, const std::vector<unsigned>& aVars,
                        const std::vector<unsigned>& bVars,
                        const std::vector<unsigned>& resultVars,
                        unsigned prefixBits, bool aNegated, bool bNegated)
{
  assert(prefixBits > 0);
  assert(!(aNegated && bNegated));

  unsigned carryVar = pinnedVar(solver, aNegated != bNegated);
  for (unsigned bit = 0; bit < prefixBits; ++bit)
  {
    const unsigned a = aVars[bit];
    const unsigned b = bVars[bit];
    const unsigned result = resultVars[bit];
    const unsigned carry = carryVar;
    SATSolver::vec_literals cl;

    // One clause per row of the three inputs, falsified only by that row
    // paired with the wrong sum bit. Written out of the row rather than
    // transcribed, so a negated operand is a flipped literal and not a
    // second set of clauses.
    for (unsigned row = 0; row < 8; ++row)
    {
      const bool aBit = (row & 1) != 0;
      const bool bBit = (row & 2) != 0;
      const bool carryBit = (row & 4) != 0;
      const bool sum = (aBit != bBit) != carryBit;
      cl.clear();
      cl.push(SATSolver::mkLit(a, aBit != aNegated));
      cl.push(SATSolver::mkLit(b, bBit != bNegated));
      cl.push(SATSolver::mkLit(carry, carryBit));
      cl.push(SATSolver::mkLit(result, !sum));
      solver.addClause(cl);
    }

    if (bit + 1 == prefixBits)
      break;

    const unsigned next = freshVar(solver);
    cl.clear(); cl.push(SATSolver::mkLit(a, aNegated));   cl.push(SATSolver::mkLit(b, bNegated));   cl.push(SATSolver::mkLit(next, true));  solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(a, aNegated));   cl.push(SATSolver::mkLit(carry, false));  cl.push(SATSolver::mkLit(next, true));  solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(b, bNegated));   cl.push(SATSolver::mkLit(carry, false));  cl.push(SATSolver::mkLit(next, true));  solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(a, !aNegated));  cl.push(SATSolver::mkLit(b, !bNegated));  cl.push(SATSolver::mkLit(next, false)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(a, !aNegated));  cl.push(SATSolver::mkLit(carry, true));   cl.push(SATSolver::mkLit(next, false)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(b, !bNegated));  cl.push(SATSolver::mkLit(carry, true));   cl.push(SATSolver::mkLit(next, false)); solver.addClause(cl);
    carryVar = next;
  }
}

// ... and the low `prefixBits` of the product, column by column. Written out
// rather than looped because there are three columns and the last one drops
// its carry, which a loop would have to special-case anyway.
void encodeMulLowPrefix(SATSolver& solver, const std::vector<unsigned>& aVars,
                        const std::vector<unsigned>& bVars,
                        const std::vector<unsigned>& resultVars,
                        unsigned prefixBits)
{
  assert(prefixBits > 0 && prefixBits <= 3);

  const unsigned p00 = mkAnd(solver, aVars[0], bVars[0]);
  addEquivalence(solver, resultVars[0], p00);
  if (prefixBits == 1)
    return;

  const unsigned p10 = mkAnd(solver, aVars[1], bVars[0]);
  const unsigned p01 = mkAnd(solver, aVars[0], bVars[1]);
  addEquivalence(solver, resultVars[1], mkXor(solver, p10, p01));
  if (prefixBits == 2)
    return;

  // Column two is its three partial products plus the carry out of column
  // one. What it carries is above the prefix and is not built.
  const unsigned carry1 = mkAnd(solver, p10, p01);
  const unsigned p20 = mkAnd(solver, aVars[2], bVars[0]);
  const unsigned p11 = mkAnd(solver, aVars[1], bVars[1]);
  const unsigned p02 = mkAnd(solver, aVars[0], bVars[2]);
  addEquivalence(solver, resultVars[2],
                 mkXor(solver, mkXor(solver, p20, p11),
                       mkXor(solver, p02, carry1)));
}

bool divRemLowPrefixHolds(const std::vector<bool>& dividendBits,
                          const std::vector<bool>& divisorBits,
                          const std::vector<bool>& quotientBits,
                          const std::vector<bool>& remainderBits,
                          unsigned prefixBits)
{
  assert(prefixBits > 0 && prefixBits <= dividendBits.size());

  // low(q*s), then low(that + r), each by the same rule the prefix
  // encoders below build: a low bit of either operation depends only on
  // equally low bits of what goes into it.
  std::vector<bool> product(prefixBits, false);
  for (unsigned i = 0; i < prefixBits; ++i)
  {
    if (!quotientBits[i])
      continue;
    bool carry = false;
    for (unsigned j = 0; i + j < prefixBits; ++j)
    {
      const unsigned bit = i + j;
      const bool addend = divisorBits[j];
      const bool sum = (product[bit] != addend) != carry;
      carry = (product[bit] && addend) || (carry && (product[bit] || addend));
      product[bit] = sum;
    }
  }

  bool carry = false;
  for (unsigned i = 0; i < prefixBits; ++i)
  {
    const bool sum = (product[i] != remainderBits[i]) != carry;
    carry = (product[i] && remainderBits[i]) ||
            (carry && (product[i] || remainderBits[i]));
    if (sum != dividendBits[i])
      return false;
  }
  return true;
}

void encodeDivRemLowPrefix(SATSolver& solver,
                           const std::vector<unsigned>& dividendVars,
                           const std::vector<unsigned>& divisorVars,
                           const std::vector<unsigned>& quotientVars,
                           const std::vector<unsigned>& remainderVars,
                           unsigned prefixBits)
{
  assert(prefixBits > 0 && prefixBits <= 3);

  // The product's low bits get variables of their own; nothing above the
  // prefix is built, so this is a handful of gates rather than a multiplier.
  std::vector<unsigned> product(prefixBits);
  for (unsigned i = 0; i < prefixBits; ++i)
    product[i] = freshVar(solver);

  encodeMulLowPrefix(solver, quotientVars, divisorVars, product, prefixBits);
  encodeAddLowPrefix(solver, product, remainderVars, dividendVars, prefixBits,
                     false, false);
}

// `q >=u 2^k <-> s <=u (a >> k)` at one k.
//
// The right side is one comparison over wires read from the dividend at an
// offset, with a pinned zero above them -- no shifter, and the comparison
// width is left alone so that a divisor with any bit at or above W-k
// correctly fails it. The left side is the disjunction of the quotient's
// bits from k up, and it is tied to the comparison without a variable of its
// own: one clause saying the comparison implies some high quotient bit, and
// one per high bit saying that bit implies the comparison.
void encodeDivPow2Threshold(SATSolver& solver,
                            const std::vector<unsigned>& dividendVars,
                            const std::vector<unsigned>& divisorVars,
                            const std::vector<unsigned>& quotientVars,
                            unsigned width, unsigned shift)
{
  assert(width > 1);
  assert(shift > 0 && shift < width);

  const unsigned zero = pinnedVar(solver, false);
  std::vector<unsigned> shiftedDividend(width, zero);
  for (unsigned i = 0; i + shift < width; ++i)
    shiftedDividend[i] = dividendVars[i + shift];

  const unsigned divisorFits =
      encodeLessOrEqual(solver, divisorVars, shiftedDividend, width, false);

  SATSolver::vec_literals cl;
  cl.push(SATSolver::mkLit(divisorFits, true));
  for (unsigned i = shift; i < width; ++i)
    cl.push(SATSolver::mkLit(quotientVars[i], false));
  solver.addClause(cl);

  for (unsigned i = shift; i < width; ++i)
  {
    cl.clear();
    cl.push(SATSolver::mkLit(quotientVars[i], true));
    cl.push(SATSolver::mkLit(divisorFits, false));
    solver.addClause(cl);
  }
}

void encodeDivBound(SATSolver& solver, DivSchema schema,
                           const std::vector<unsigned>& dividendVars,
                           const std::vector<unsigned>& divisorVars,
                           const std::vector<unsigned>& resultVars,
                           unsigned width)
{
  SATSolver::vec_literals cl;

  if (schema == DivSchema::RemainderAtMostDividend)
  {
    // r <= a, unconditionally: a unit clause on the chain's answer.
    const unsigned le =
        encodeLessOrEqual(solver, resultVars, dividendVars, width, false);
    cl.clear();
    cl.push(SATSolver::mkLit(le, false));
    solver.addClause(cl);
    return;
  }

  if (schema == DivSchema::QuotientAtMostDividend)
  {
    // b != 0 -> t <= a, i.e. t > a -> b = 0.
    const unsigned le =
        encodeLessOrEqual(solver, resultVars, dividendVars, width, false);
    for (unsigned i = 0; i < width; ++i)
    {
      cl.clear();
      cl.push(SATSolver::mkLit(le, false));
      cl.push(SATSolver::mkLit(divisorVars[i], true));
      solver.addClause(cl);
    }
    return;
  }

  // b != 0 -> r < b. `r < b` is `not (b <= r)`, so the chain is run the
  // other way round and its answer is the one that must be false.
  const unsigned bLeR =
      encodeLessOrEqual(solver, divisorVars, resultVars, width, false);
  for (unsigned i = 0; i < width; ++i)
  {
    cl.clear();
    cl.push(SATSolver::mkLit(bLeR, true));
    cl.push(SATSolver::mkLit(divisorVars[i], true));
    solver.addClause(cl);
  }
}

// b >=u 2^shift -> t <=u (a >> shift).
//
// The shift is a constant, so `a >> shift` is the dividend's own variables
// read from an offset with a pinned zero above it -- no gates, and no new
// variable beyond the one the comparison chain needs. The premise
// `b >=u 2^shift` is "some bit of b at or above shift is set", which is a
// disjunction, so its contrapositive is one binary clause per such bit: no
// premise variable, and the solver sees the guard on every bit of the divisor
// rather than behind a literal it has to reason through. That is the shape
// encodeDivBound uses for `b != 0`, and for the same reason.
void encodeDivShiftBound(SATSolver& solver,
                         const std::vector<unsigned>& dividendVars,
                         const std::vector<unsigned>& divisorVars,
                         const std::vector<unsigned>& resultVars,
                         unsigned width, unsigned shift)
{
  assert(shift < width);

  const unsigned zero = pinnedVar(solver, false);
  std::vector<unsigned> shifted(width);
  for (unsigned i = 0; i < width; ++i)
    shifted[i] = (i + shift < width) ? dividendVars[i + shift] : zero;

  const unsigned le =
      encodeLessOrEqual(solver, resultVars, shifted, width, false);

  SATSolver::vec_literals cl;
  for (unsigned i = shift; i < width; ++i)
  {
    cl.clear();
    cl.push(SATSolver::mkLit(le, false));
    cl.push(SATSolver::mkLit(divisorVars[i], true));
    solver.addClause(cl);
  }
}

void encodeDivUnderDivisorValue(
    SATSolver& solver, const std::vector<unsigned>& divisorVars,
    const std::vector<bool>& divisorBits,
    const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& resultVars, unsigned width,
    const std::vector<int>& source)
{
  const auto guard = [&](SATSolver::vec_literals& cl) {
    cl.clear();
    for (unsigned i = 0; i < width; ++i)
      cl.push(SATSolver::mkLit(divisorVars[i], divisorBits[i]));
  };

  SATSolver::vec_literals cl;
  for (unsigned bit = 0; bit < width; ++bit)
  {
    if (source[bit] == DIV_SOURCE_ZERO || source[bit] == DIV_SOURCE_ONE)
    {
      guard(cl);
      cl.push(SATSolver::mkLit(resultVars[bit], source[bit] == DIV_SOURCE_ZERO));
      solver.addClause(cl);
      continue;
    }

    const unsigned src = dividendVars[source[bit]];
    guard(cl);
    cl.push(SATSolver::mkLit(resultVars[bit], true));
    cl.push(SATSolver::mkLit(src, false));
    solver.addClause(cl);

    guard(cl);
    cl.push(SATSolver::mkLit(resultVars[bit], false));
    cl.push(SATSolver::mkLit(src, true));
    solver.addClause(cl);
  }
}

unsigned BVAbstractionRefiner::refineTerms(
    SATSolver& solver, const ToSATBase::ASTNodeToSATVar& nodeToSATVar)
{
  // Phase 1: Scan all abstractions, reading model values to find inconsistencies.
  // Cache the data needed for clause generation so we don't need modelValue later.
  struct InconsistentCmp {
    size_t absIdx;
    bool swapOps, negateResult, isSigned;
  };
  struct InconsistentPlus {
    size_t absIdx;
    // The algebraic fact this candidate contradicts, if `add` is on and one
    // does. Decided here, with the model in hand, because the clause phase
    // must not read it. Without one, the record is encoded exactly, which
    // is what an inconsistent addition has always got.
    AddSchemaChoice schema;
  };
  struct InconsistentITE {
    size_t absIdx;
  };
  struct InconsistentDivMul {
    size_t absIdx;
    std::vector<bool> aBits, bBits, expected;
    // The algebraic fact this candidate contradicts, if any. Decided here
    // rather than below because it is read off the model and the clause
    // phase must not touch the model. At most one of the two is ever set:
    // an abstraction is a multiplication or a division, never both.
    MulSchemaChoice schema;
    DivSchemaChoice divSchema;
    // The lowest bit the candidate's result got wrong, which is where a
    // piece-at-a-time escalation starts from. Always below the width: this
    // record exists because some bit is wrong.
    unsigned lowestWrongBit;
  };

  // What every abstracted division and remainder holds in this candidate,
  // kept whether the record turned out wrong or not. The identity below is
  // about a pair, and a pair is broken as easily by one half being wrong as
  // by both; the half that is right still has to be read.
  struct CandidateDivMod
  {
    bool seen = false;
    std::vector<bool> aBits, bBits, actual;
  };
  std::vector<CandidateDivMod> divMods(terms_.size());

  std::vector<InconsistentCmp> incCmps;
  std::vector<InconsistentPlus> incPlus;
  std::vector<InconsistentITE> incITE;
  std::vector<InconsistentDivMul> incDivMul;

  for (size_t idx = 0; idx < terms_.size(); ++idx)
  {
    auto& abs = terms_[idx];
    if (abs.defined)
      continue;

    if (isBVCompare(abs.opKind))
    {
      const unsigned condVar = recordedVar(
          abs.condSATVar, abs.termNode,
          "BV abstraction: an abstracted comparison has no input carrying "
          "its answer: ");

      std::vector<bool> aBits, bBits;
      getOperandBits(abs.operands[0], abs.width, nodeToSATVar, solver, aBits);
      getOperandBits(abs.operands[1], abs.width, nodeToSATVar, solver, bBits);

      bool expected = computeBVCompare(abs.opKind, aBits, bBits);
      bool actual = (solver.modelValue(condVar) == solver.true_literal());
      if (expected == actual)
        continue;

      // The same three answers computeBVCompare just used, taken from the
      // same place rather than restated here.
      const CompareForm form = comparisonForm(abs.opKind);

      incCmps.push_back({idx, form.swapOps, form.negateResult, form.isSigned});
      continue;
    }

    const std::vector<unsigned>& resultVars =
        encodedResultBitsOf(abs, nodeToSATVar);

    if (abs.opKind == BVPLUS)
    {
      std::vector<bool> leftBits, rightBits;
      getOperandBits(abs.operands[0], abs.width, nodeToSATVar, solver, leftBits);
      getOperandBits(abs.operands[1], abs.width, nodeToSATVar, solver, rightBits);

      const bool lNeg = abs.operandNegated[0];
      const bool rNeg = abs.operandNegated[1];
      const bool carryInit = (lNeg != rNeg);

      // The sum the candidate holds, kept rather than compared bit by bit
      // and dropped: the facts below are about the whole of it.
      std::vector<bool> sumBits(abs.width);
      for (unsigned bit = 0; bit < abs.width; ++bit)
        sumBits[bit] =
            (solver.modelValue(resultVars[bit]) == solver.true_literal());

      bool carry = carryInit;
      bool consistent = true;
      for (unsigned bit = 0; bit < abs.width; ++bit)
      {
        bool l = leftBits[bit] ^ lNeg;
        bool r = rightBits[bit] ^ rNeg;
        bool expectedSum = l ^ r ^ carry;
        carry = (l && r) || (l && carry) || (r && carry);
        if (sumBits[bit] != expectedSum) { consistent = false; break; }
      }
      if (consistent) continue;

      // A fact about every pair of operands, where one is on offer and the
      // record has schema allowance left. The exact adder behind it is
      // cheap and unconditional, so this is the one operation where the
      // fallback is at least as good as the fact -- which is why `add` is
      // off, and why nothing here changes unless it is turned on.
      AddSchemaChoice addSchema;
      const unsigned schemaLimit = bm->UserFlags.bv_term_abstraction_rounds;
      if (bm->UserFlags.bv_term_abstraction_schemas &&
          (schemaLimit == 0 || abs.schemaRounds < schemaLimit))
        addSchema = chooseAddSchema(
            leftBits, rightBits, sumBits, lNeg, rNeg, abs.installedSchemas,
            bm->UserFlags.bv_term_abstraction_schema_groups);

      incPlus.push_back({idx, addSchema});
    }
    else if (abs.opKind == ITE)
    {
      const unsigned condVar = recordedVar(
          abs.condSATVar, abs.termNode,
          "BV abstraction: an abstracted if-then-else has no input carrying "
          "its condition: ");

      bool condVal = (solver.modelValue(condVar) == solver.true_literal());
      unsigned branchIdx = condVal ? 1 : 2;
      std::vector<bool> branchBits;
      getOperandBits(abs.operands[branchIdx], abs.width, nodeToSATVar, solver,
                     branchBits);

      bool consistent = true;
      for (unsigned bit = 0; bit < abs.width; ++bit)
      {
        bool r = (solver.modelValue(resultVars[bit]) == solver.true_literal());
        if (r != branchBits[bit]) { consistent = false; break; }
      }
      if (consistent) continue;

      incITE.push_back({idx});
    }
    else if (abs.opKind == BVMULT || abs.opKind == BVDIV || abs.opKind == BVMOD)
    {
      std::vector<bool> aBits, bBits;
      getOperandBits(abs.operands[0], abs.width, nodeToSATVar, solver, aBits);
      getOperandBits(abs.operands[1], abs.width, nodeToSATVar, solver, bBits);

      unsigned W = abs.width;
      std::vector<bool> expected(W, false);
      if (abs.opKind == BVMULT)
      {
        for (unsigned i = 0; i < W; ++i)
          if (aBits[i])
            for (unsigned j = 0; j < W && i + j < W; ++j)
              if (bBits[j])
              {
                bool carry = false;
                for (unsigned p = i + j; p < W; ++p)
                {
                  if (p == i + j)
                  {
                    bool sum = expected[p] ^ true ^ carry;
                    carry = (expected[p] && true) || (expected[p] && carry) || (true && carry);
                    expected[p] = sum;
                  }
                  else
                  {
                    bool sum = expected[p] ^ false ^ carry;
                    carry = (expected[p] && carry);
                    expected[p] = sum;
                  }
                  if (!carry) break;
                }
              }
      }
      else
      {
        bool divisorZero = true;
        for (unsigned i = 0; i < W; ++i)
          if (bBits[i]) { divisorZero = false; break; }

        if (divisorZero)
        {
          // Both are totalised, and not to the same thing: division by zero
          // is all ones, while the remainder is the dividend. That is what
          // SMT-LIB says and what the unabstracted BBDivMod answers -- its
          // restoring loop finds every shifted remainder at or above a zero
          // divisor, subtracts nothing each time, and hands the dividend
          // back. Left at zero, this reference agreed with an abstraction
          // holding a value the query does not give it, so a bogus candidate
          // was called consistent: no lemma, and the refinement loop ran out
          // of things to say about a model it had already rejected.
          if (abs.opKind == BVDIV)
            for (unsigned i = 0; i < W; ++i) expected[i] = true;
          else
            expected = aBits;
        }
        else
        {
          std::vector<bool> quotient(W, false);
          std::vector<bool> remainder(W, false);
          for (int i = (int)W - 1; i >= 0; --i)
          {
            for (int j = (int)W - 1; j > 0; --j)
              remainder[j] = remainder[j - 1];
            remainder[0] = aBits[i];

            bool geq = true;
            for (int j = (int)W - 1; j >= 0; --j)
            {
              if (!remainder[j] && bBits[j]) { geq = false; break; }
              if (remainder[j] && !bBits[j]) break;
            }

            if (geq)
            {
              quotient[i] = true;
              bool borrow = false;
              for (unsigned j = 0; j < W; ++j)
              {
                bool sub = remainder[j] ^ bBits[j] ^ borrow;
                borrow = (!remainder[j] && bBits[j]) ||
                         (!remainder[j] && borrow) ||
                         (bBits[j] && borrow);
                remainder[j] = sub;
              }
            }
          }
          expected = (abs.opKind == BVDIV) ? quotient : remainder;
        }
      }

      // Read out in full rather than stopping at the first disagreement:
      // the schemas below are chosen by what the candidate's own product
      // *is*, not merely by the fact that it is wrong.
      std::vector<bool> actual(W);
      for (unsigned bit = 0; bit < W; ++bit)
        actual[bit] =
            (solver.modelValue(resultVars[bit]) == solver.true_literal());

      if (abs.opKind != BVMULT)
      {
        divMods[idx].seen = true;
        divMods[idx].aBits = aBits;
        divMods[idx].bBits = bBits;
        divMods[idx].actual = actual;
      }

      unsigned lowestWrongBit = W;
      for (unsigned bit = 0; bit < W; ++bit)
        if (actual[bit] != expected[bit]) { lowestWrongBit = bit; break; }
      if (lowestWrongBit == W) continue;

      // Only while there is allowance left. Schemas are spent from a
      // separate purse: one is both cheaper and stronger than a blocking
      // lemma, so it should not bring the escalation forward -- but it must
      // not push it out of reach either, and a candidate that keeps landing
      // on fresh powers of two would buy a solve for each one. The bound is
      // the flat ceiling rather than the width-scaled allowance below,
      // because what makes that allowance narrow is exactly what a schema
      // does not suffer from: a blocking lemma is worth less as the
      // operands widen, and a fact about every pair is worth the same.
      //
      // Multiplication and division draw on the same purse and are asked
      // separately, because what they can say about a candidate has nothing
      // in common: the multiplication facts are about the low bits of a
      // product and the commutativity that gives each of them two readings,
      // and the division facts are about one divisor at a time.
      MulSchemaChoice schema;
      DivSchemaChoice divSchema;
      const unsigned schemaLimit = bm->UserFlags.bv_term_abstraction_rounds;
      const bool schemaAllowance =
          bm->UserFlags.bv_term_abstraction_schemas &&
          (schemaLimit == 0 || abs.schemaRounds < schemaLimit);
      if (schemaAllowance)
      {
        const uint32_t groups =
            bm->UserFlags.bv_term_abstraction_schema_groups;
        if (abs.opKind == BVMULT)
          schema = chooseMulSchema(aBits, bBits, actual, abs.installedSchemas,
                                   groups);
        else
          divSchema = chooseDivSchema(abs.opKind, aBits, bBits, actual,
                                      abs.installedSchemas, groups);
      }

      incDivMul.push_back({idx, std::move(aBits), std::move(bBits),
                            std::move(expected), schema, divSchema,
                            lowestWrongBit});
    }
  }

  // Phase 2: Add refinement clauses (no model reads needed).
  unsigned refined = 0;

  // The division identity, first, because it says more than anything below
  // it: `x = t*s + r` over a quotient and a remainder the query takes of the
  // same operands. It is the definition rather than a consequence of one, so
  // at five bits it rules out nine in ten of the pairs the two records'
  // own facts admit between them.
  //
  // The partner is found by building the node it would be -- a BVMOD over
  // the same two operands -- and asking the blast whether it encoded one.
  // Nodes are hash-consed, so a query that holds both operations hands back
  // the very node the other record was minted from, and a query that holds
  // only the division finds nothing.
  //
  // Installed once per pair and never revisited: it is unconditional, so no
  // later candidate can contradict it.
  //
  // Two relations, and the prefix gets first refusal. It is the identity's
  // low bits and costs a handful of gates where the identity costs a
  // multiplier, so where the candidate breaks the prefix it is the cheaper
  // way to say the same thing. Where the candidate's low bits already
  // recompose the prefix would rule nothing out, and the identity -- which
  // may still be broken further up -- is what fires.
  const uint32_t pairGroups = bm->UserFlags.bv_term_abstraction_schema_groups;
  if (bm->UserFlags.bv_term_abstraction_schemas &&
      (bvSchemaGroupEnabled(pairGroups, BVSchemaGroup::DIVREM_IDENTITY) ||
       bvSchemaGroupEnabled(pairGroups, BVSchemaGroup::DIVREM_PREFIX)))
  {
    std::unordered_map<ASTNode, size_t, ASTNode::ASTNodeHasher,
                       ASTNode::ASTNodeEqual>
        remainders;
    for (size_t idx = 0; idx < terms_.size(); ++idx)
      if (terms_[idx].opKind == BVMOD && divMods[idx].seen)
        remainders[terms_[idx].termNode] = idx;

    for (size_t idx = 0; idx < terms_.size() && !remainders.empty(); ++idx)
    {
      BVTermAbstraction& q = terms_[idx];
      if (q.opKind != BVDIV || q.defined || !divMods[idx].seen)
        continue;
      if (q.divModIdentity && q.divModPrefix)
        continue;

      NodeFactory* nf = bm->defaultNodeFactory;
      const ASTNode partner =
          nf->CreateTerm(BVMOD, q.width, q.operands[0], q.operands[1]);
      const auto found = remainders.find(partner);
      if (found == remainders.end())
        continue;

      BVTermAbstraction& r = terms_[found->second];
      if (r.defined || r.width != q.width)
        continue;

      const std::vector<unsigned>& quotientVars =
          encodedResultBitsOf(q, nodeToSATVar);
      const std::vector<unsigned>& remainderVars =
          encodedResultBitsOf(r, nodeToSATVar);
      const unsigned prefix = lowPrefixWidth(q.width);

      // The prefix first, where it is on and the candidate breaks it.
      if (bvSchemaGroupEnabled(pairGroups, BVSchemaGroup::DIVREM_PREFIX) &&
          !q.divModPrefix && !r.divModPrefix &&
          !divRemLowPrefixHolds(divMods[idx].aBits, divMods[idx].bBits,
                                divMods[idx].actual,
                                divMods[found->second].actual, prefix))
      {
        std::vector<unsigned> aVars, bVars;
        getOperandVars(q.operands[0], q.width, nodeToSATVar, solver, aVars);
        getOperandVars(q.operands[1], q.width, nodeToSATVar, solver, bVars);
        encodeDivRemLowPrefix(solver, aVars, bVars, quotientVars,
                              remainderVars, prefix);

        q.divModPrefix = r.divModPrefix = true;
        countSchemaLemma(bm, BVSchemaGroup::DIVREM_PREFIX);
        if (bm->UserFlags.stats_flag)
          std::cerr << "BV abstraction: BVDIV/BVMOD division-identity prefix"
                    << std::endl;
        refined++;
        continue;
      }

      if (!bvSchemaGroupEnabled(pairGroups, BVSchemaGroup::DIVREM_IDENTITY) ||
          q.divModIdentity || r.divModIdentity)
        continue;

      // Only where the candidate breaks it. A round spent on a fact the
      // candidate already satisfies rules nothing out.
      if (divModIdentityHolds(divMods[idx].aBits, divMods[idx].bBits,
                              divMods[idx].actual,
                              divMods[found->second].actual))
        continue;

      // `t*s` needs a node for the multiplier to read, and the honest one
      // is the product of the quotient's own term and the divisor. The
      // factory may fold it -- a divisor of one leaves no multiplication
      // standing -- and then there is nothing here worth splicing.
      const ASTNode product =
          nf->CreateTerm(BVMULT, q.width, q.termNode, q.operands[1]);
      if (product.GetKind() != BVMULT)
        continue;

      std::vector<unsigned> aVars, bVars;
      getOperandVars(q.operands[0], q.width, nodeToSATVar, solver, aVars);
      getOperandVars(q.operands[1], q.width, nodeToSATVar, solver, bVars);
      BVExactEncoder(bm).encodeDivModIdentity(solver, product, q.width, aVars,
                                              bVars, quotientVars,
                                              remainderVars);

      q.divModIdentity = r.divModIdentity = true;
      countSchemaLemma(bm, BVSchemaGroup::DIVREM_IDENTITY);
      if (bm->UserFlags.stats_flag)
        std::cerr << "BV abstraction: BVDIV/BVMOD division-identity lemma"
                  << std::endl;
      refined++;
    }
  }

  for (auto& inc : incCmps)
  {
    auto& abs = terms_[inc.absIdx];
    std::vector<unsigned> leftVars, rightVars;
    getOperandVars(abs.operands[0], abs.width, nodeToSATVar, solver, leftVars);
    getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, rightVars);
    const std::vector<unsigned>& lv = inc.swapOps ? rightVars : leftVars;
    const std::vector<unsigned>& rv = inc.swapOps ? leftVars : rightVars;

    const unsigned carryVar =
        encodeLessOrEqual(solver, lv, rv, abs.width, inc.isSigned);

    {
      SATSolver::vec_literals cl;
      cl.clear(); cl.push(SATSolver::mkLit(abs.condSATVar, inc.negateResult));  cl.push(SATSolver::mkLit(carryVar, true));  solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(abs.condSATVar, !inc.negateResult)); cl.push(SATSolver::mkLit(carryVar, false)); solver.addClause(cl);
    }

    abs.defined = true;
    refined++;
  }

  for (auto& inc : incPlus)
  {
    auto& abs = terms_[inc.absIdx];
    std::vector<unsigned> leftVars, rightVars;
    getOperandVars(abs.operands[0], abs.width, nodeToSATVar, solver, leftVars);
    getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, rightVars);
    const std::vector<unsigned>& resultVars =
        encodedResultBitsOf(abs, nodeToSATVar);
    const bool lNeg = abs.operandNegated[0];
    const bool rNeg = abs.operandNegated[1];
    const bool carryInit = (lNeg != rNeg);

    // A fact instead of the adder, where the chooser found one. The record
    // is not defined by it -- the sum stays free and a later round may take
    // another fact or the adder itself.
    if (inc.schema.schema != AddSchema::None)
    {
      const unsigned chosen = inc.schema.operand;
      const std::vector<unsigned>* opVars[2] = {&leftVars, &rightVars};
      const bool negated[2] = {lNeg, rNeg};

      if (inc.schema.schema == AddSchema::LowPrefix)
      {
        encodeAddLowPrefix(solver, leftVars, rightVars, resultVars,
                           lowPrefixWidth(abs.width), lNeg, rNeg);
        abs.installedSchemas |= SCHEMA_INSTALLED_LOW_PREFIX;
      }
      else
      {
        BVExactEncoder(bm).encodeAddLemma(
            solver, inc.schema.lemma, abs.width, *opVars[chosen],
            *opVars[1 - chosen], resultVars, negated[chosen],
            negated[1 - chosen]);
        abs.installedSchemas |=
            addLemmaInstalledBit(inc.schema.lemmaIndex, chosen);
      }

      abs.schemaRounds++;
      countSchemaLemma(bm, inc.schema.group);
      if (bm->UserFlags.stats_flag)
        std::cerr << "BV abstraction: BVPLUS "
                  << (inc.schema.schema == AddSchema::LowPrefix
                          ? "exact-low-prefix"
                          : addLemmaName(inc.schema.lemma))
                  << " lemma over operand " << chosen << std::endl;
      refined++;
      continue;
    }

    unsigned carryVar = solver.newVar();
    solver.setFrozen(carryVar);
    {
      SATSolver::vec_literals cl;
      cl.push(SATSolver::mkLit(carryVar, !carryInit));
      solver.addClause(cl);
    }

    for (unsigned bit = 0; bit < abs.width; ++bit)
    {
      unsigned l = leftVars[bit];
      unsigned r = rightVars[bit];
      unsigned s = resultVars[bit];
      unsigned c = carryVar;
      SATSolver::vec_literals cl;

      // s <-> l ^ r ^ c, one clause per row of the three inputs, each falsified
      // only by that row paired with the wrong sum bit. Written out of the row
      // rather than transcribed, because the transcription carried every s
      // literal inverted: the lemma forced s = !(l ^ r ^ c), which is not a
      // weaker constraint on the abstraction but the negation of the one the
      // scan above had just checked. A refined addition was therefore still
      // inconsistent on the next round, and `defined` below meant it was never
      // looked at again.
      //
      // mkLit(v, sign) is false exactly when v equals sign, so a literal taken
      // at `bit != negated` is false exactly when that operand's effective bit
      // -- the variable read through the BVUMINUS that operandNegated records,
      // whose +1 the carry above seeds -- is `bit`.
      for (unsigned row = 0; row < 8; ++row)
      {
        const bool lBit = (row & 1) != 0;
        const bool rBit = (row & 2) != 0;
        const bool cBit = (row & 4) != 0;
        const bool sum = lBit ^ rBit ^ cBit;
        cl.clear();
        cl.push(SATSolver::mkLit(l, lBit != lNeg));
        cl.push(SATSolver::mkLit(r, rBit != rNeg));
        cl.push(SATSolver::mkLit(c, cBit));
        cl.push(SATSolver::mkLit(s, !sum));
        solver.addClause(cl);
      }

      if (bit < abs.width - 1)
      {
        unsigned nc = solver.newVar();
        solver.setFrozen(nc);

        cl.clear(); cl.push(SATSolver::mkLit(l,lNeg));   cl.push(SATSolver::mkLit(r,rNeg));   cl.push(SATSolver::mkLit(nc,true)); solver.addClause(cl);
        cl.clear(); cl.push(SATSolver::mkLit(l,lNeg));   cl.push(SATSolver::mkLit(c,false));   cl.push(SATSolver::mkLit(nc,true)); solver.addClause(cl);
        cl.clear(); cl.push(SATSolver::mkLit(r,rNeg));   cl.push(SATSolver::mkLit(c,false));   cl.push(SATSolver::mkLit(nc,true)); solver.addClause(cl);
        cl.clear(); cl.push(SATSolver::mkLit(l,!lNeg));  cl.push(SATSolver::mkLit(r,!rNeg));  cl.push(SATSolver::mkLit(nc,false)); solver.addClause(cl);
        cl.clear(); cl.push(SATSolver::mkLit(l,!lNeg));  cl.push(SATSolver::mkLit(c,true));   cl.push(SATSolver::mkLit(nc,false)); solver.addClause(cl);
        cl.clear(); cl.push(SATSolver::mkLit(r,!rNeg));  cl.push(SATSolver::mkLit(c,true));   cl.push(SATSolver::mkLit(nc,false)); solver.addClause(cl);

        carryVar = nc;
      }
    }

    abs.defined = true;
    refined++;
  }

  for (auto& inc : incITE)
  {
    auto& abs = terms_[inc.absIdx];
    // Both branches, where the scan above only read the one the candidate's
    // condition selected: a pinned if-then-else has to say what it is under
    // either.
    std::vector<unsigned> thenVars, elseVars;
    getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, thenVars);
    getOperandVars(abs.operands[2], abs.width, nodeToSATVar, solver, elseVars);
    const std::vector<unsigned>& resultVars =
        encodedResultBitsOf(abs, nodeToSATVar);
    unsigned c = abs.condSATVar;

    for (unsigned bit = 0; bit < abs.width; ++bit)
    {
      unsigned r = resultVars[bit];
      unsigned t = thenVars[bit];
      unsigned e = elseVars[bit];
      SATSolver::vec_literals cl;

      cl.clear(); cl.push(SATSolver::mkLit(c,true));  cl.push(SATSolver::mkLit(r,true));  cl.push(SATSolver::mkLit(t,false)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(c,true));  cl.push(SATSolver::mkLit(r,false)); cl.push(SATSolver::mkLit(t,true));  solver.addClause(cl);

      cl.clear(); cl.push(SATSolver::mkLit(c,false)); cl.push(SATSolver::mkLit(r,true));  cl.push(SATSolver::mkLit(e,false)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(c,false)); cl.push(SATSolver::mkLit(r,false)); cl.push(SATSolver::mkLit(e,true));  solver.addClause(cl);
    }

    abs.defined = true;
    refined++;
  }

  for (auto& inc : incDivMul)
  {
    auto& abs = terms_[inc.absIdx];
    std::vector<unsigned> aVars, bVars;
    getOperandVars(abs.operands[0], abs.width, nodeToSATVar, solver, aVars);
    getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, bVars);
    const std::vector<unsigned>& resultVars =
        encodedResultBitsOf(abs, nodeToSATVar);
    unsigned W = abs.width;

    // An algebraic fact the candidate contradicts, where there is one.
    // Every branch here writes a theorem about the operation over the
    // variables already in the solver -- the operand proxies and the
    // abstraction's own result bits -- so none of it is retractable and
    // none of it needs to be. What the candidate chose is only *which*
    // theorem to spend a round on.
    if (inc.divSchema.schema != DivSchema::None)
    {
      switch (inc.divSchema.schema)
      {
        case DivSchema::DivisorZero:
        case DivSchema::Pow2Divisor:
          encodeDivUnderDivisorValue(
              solver, bVars, inc.bBits, aVars, resultVars, W,
              divSchemaSources(abs.opKind, W, inc.divSchema));
          break;

        case DivSchema::QuotientPow2Threshold:
          assert(abs.opKind == BVDIV);
          encodeDivPow2Threshold(solver, aVars, bVars, resultVars, W,
                                 inc.divSchema.shift);
          break;

        case DivSchema::DivisorAtLeastPow2:
          encodeDivShiftBound(solver, aVars, bVars, resultVars, W,
                              inc.divSchema.shift);
          for (unsigned i = 0; i < DIV_SCHEMA_SHIFT_BOUND_ALLOWANCE; ++i)
            if ((abs.installedSchemas & divShiftBoundBit(i)) == 0)
            {
              abs.installedSchemas |= divShiftBoundBit(i);
              break;
            }
          break;

        case DivSchema::RemainderAtMostDividend:
          encodeDivBound(solver, inc.divSchema.schema, aVars, bVars, resultVars,
                         W);
          abs.installedSchemas |=
              DIV_SCHEMA_INSTALLED_REMAINDER_AT_MOST_DIVIDEND;
          break;

        case DivSchema::RemainderBelowDivisor:
          encodeDivBound(solver, inc.divSchema.schema, aVars, bVars, resultVars,
                         W);
          abs.installedSchemas |= DIV_SCHEMA_INSTALLED_REMAINDER_BELOW_DIVISOR;
          break;

        case DivSchema::QuotientAtMostDividend:
          encodeDivBound(solver, inc.divSchema.schema, aVars, bVars, resultVars,
                         W);
          abs.installedSchemas |=
              DIV_SCHEMA_INSTALLED_QUOTIENT_AT_MOST_DIVIDEND;
          break;

        case DivSchema::Lemma:
          if (abs.opKind == BVDIV)
            BVExactEncoder(bm).encodeDivLemma(
                solver, DIV_LEMMAS[inc.divSchema.lemmaIndex], W, aVars, bVars,
                resultVars);
          else
            BVExactEncoder(bm).encodeRemLemma(
                solver, REM_LEMMAS[inc.divSchema.lemmaIndex], W, aVars, bVars,
                resultVars);
          abs.installedSchemas |=
              divLemmaInstalledBit(inc.divSchema.lemmaIndex);
          break;

        case DivSchema::None:
          break;
      }

      abs.schemaRounds++;
      countSchemaLemma(bm, inc.divSchema.group);
      if (bm->UserFlags.stats_flag)
        std::cerr << "BV abstraction: " << _kind_names[abs.opKind] << " "
                  << (inc.divSchema.schema != DivSchema::Lemma
                          ? divSchemaName(inc.divSchema.schema)
                      : (abs.opKind == BVDIV)
                          ? divLemmaName(DIV_LEMMAS[inc.divSchema.lemmaIndex])
                          : remLemmaName(REM_LEMMAS[inc.divSchema.lemmaIndex]))
                  << " lemma" << std::endl;
      refined++;
      continue;
    }

    if (inc.schema.schema != MulSchema::None)
    {
      const unsigned chosen = inc.schema.operand;
      const std::vector<unsigned>* opVars[2] = {&aVars, &bVars};
      const std::vector<bool>* opBits[2] = {&inc.aBits, &inc.bBits};

      switch (inc.schema.schema)
      {
        case MulSchema::Odd:
          encodeMulOdd(solver, aVars, bVars, resultVars);
          abs.installedSchemas |= MUL_SCHEMA_INSTALLED_ODD;
          break;

        case MulSchema::TrailingZeros:
          encodeMulTrailingZeros(solver, *opVars[chosen], resultVars, W);
          abs.installedSchemas |=
              (chosen == 0 ? MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0
                           : MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1);
          break;

        case MulSchema::Pow2:
          encodeMulShiftUnderValue(solver, *opVars[chosen], *opBits[chosen],
                                   *opVars[1 - chosen], resultVars, W,
                                   inc.schema.shift);
          break;

        case MulSchema::NegPow2:
        {
          // The negation circuit is minted once and kept: this schema can
          // fire once per power of two, and the operand proxies it is
          // written over are the same variables every round -- the blaster
          // registers them, so getOperandVars hands back the registry's
          // entry rather than fresh bits.
          const unsigned other = 1 - chosen;
          if (abs.negatedOperand[other].empty())
            abs.negatedOperand[other] =
                encodeNegate(solver, *opVars[other], W);
          encodeMulShiftUnderValue(solver, *opVars[chosen], *opBits[chosen],
                                   abs.negatedOperand[other], resultVars, W,
                                   inc.schema.shift);
          break;
        }

        case MulSchema::LowPrefix:
          encodeMulLowPrefix(solver, *opVars[0], *opVars[1], resultVars,
                             lowPrefixWidth(W));
          abs.installedSchemas |= SCHEMA_INSTALLED_LOW_PREFIX;
          break;

        case MulSchema::Lemma:
        {
          // `chosen` says which operand plays the fact's `x`; the other
          // plays its `s`.
          BVExactEncoder(bm).encodeMulLemma(
              solver, MUL_LEMMAS[inc.schema.lemmaIndex], W, *opVars[chosen],
              *opVars[1 - chosen], resultVars);
          abs.installedSchemas |=
              mulLemmaInstalledBit(inc.schema.lemmaIndex, chosen);
          break;
        }

        case MulSchema::None:
          break;
      }

      abs.schemaRounds++;
      countSchemaLemma(bm, inc.schema.group);
      if (bm->UserFlags.stats_flag)
        std::cerr << "BV abstraction: BVMULT "
                  << (inc.schema.schema == MulSchema::Lemma
                          ? mulLemmaName(MUL_LEMMAS[inc.schema.lemmaIndex])
                          : mulSchemaName(inc.schema.schema))
                  << " lemma over operand " << chosen << std::endl;
      refined++;
      continue;
    }

    // Once this abstraction has been blocked its allowance of times, stop
    // ruling out operand pairs one at a time and say what the operation is.
    // Everything the encoding needs is already here and already frozen: the
    // operands, through the proxies tied to their real bits or pinned to a
    // constant, and the result, which is the abstraction's own bits. Every
    // one of those is a variable the CNF has -- encodedBitsOf above will not
    // hand back a vector holding anything else -- so there is no incomplete
    // mapping to fall back off, only the choice of when to stop enumerating.
    //
    // What it says is the encoding the query would have had if the term had
    // never been abstracted -- literally so: the same bit-blaster entry
    // point BBTerm uses, mapped to CNF by the same ABC pass. See
    // BVExactEncoder. Two independent encodings of a divider that agree
    // today are two that can stop agreeing, and these two already had: the
    // written-out one and BBDivMod disagreed about a zero divisor.
    const unsigned limit = valueLemmaAllowance(bm->UserFlags, W);
    if (limit != 0 && abs.blockedRounds >= limit)
    {
      // All of it, unless the piece-at-a-time escalation is on and this is
      // a multiplication. A piece reaches past the lowest bit the candidate
      // got wrong, which is at or above everything already encoded -- the
      // bits below are pinned exactly, so no candidate can disagree there
      // -- and so every round pushes the encoding strictly further up and
      // the last one finishes it.
      //
      // Each piece is a whole circuit for the bits below it, so a
      // multiplication that takes several of them pays for the low bits
      // more than once. This implementation does not reuse the lower-bit
      // circuit from an earlier piece, which is one reason the flag is off
      // until something measures it.
      unsigned upto = W;
      ASTNode encodeAs = abs.termNode;
      if (bm->UserFlags.bv_term_abstraction_inc_bitblast &&
          abs.opKind == BVMULT && inc.lowestWrongBit + 1 < W)
      {
        const unsigned reach = inc.lowestWrongBit + BV_INC_BITBLAST_STEP + 1;
        if (reach < W)
        {
          const ASTNode narrowed = narrowedProduct(bm, abs.termNode, reach);
          if (!narrowed.IsNull())
          {
            upto = reach;
            encodeAs = narrowed;
          }
        }
      }

      // What the exact encoding costs, measured rather than inferred: the
      // solver's own clause and variable counts across the call.
      const uint64_t exactClausesBefore = solver.submittedClauses();
      const uint32_t exactVariablesBefore = solver.nVars();

      BVExactEncoder(bm).encode(solver, encodeAs, upto, aVars, bVars,
                                resultVars);
      abs.blastedBits = upto;
      abs.defined = (upto == W);

      {
        UserDefinedFlags::EncodingCoverage& c = bm->UserFlags.coverage;
        c.bv_exact_escalations++;
        if (abs.opKind == BVMULT)
          c.bv_exact_escalations_mult++;
        else
          c.bv_exact_escalations_divmod++;
        c.bv_exact_clauses += solver.submittedClauses() - exactClausesBefore;
        c.bv_exact_variables += solver.nVars() - exactVariablesBefore;
      }

      if (bm->UserFlags.stats_flag)
      {
        std::cerr << "BV abstraction: encoding " << _kind_names[abs.opKind];
        if (!abs.defined)
          std::cerr << " up to bit " << (upto - 1);
        else
          std::cerr << " exactly";
        std::cerr << " after " << abs.blockedRounds << " blocking lemmas"
                  << std::endl;
      }
      refined++;
      continue;
    }
    abs.blockedRounds++;
    bm->UserFlags.coverage.bv_blocking_lemmas++;

    for (unsigned bit = 0; bit < W; ++bit)
    {
      SATSolver::vec_literals cl;
      for (unsigned i = 0; i < W; ++i)
        cl.push(SATSolver::mkLit(aVars[i], inc.aBits[i]));
      for (unsigned i = 0; i < W; ++i)
        cl.push(SATSolver::mkLit(bVars[i], inc.bBits[i]));
      cl.push(SATSolver::mkLit(resultVars[bit], !inc.expected[bit]));
      solver.addClause(cl);
    }

    refined++;
  }

  return refined;
}

} // namespace stp
