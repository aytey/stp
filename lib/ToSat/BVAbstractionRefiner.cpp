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
#include <limits>
#include <unordered_map>

namespace stp
{

static void countSchemaLemma(UserDefinedFlags& flags, BVSchemaGroup group)
{
  const unsigned index = static_cast<unsigned>(group);
  assert(index < BV_SCHEMA_GROUP_COUNT);
  flags.coverage.bv_schema_lemmas++;
  flags.coverage.bv_schema_group_lemmas[index]++;
}

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

static void readModelBits(const std::vector<unsigned>& satVars,
                          unsigned width, SATSolver& solver,
                          std::vector<bool>& bits)
{
  assert(satVars.size() >= width);
  bits.resize(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = (solver.modelValue(satVars[i]) == solver.true_literal());
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
  readModelBits(satVars, width, solver, bits);
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

// z <-> x & y
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

bool exactLowPrefixHolds(Kind opKind, const std::vector<bool>& aBits,
                         const std::vector<bool>& bBits,
                         const std::vector<bool>& resultBits,
                         unsigned prefixBits)
{
  assert(opKind == BVPLUS || opKind == BVMULT);
  assert(aBits.size() == bBits.size());
  assert(aBits.size() == resultBits.size());
  assert(prefixBits > 0 && prefixBits <= resultBits.size());

  std::vector<bool> expected(prefixBits, false);
  if (opKind == BVPLUS)
  {
    bool carry = false;
    for (unsigned i = 0; i < prefixBits; ++i)
    {
      expected[i] = (aBits[i] != bBits[i]) != carry;
      carry = (aBits[i] && bBits[i]) || (aBits[i] && carry) ||
              (bBits[i] && carry);
    }
  }
  else
  {
    // Add each low shifted copy of b into the prefix. No operand bit at or
    // above prefixBits can affect a lower product bit.
    for (unsigned i = 0; i < prefixBits; ++i)
      if (aBits[i])
      {
        bool carry = false;
        for (unsigned j = 0; i + j < prefixBits; ++j)
        {
          const unsigned bit = i + j;
          const bool addend = bBits[j];
          const bool sum = (expected[bit] != addend) != carry;
          carry = (expected[bit] && addend) || (expected[bit] && carry) ||
                  (addend && carry);
          expected[bit] = sum;
        }
      }
  }

  for (unsigned i = 0; i < prefixBits; ++i)
    if (expected[i] != resultBits[i])
      return false;
  return true;
}

bool divRemLowPrefixHolds(const std::vector<bool>& dividendBits,
                          const std::vector<bool>& divisorBits,
                          const std::vector<bool>& quotientBits,
                          const std::vector<bool>& remainderBits,
                          unsigned prefixBits)
{
  assert(dividendBits.size() == divisorBits.size());
  assert(dividendBits.size() == quotientBits.size());
  assert(dividendBits.size() == remainderBits.size());
  assert(prefixBits > 0 && prefixBits <= dividendBits.size());

  std::vector<bool> product(prefixBits, false);
  for (unsigned i = 0; i < prefixBits; ++i)
    if (quotientBits[i])
    {
      bool carry = false;
      for (unsigned j = 0; i + j < prefixBits; ++j)
      {
        const unsigned bit = i + j;
        const bool addend = divisorBits[j];
        const bool sum = (product[bit] != addend) != carry;
        carry = (product[bit] && addend) || (product[bit] && carry) ||
                (addend && carry);
        product[bit] = sum;
      }
    }

  bool carry = false;
  for (unsigned i = 0; i < prefixBits; ++i)
  {
    const bool sum = (product[i] != remainderBits[i]) != carry;
    carry = (product[i] && remainderBits[i]) || (product[i] && carry) ||
            (remainderBits[i] && carry);
    if (sum != dividendBits[i])
      return false;
  }
  return true;
}

static const MulLemma MUL_LEMMAS[] = {
    MulLemma::FactorUnchangedByMaskedShift, // Bitwuzla MUL8; 75 firings
    MulLemma::FactorAndProductNotOr,        // Bitwuzla MUL ref3; 5
    MulLemma::MulRefN3,                     // 4

    // The unobserved tail in upstream registry order.
    MulLemma::MulRef1, MulLemma::MulRefN5, MulLemma::MulRefN6,
    MulLemma::MulRef14, MulLemma::MulRef15, MulLemma::MulRefN9,
    MulLemma::MulRef18, MulLemma::MulRefN11, MulLemma::MulRefN12,
    MulLemma::MulRefN13, MulLemma::MulRef13, MulLemma::MulRef12};

static const unsigned MUL_LEMMA_COUNT =
    sizeof(MUL_LEMMAS) / sizeof(MUL_LEMMAS[0]);

static BVSchemaGroup mulLemmaGroup(MulLemma lemma)
{
  switch (lemma)
  {
    case MulLemma::FactorUnchangedByMaskedShift:
      return BVSchemaGroup::MUL8;
    case MulLemma::FactorAndProductNotOr:
      return BVSchemaGroup::MUL_REF3;

    case MulLemma::MulRef1:
    case MulLemma::MulRefN3:
    case MulLemma::MulRefN5:
    case MulLemma::MulRefN6:
    case MulLemma::MulRef14:
    case MulLemma::MulRef15:
    case MulLemma::MulRefN9:
    case MulLemma::MulRef18:
    case MulLemma::MulRefN11:
    case MulLemma::MulRefN12:
    case MulLemma::MulRefN13:
    case MulLemma::MulRef13:
    case MulLemma::MulRef12:
      return BVSchemaGroup::MUL_EXTRA;
  }
  assert(false && "MulLemma has no schema-group owner");
  return BVSchemaGroup::MUL_EXTRA;
}

const MulLemma* mulLemmaTable(unsigned& count)
{
  count = MUL_LEMMA_COUNT;
  return MUL_LEMMAS;
}

static const AddLemma ADD_LEMMAS[] = {
    AddLemma::AddZero,       AddLemma::AddSame, AddLemma::AddInv,
    AddLemma::AddOverflow,   AddLemma::AddNoOverflow,
    AddLemma::AddOr,         AddLemma::AddRef6, AddLemma::AddRef7,
    AddLemma::AddRef8,       AddLemma::AddRef9, AddLemma::AddRef10,
    AddLemma::AddRef11,      AddLemma::AddRef12};

static const unsigned ADD_LEMMA_COUNT =
    sizeof(ADD_LEMMAS) / sizeof(ADD_LEMMAS[0]);

const AddLemma* addLemmaTable(unsigned& count)
{
  count = ADD_LEMMA_COUNT;
  return ADD_LEMMAS;
}

AddSchemaChoice chooseAddSchema(const std::vector<bool>& aBits,
                                const std::vector<bool>& bBits,
                                const std::vector<bool>& tBits,
                                uint64_t installedSchemas,
                                uint32_t enabledGroups)
{
  const std::vector<bool>* ops[2] = {&aBits, &bBits};
  if (bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::ADD))
    for (unsigned lemmaIndex = 0; lemmaIndex < ADD_LEMMA_COUNT; ++lemmaIndex)
    {
      if (!addLemmaApplicable(ADD_LEMMAS[lemmaIndex], (unsigned)tBits.size()))
        continue;
      for (unsigned operand = 0; operand < 2; ++operand)
      {
        if ((installedSchemas & addLemmaInstalledBit(lemmaIndex, operand)) != 0)
          continue;
        if (!addLemmaHolds(ADD_LEMMAS[lemmaIndex], *ops[operand],
                           *ops[1 - operand], tBits))
          return {true, operand, lemmaIndex, 0, BVSchemaGroup::ADD};
      }
    }

  const unsigned prefix = std::min(3u, (unsigned)tBits.size());
  if (bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::LOW_PREFIX) &&
      (installedSchemas & ADD_SCHEMA_INSTALLED_LOW_PREFIX) == 0 &&
      !exactLowPrefixHolds(BVPLUS, aBits, bBits, tBits, prefix))
    return {true, 0, 0, prefix, BVSchemaGroup::LOW_PREFIX};
  return AddSchemaChoice();
}

MulSchemaChoice chooseMulSchema(const std::vector<bool>& aBits,
                                const std::vector<bool>& bBits,
                                const std::vector<bool>& tBits,
                                uint64_t installedSchemas,
                                uint32_t enabledGroups)
{
  const std::vector<bool>* ops[2] = {&aBits, &bBits};
  const bool base = bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::BASE);

  // a = 2^k -> t = b << k, and the same read the other way round. Where it
  // applies it says the most of the four: the shift *is* the product for
  // that operand value, so one lemma settles every b at once where a
  // blocking lemma settles one pair. It therefore also always fires when it
  // applies -- this is only ever called over a candidate whose product is
  // already known wrong, and for a power-of-two operand "wrong" and
  // "disagrees with the shift" are the same statement.
  if (base)
    for (unsigned i = 0; i < 2; ++i)
    {
      const int k = powerOfTwoExponent(*ops[i]);
      if (k >= 0 && !productIsShift(*ops[1 - i], (unsigned)k, tBits))
        return {MulSchema::Pow2, i, (unsigned)k};
    }

  // a = -2^k -> t = (-b) << k. A power of two is skipped rather than
  // excluded by name: that covers the minimum signed value, which is its own
  // negation and which the schema above has already taken.
  if (base)
    for (unsigned i = 0; i < 2; ++i)
    {
      if (powerOfTwoExponent(*ops[i]) >= 0)
        continue;
      const int k = powerOfTwoExponent(negatedValue(*ops[i]));
      if (k >= 0 &&
          !productIsShift(negatedValue(*ops[1 - i]), (unsigned)k, tBits))
        return {MulSchema::NegPow2, i, (unsigned)k};
    }

  // The product carries at least as many trailing zeros as either operand.
  // Check operand 1 before operand 0 so schema selection remains
  // deterministic for this commutative operator.
  static const unsigned tzInstalled[2] = {
      MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_0,
      MUL_SCHEMA_INSTALLED_TRAILING_ZEROS_1};
  if (base)
    for (unsigned pass = 0; pass < 2; ++pass)
    {
      const unsigned i = 1 - pass;
      if ((installedSchemas & tzInstalled[i]) != 0)
        continue;
      const unsigned zeros = trailingZeros(*ops[i]);
      for (unsigned bit = 0; bit < zeros; ++bit)
        if (tBits[bit])
          return {MulSchema::TrailingZeros, i, 0};
    }

  // t[0] = a[0] & b[0].
  if (base && (installedSchemas & MUL_SCHEMA_INSTALLED_ODD) == 0 &&
      tBits[0] != (aBits[0] && bBits[0]))
    return {MulSchema::Odd, 0, 0};

  // The registry facts are unconditional but asymmetric expressions over a
  // commutative operation. Offer each source fact in both readings, exactly
  // once apiece. MUL8 is entry zero, so the ranked 75-firing fact is offered
  // before the remainder of the imported catalogue.
  for (unsigned lemmaIndex = 0; lemmaIndex < MUL_LEMMA_COUNT; ++lemmaIndex)
  {
    const MulLemma lemma = MUL_LEMMAS[lemmaIndex];
    const BVSchemaGroup group = mulLemmaGroup(lemma);
    if (!bvSchemaGroupEnabled(enabledGroups, group))
      continue;
    if (!mulLemmaApplicable(lemma, (unsigned)tBits.size()))
      continue;
    for (unsigned operand = 0; operand < 2; ++operand)
    {
      if ((installedSchemas &
           mulLemmaInstalledBit(lemmaIndex, operand)) != 0)
        continue;
      if (!mulLemmaHolds(lemma, *ops[operand], *ops[1 - operand], tBits))
        return {MulSchema::Lemma, operand, 0, lemmaIndex, group};
    }
  }

  const unsigned prefix = std::min(3u, (unsigned)tBits.size());
  if (bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::LOW_PREFIX) &&
      (installedSchemas & MUL_SCHEMA_INSTALLED_LOW_PREFIX) == 0 &&
      !exactLowPrefixHolds(BVMULT, aBits, bBits, tBits, prefix))
    return {MulSchema::LowPrefix, 0, prefix, 0, BVSchemaGroup::LOW_PREFIX};

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
    // STP-specific. Ranked here by the extra candidate cube it excludes at
    // six bits (2.42%), ahead of facts below that add no unique exclusions.
    DivLemma::QuotientIsOne,
    DivLemma::DividendZero,                          // 171
    DivLemma::DivisorEqualsDividend,                 // 162
    DivLemma::DivisorLessOneAboveShiftedDividend,    // 161
    DivLemma::DividendAboveShiftedDoubleQuotient,    // 125
    DivLemma::QuotientNotNegatedAnd,                 // ref9; 62
    DivLemma::DivisorAllOnes,                        // 59
    DivLemma::DividendAboveDoubledShiftedDivisor,    // ref14; 54
    DivLemma::DividendNotTwiceQuotientPlusOr,        // ref33; 26
    DivLemma::QuotientAboveDoubledShiftedDividend,   // ref16; 14
    DivLemma::DividendAboveOrAndDoubledDivisor,      // ref17; 10
    DivLemma::MaskedDividendAboveDivisorAndQuotient, // ref12; 9
    DivLemma::DividendAboveQuotientXorShifted,       // ref26; 3
    DivLemma::ShiftedDividendNotOr,                  // ref19; 3
    DivLemma::DividendAboveOrAndDoubledQuotient,     // ref18; 2
    DivLemma::DividendAboveDivisorXorShifted,        // ref27; 2

    // The remainder of Bitwuzla's enabled UDIV registry did not fire in the
    // profile used to rank the entries above. Keep source order for this
    // unranked tail so reconciliation against that registry stays mechanical.
    DivLemma::UdivRef10, DivLemma::UdivRef11, DivLemma::UdivRef20,
    DivLemma::UdivRef21, DivLemma::UdivRef23, DivLemma::UdivRef24,
    DivLemma::UdivRef25, DivLemma::UdivRef28, DivLemma::UdivRef29,
    DivLemma::UdivRef30, DivLemma::UdivRef31, DivLemma::UdivRef32,
    DivLemma::UdivRef34, DivLemma::UdivRef36, DivLemma::UdivRef38};

static const unsigned DIV_LEMMA_COUNT =
    sizeof(DIV_LEMMAS) / sizeof(DIV_LEMMAS[0]);

static_assert(DIV_LEMMA_COUNT <= 54,
              "the UDIV registry overlaps reserved magnitude-bound bits");

static BVSchemaGroup divLemmaGroup(DivLemma lemma)
{
  switch (lemma)
  {
    case DivLemma::DividendAboveShiftedDoubleQuotient:
      return BVSchemaGroup::UDIV15;

    case DivLemma::QuotientIsOne:
      return BVSchemaGroup::QUOTIENT_ONE_QUOT;

    case DivLemma::DividendZero:
    case DivLemma::DivisorEqualsDividend:
    case DivLemma::DivisorAllOnes:
    case DivLemma::QuotientBelowNegatedDivisor:
    case DivLemma::DividendAboveNegatedAnd:
    case DivLemma::DivisorAboveShiftedDividend:
    case DivLemma::DivisorLessOneAboveShiftedDividend:
      return BVSchemaGroup::BASE;

    case DivLemma::QuotientNotNegatedAnd:
    case DivLemma::MaskedDividendAboveDivisorAndQuotient:
    case DivLemma::DividendAboveDoubledShiftedDivisor:
    case DivLemma::QuotientAboveDoubledShiftedDividend:
    case DivLemma::DividendAboveOrAndDoubledDivisor:
    case DivLemma::DividendAboveOrAndDoubledQuotient:
    case DivLemma::ShiftedDividendNotOr:
    case DivLemma::DividendAboveQuotientXorShifted:
    case DivLemma::DividendAboveDivisorXorShifted:
    case DivLemma::DividendNotTwiceQuotientPlusOr:
      return BVSchemaGroup::UDIV_OBSERVED;

    case DivLemma::UdivRef10:
    case DivLemma::UdivRef11:
    case DivLemma::UdivRef20:
    case DivLemma::UdivRef21:
    case DivLemma::UdivRef23:
    case DivLemma::UdivRef24:
    case DivLemma::UdivRef25:
    case DivLemma::UdivRef28:
    case DivLemma::UdivRef29:
    case DivLemma::UdivRef30:
    case DivLemma::UdivRef31:
    case DivLemma::UdivRef32:
    case DivLemma::UdivRef34:
    case DivLemma::UdivRef36:
    case DivLemma::UdivRef38:
      return BVSchemaGroup::UDIV_EXTRA;
  }
  assert(false && "DivLemma has no schema-group owner");
  return BVSchemaGroup::UDIV_EXTRA;
}

// UDIV_EXTRA was published by v2 as an umbrella for the complete non-base
// registry. Keep that spelling source-compatible while allowing v3's new
// UDIV_OBSERVED bit to select and account for only the ranked entries.
static bool divLemmaGroupEnabled(uint32_t mask, BVSchemaGroup group)
{
  return bvSchemaGroupEnabled(mask, group) ||
         (group == BVSchemaGroup::UDIV_OBSERVED &&
          bvSchemaGroupEnabled(mask, BVSchemaGroup::UDIV_EXTRA));
}

static BVSchemaGroup divLemmaAccountingGroup(uint32_t mask, BVSchemaGroup group)
{
  if (group == BVSchemaGroup::UDIV_OBSERVED &&
      !bvSchemaGroupEnabled(mask, BVSchemaGroup::UDIV_OBSERVED))
    return BVSchemaGroup::UDIV_EXTRA;
  return group;
}

static const RemLemma REM_LEMMAS[] = {
    RemLemma::DividendZero,
    RemLemma::DivisorEqualsDividend,
    RemLemma::DividendBelowDivisor,
    // STP-specific, and ranked with the three facts above because it likewise
    // determines the result throughout its premise rather than only bounding it.
    RemLemma::RemainderIsDifference,
    RemLemma::DividendWithinDivisorOrRemainder,
    RemLemma::DividendAboveRemainderOrAnd,
    RemLemma::RemainderOutsideOperandsNotOne,
    RemLemma::RemainderNotOrOfComplements,
    RemLemma::RemainderInOperandsAboveLowBit,
    RemLemma::DividendNotOrOfNegations,
    RemLemma::DifferenceAboveRemainder,
    RemLemma::XorAboveRemainder,
    // Transcribed and tested, but deliberately never offered.
    RemLemma::RemainderBelowDivisorDisabled};

static const unsigned REM_LEMMA_COUNT =
    sizeof(REM_LEMMAS) / sizeof(REM_LEMMAS[0]);

static BVSchemaGroup remLemmaGroup(RemLemma lemma)
{
  switch (lemma)
  {
    case RemLemma::RemainderIsDifference:
      return BVSchemaGroup::QUOTIENT_ONE_REM;

    case RemLemma::DividendZero:
    case RemLemma::DivisorEqualsDividend:
    case RemLemma::DividendBelowDivisor:
    case RemLemma::RemainderBelowDivisorDisabled:
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
  assert(false && "RemLemma has no schema-group owner");
  return BVSchemaGroup::UREM;
}

const DivLemma* divLemmaTable(unsigned& count)
{
  count = DIV_LEMMA_COUNT;
  return DIV_LEMMAS;
}

const RemLemma* remLemmaTable(unsigned& count)
{
  count = REM_LEMMA_COUNT;
  return REM_LEMMAS;
}

DivSchemaChoice chooseDivSchema(Kind opKind, const std::vector<bool>& aBits,
                                const std::vector<bool>& bBits,
                                const std::vector<bool>& tBits,
                                uint64_t installedSchemas,
                                uint32_t enabledGroups)
{
  const unsigned width = (unsigned)tBits.size();
  const bool divisorZero = valueIsZero(bBits);
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
        (installedSchemas & DIV_SCHEMA_INSTALLED_REMAINDER_AT_MOST_DIVIDEND) ==
            0 &&
        !valueLessOrEqual(tBits, aBits))
      return {DivSchema::RemainderAtMostDividend, 0};

    // b != 0 -> r <u b.
    if (base &&
        (installedSchemas & DIV_SCHEMA_INSTALLED_REMAINDER_BELOW_DIVISOR) ==
            0 &&
        !divisorZero && valueLessOrEqual(bBits, tBits))
      return {DivSchema::RemainderBelowDivisor, 0};

    for (unsigned i = 0; i < REM_LEMMA_COUNT; ++i)
    {
      const RemLemma lemma = REM_LEMMAS[i];
      const BVSchemaGroup group = remLemmaGroup(lemma);
      if (!bvSchemaGroupEnabled(enabledGroups, group))
        continue;
      if (!remLemmaEnabled(lemma) || !remLemmaApplicable(lemma, width))
        continue;
      if ((installedSchemas & divLemmaInstalledBit(i)) != 0)
        continue;
      if (!remLemmaHolds(lemma, aBits, bBits, tBits))
        return {DivSchema::Lemma, 0, i, group};
    }
  }
  else if (opKind == BVDIV)
  {
    // b != 0 -> t <=u a.
    if (base &&
        (installedSchemas & DIV_SCHEMA_INSTALLED_QUOTIENT_AT_MOST_DIVIDEND) ==
            0 &&
        !divisorZero && !valueLessOrEqual(tBits, aBits))
      return {DivSchema::QuotientAtMostDividend, 0, 0};

    // Try the ranked, fixed family before the synthesised thresholds below.
    // A W-bit quotient has W-1 distinct threshold facts, so putting that
    // open-ended family first can consume the complete schema-round budget
    // and starve a single stronger fact that would decide the query.
    // Quotients only: every one is about `t = a udiv b`.
    for (unsigned i = 0; i < DIV_LEMMA_COUNT; ++i)
    {
      const BVSchemaGroup group = divLemmaGroup(DIV_LEMMAS[i]);
      if (!divLemmaGroupEnabled(enabledGroups, group))
        continue;
      if ((installedSchemas & divLemmaInstalledBit(i)) != 0)
        continue;
      if (!divLemmaApplicable(DIV_LEMMAS[i], width))
        continue;
      if (!divLemmaHolds(DIV_LEMMAS[i], aBits, bBits, tBits))
        return {DivSchema::Lemma, 0, i,
                divLemmaAccountingGroup(enabledGroups, group)};
    }

    // Use the candidate divisor's highest set bit as a broad guard:
    // b >= 2^k -> q <= a >> k. This family is deliberately capped at two
    // magnitudes per abstraction, so give it precedence over the open-ended
    // quotient thresholds below. On a query that pins the divisor's binade,
    // the magnitude bound can decide the result in one round; letting the
    // thresholds go first can consume the complete schema allowance before
    // this stronger candidate-specific bound gets a turn.
    if (bvSchemaGroupEnabled(enabledGroups,
                             BVSchemaGroup::DIVISOR_MAGNITUDE) &&
        divMagnitudeBoundsLeft(installedSchemas))
    {
      int divisorTop = -1;
      for (int i = (int)width - 1; i >= 0; --i)
        if (bBits[i])
        {
          divisorTop = i;
          break;
        }

      if (divisorTop >= 1)
      {
        std::vector<bool> shiftedDividend(width, false);
        for (unsigned i = 0; i + (unsigned)divisorTop < width; ++i)
          shiftedDividend[i] = aBits[i + (unsigned)divisorTop];
        if (!valueLessOrEqual(tBits, shiftedDividend))
          return {DivSchema::DivisorMagnitudeBound,
                  (unsigned)divisorTop, 0,
                  BVSchemaGroup::DIVISOR_MAGNITUDE};
      }
    }

    // q >= 2^k iff b <= (a >> k). The right side is just a comparison over
    // wires from the dividend; the left side is the OR of q[k..W-1]. Start
    // at one because k=0 is the already-covered q != 0 boundary. No
    // installed bit is needed: once one threshold is in the permanent
    // solver clauses, no later candidate can contradict that same k.
    const auto thresholdMismatch = [&](unsigned k) {
      std::vector<bool> shiftedDividend(width, false);
      for (unsigned i = 0; i + k < width; ++i)
        shiftedDividend[i] = aBits[i + k];
      const bool divisorBelowShiftedDividend =
          valueLessOrEqual(bBits, shiftedDividend);
      // The caller chooses only the two boundaries around the candidate's
      // highest set bit, so whether q >= 2^k is known from which one it is.
      bool quotientAboveThreshold = false;
      for (unsigned i = k; i < width; ++i)
        quotientAboveThreshold = quotientAboveThreshold || tBits[i];
      return quotientAboveThreshold != divisorBelowShiftedDividend;
    };

    // Every threshold below or at q's highest set bit has a true left side;
    // every one above it has a false left side. The real quotient has the
    // same shape, so if their magnitude bands differ, one of the two
    // boundaries around the candidate's band must witness it. Checking only
    // those two keeps schema selection linear in the width rather than
    // comparing W shifted dividends at O(W) apiece.
    int quotientTop = -1;
    for (int i = (int)width - 1; i >= 0; --i)
      if (tBits[i])
      {
        quotientTop = i;
        break;
      }
    if (bvSchemaGroupEnabled(enabledGroups, BVSchemaGroup::QUOTIENT_THRESHOLDS))
    {
      if (quotientTop > 0 && thresholdMismatch((unsigned)quotientTop))
        return {DivSchema::QuotientPow2Threshold, (unsigned)quotientTop, 0,
                BVSchemaGroup::QUOTIENT_THRESHOLDS};
      const unsigned above = (quotientTop < 1) ? 1u : (unsigned)quotientTop + 1;
      if (above < width && thresholdMismatch(above))
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
    case DivSchema::RemainderAtMostDividend: return "remainder-at-most-dividend";
    case DivSchema::RemainderBelowDivisor: return "remainder-below-divisor";
    case DivSchema::QuotientAtMostDividend: return "quotient-at-most-dividend";
    case DivSchema::QuotientPow2Threshold:
      return "power-of-two-quotient-threshold";
    case DivSchema::DivisorMagnitudeBound:
      return "divisor-magnitude-bound";
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
    case MulSchema::Lemma: return "lemma";
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

void encodeAddLowPrefix(SATSolver& solver,
                        const std::vector<unsigned>& aVars,
                        const std::vector<unsigned>& bVars,
                        const std::vector<unsigned>& resultVars,
                        unsigned width, unsigned prefixBits, bool aNegated,
                        bool bNegated)
{
  assert(width > 0);
  assert(prefixBits > 0 && prefixBits <= width);
  assert(aVars.size() >= width);
  assert(bVars.size() >= width);
  assert(resultVars.size() >= width);
  assert(!(aNegated && bNegated));

  unsigned carryVar = pinnedVar(solver, aNegated != bNegated);
  for (unsigned bit = 0; bit < prefixBits; ++bit)
  {
    const unsigned a = aVars[bit];
    const unsigned b = bVars[bit];
    const unsigned result = resultVars[bit];
    const unsigned carry = carryVar;
    SATSolver::vec_literals cl;

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

    if (bit + 1 < prefixBits)
    {
      const unsigned nextCarry = freshVar(solver);
      cl.clear(); cl.push(SATSolver::mkLit(a,aNegated));   cl.push(SATSolver::mkLit(b,bNegated));   cl.push(SATSolver::mkLit(nextCarry,true)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(a,aNegated));   cl.push(SATSolver::mkLit(carry,false));  cl.push(SATSolver::mkLit(nextCarry,true)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(b,bNegated));   cl.push(SATSolver::mkLit(carry,false));  cl.push(SATSolver::mkLit(nextCarry,true)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(a,!aNegated));  cl.push(SATSolver::mkLit(b,!bNegated));  cl.push(SATSolver::mkLit(nextCarry,false)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(a,!aNegated));  cl.push(SATSolver::mkLit(carry,true));   cl.push(SATSolver::mkLit(nextCarry,false)); solver.addClause(cl);
      cl.clear(); cl.push(SATSolver::mkLit(b,!bNegated));  cl.push(SATSolver::mkLit(carry,true));   cl.push(SATSolver::mkLit(nextCarry,false)); solver.addClause(cl);
      carryVar = nextCarry;
    }
  }
}

void encodeMulLowPrefix(SATSolver& solver,
                        const std::vector<unsigned>& aVars,
                        const std::vector<unsigned>& bVars,
                        const std::vector<unsigned>& resultVars,
                        unsigned width, unsigned prefixBits)
{
  assert(width > 0);
  assert(prefixBits > 0 && prefixBits <= width && prefixBits <= 3);
  assert(aVars.size() >= width);
  assert(bVars.size() >= width);
  assert(resultVars.size() >= width);

  const unsigned p00 = mkAnd(solver, aVars[0], bVars[0]);
  addEquivalence(solver, resultVars[0], p00);
  if (prefixBits == 1)
    return;

  const unsigned p10 = mkAnd(solver, aVars[1], bVars[0]);
  const unsigned p01 = mkAnd(solver, aVars[0], bVars[1]);
  addEquivalence(solver, resultVars[1], mkXor(solver, p10, p01));
  if (prefixBits == 2)
    return;

  // Column two consists of its three partial products plus the carry from
  // column one. Carries out of it are above the prefix and need not exist.
  const unsigned carry1 = mkAnd(solver, p10, p01);
  const unsigned p20 = mkAnd(solver, aVars[2], bVars[0]);
  const unsigned p11 = mkAnd(solver, aVars[1], bVars[1]);
  const unsigned p02 = mkAnd(solver, aVars[0], bVars[2]);
  const unsigned x0 = mkXor(solver, p20, p11);
  const unsigned x1 = mkXor(solver, p02, carry1);
  addEquivalence(solver, resultVars[2], mkXor(solver, x0, x1));
}

// oddOperand[0] = 1 and otherOperand != 0 -> result != 0.
//
// `resultNonzero` shares the OR of the result bits across the width clauses.
// Writing the implication out without it would put all W result literals in
// each of W clauses. With it, each bit of the other operand needs only the
// ternary clause below.
void encodeMulZeroProductOddOperand(SATSolver& solver,
                                    const std::vector<unsigned>& oddOperand,
                                    const std::vector<unsigned>& otherOperand,
                                    const std::vector<unsigned>& result,
                                    unsigned width)
{
  assert(width > 0);
  assert(oddOperand.size() == width);
  assert(otherOperand.size() == width);
  assert(result.size() == width);

  unsigned resultNonzero = result[0];
  for (unsigned i = 1; i < width; ++i)
    resultNonzero = mkOr(solver, resultNonzero, result[i]);

  for (unsigned i = 0; i < width; ++i)
  {
    SATSolver::vec_literals cl;
    cl.push(SATSolver::mkLit(oddOperand[0], true));
    cl.push(SATSolver::mkLit(otherOperand[i], true));
    cl.push(SATSolver::mkLit(resultNonzero, false));
    solver.addClause(cl);
  }
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

void encodeDivPow2Threshold(SATSolver& solver,
                            const std::vector<unsigned>& dividendVars,
                            const std::vector<unsigned>& divisorVars,
                            const std::vector<unsigned>& quotientVars,
                            unsigned width, unsigned shift)
{
  assert(width > 1);
  assert(shift > 0 && shift < width);
  assert(dividendVars.size() >= width);
  assert(divisorVars.size() >= width);
  assert(quotientVars.size() >= width);

  // Keep the comparison width unchanged: a divisor with any bit at or above
  // W-k cannot be <= the shifted dividend. The high zero is shared by all
  // of those positions.
  const unsigned zero = pinnedVar(solver, false);
  std::vector<unsigned> shiftedDividend(width, zero);
  for (unsigned i = 0; i + shift < width; ++i)
    shiftedDividend[i] = dividendVars[i + shift];

  const unsigned divisorBelowShiftedDividend = encodeLessOrEqual(
      solver, divisorVars, shiftedDividend, width, false);

  SATSolver::vec_literals cl;
  // comparison -> OR(quotient[shift..W-1])
  cl.push(SATSolver::mkLit(divisorBelowShiftedDividend, true));
  for (unsigned i = shift; i < width; ++i)
    cl.push(SATSolver::mkLit(quotientVars[i], false));
  solver.addClause(cl);

  // Each high quotient bit -> comparison. Together with the clause above,
  // these make the reduction-OR and the comparison equivalent without an
  // extra variable for the OR.
  for (unsigned i = shift; i < width; ++i)
  {
    cl.clear();
    cl.push(SATSolver::mkLit(quotientVars[i], true));
    cl.push(SATSolver::mkLit(divisorBelowShiftedDividend, false));
    solver.addClause(cl);
  }
}

void encodeDivisorMagnitudeBound(
    SATSolver& solver, const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& divisorVars,
    const std::vector<unsigned>& quotientVars, unsigned width,
    unsigned shift)
{
  assert(width > 1);
  assert(shift > 0 && shift < width);
  assert(dividendVars.size() >= width);
  assert(divisorVars.size() >= width);
  assert(quotientVars.size() >= width);

  const unsigned zero = pinnedVar(solver, false);
  std::vector<unsigned> shiftedDividend(width, zero);
  for (unsigned i = 0; i + shift < width; ++i)
    shiftedDividend[i] = dividendVars[i + shift];

  const unsigned quotientBelowShiftedDividend = encodeLessOrEqual(
      solver, quotientVars, shiftedDividend, width, false);

  // b >= 2^shift is the disjunction of b[shift..W-1]. Its implication to
  // the comparison is one binary clause per possible witnessing bit, which
  // exposes the guard directly to the SAT solver without an auxiliary OR.
  for (unsigned i = shift; i < width; ++i)
  {
    SATSolver::vec_literals cl;
    cl.push(SATSolver::mkLit(quotientBelowShiftedDividend, false));
    cl.push(SATSolver::mkLit(divisorVars[i], true));
    solver.addClause(cl);
  }
}

namespace
{
struct QuotientOneBand
{
  std::vector<unsigned> difference;
  unsigned divisorBelowDividend;
  unsigned divisorBelowDifference;
};

QuotientOneBand encodeQuotientOneBand(
    SATSolver& solver, const std::vector<unsigned>& dividendVars,
    const std::vector<unsigned>& divisorVars, unsigned width)
{
  QuotientOneBand band;
  band.difference.resize(width);
  for (unsigned i = 0; i < width; ++i)
    band.difference[i] = freshVar(solver);
  encodeAddLowPrefix(solver, dividendVars, divisorVars, band.difference, width,
                     width, false, true);

  band.divisorBelowDividend = encodeLessOrEqual(
      solver, divisorVars, dividendVars, width, false);
  band.divisorBelowDifference = encodeLessOrEqual(
      solver, divisorVars, band.difference, width, false);
  return band;
}
} // namespace

void encodeRemQuotientOne(SATSolver& solver,
                          const std::vector<unsigned>& dividendVars,
                          const std::vector<unsigned>& divisorVars,
                          const std::vector<unsigned>& remainderVars,
                          unsigned width)
{
  assert(width > 0);
  assert(dividendVars.size() >= width);
  assert(divisorVars.size() >= width);
  assert(remainderVars.size() >= width);

  const QuotientOneBand band =
      encodeQuotientOneBand(solver, dividendVars, divisorVars, width);

  // (b <= a && !(b <= a-b)) -> r = a-b. The second comparison is the
  // strict (a-b) < b edge, and makes the premise false when b is zero.
  for (unsigned i = 0; i < width; ++i)
  {
    SATSolver::vec_literals cl;
    cl.push(SATSolver::mkLit(band.divisorBelowDividend, true));
    cl.push(SATSolver::mkLit(band.divisorBelowDifference, false));
    cl.push(SATSolver::mkLit(remainderVars[i], true));
    cl.push(SATSolver::mkLit(band.difference[i], false));
    solver.addClause(cl);

    cl.clear();
    cl.push(SATSolver::mkLit(band.divisorBelowDividend, true));
    cl.push(SATSolver::mkLit(band.divisorBelowDifference, false));
    cl.push(SATSolver::mkLit(remainderVars[i], false));
    cl.push(SATSolver::mkLit(band.difference[i], true));
    solver.addClause(cl);
  }
}

void encodeDivQuotientOne(SATSolver& solver,
                          const std::vector<unsigned>& dividendVars,
                          const std::vector<unsigned>& divisorVars,
                          const std::vector<unsigned>& quotientVars,
                          unsigned width)
{
  assert(width > 0);
  assert(dividendVars.size() >= width);
  assert(divisorVars.size() >= width);
  assert(quotientVars.size() >= width);

  const QuotientOneBand band =
      encodeQuotientOneBand(solver, dividendVars, divisorVars, width);

  // (b <= a && !(b <= a-b)) -> q = 1. Bit zero is true and every other
  // quotient bit false under the shared premise.
  for (unsigned i = 0; i < width; ++i)
  {
    SATSolver::vec_literals cl;
    cl.push(SATSolver::mkLit(band.divisorBelowDividend, true));
    cl.push(SATSolver::mkLit(band.divisorBelowDifference, false));
    cl.push(SATSolver::mkLit(quotientVars[i], i == 0 ? false : true));
    solver.addClause(cl);
  }
}

void encodeDivRemLowPrefix(SATSolver& solver,
                           const std::vector<unsigned>& dividendVars,
                           const std::vector<unsigned>& divisorVars,
                           const std::vector<unsigned>& quotientVars,
                           const std::vector<unsigned>& remainderVars,
                           unsigned width, unsigned prefixBits)
{
  assert(width > 0);
  assert(prefixBits > 0 && prefixBits <= width && prefixBits <= 3);
  assert(dividendVars.size() >= width);
  assert(divisorVars.size() >= width);
  assert(quotientVars.size() >= width);
  assert(remainderVars.size() >= width);

  std::vector<unsigned> product(prefixBits);
  for (unsigned i = 0; i < prefixBits; ++i)
    product[i] = freshVar(solver);

  // Both component encoders depend only on the low prefix. Passing that as
  // their circuit width avoids minting W-prefix unused product variables.
  encodeMulLowPrefix(solver, quotientVars, divisorVars, product, prefixBits,
                     prefixBits);
  encodeAddLowPrefix(solver, product, remainderVars, dividendVars, prefixBits,
                     prefixBits);
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
  struct InconsistentDivRemPair {
    size_t divIdx;
    size_t remIdx;
    unsigned prefixBits;
    BVSchemaGroup group;
    ASTNode product;
  };

  std::vector<InconsistentCmp> incCmps;
  std::vector<InconsistentPlus> incPlus;
  std::vector<InconsistentITE> incITE;
  std::vector<InconsistentDivMul> incDivMul;
  std::vector<InconsistentDivRemPair> incDivRemPairs;
  std::vector<bool> handledByDivRemPair(terms_.size(), false);

  // A quotient and remainder over the same operands carry a relation neither
  // abstraction can state alone. Find those pairs by AST identity before the
  // per-record scan, and give a violated recomposition fact first refusal for
  // this round. Node numbers are unique within the manager and the width is
  // part of the key, so only genuinely identical operations meet here.
  const uint32_t enabledSchemaGroups =
      bm->UserFlags.bv_term_abstraction_schema_groups;
  const bool lowPairEnabled =
      bvSchemaGroupEnabled(enabledSchemaGroups, BVSchemaGroup::DIVREM_PAIR);
  const bool fullPairEnabled =
      bvSchemaGroupEnabled(enabledSchemaGroups, BVSchemaGroup::DIVREM_FULL);
  if (bm->UserFlags.bv_term_abstraction_schemas &&
      (lowPairEnabled || fullPairEnabled))
  {
    struct DivRemKey {
      uint64_t dividend;
      uint64_t divisor;
      unsigned width;

      bool operator==(const DivRemKey& other) const
      {
        return dividend == other.dividend && divisor == other.divisor &&
               width == other.width;
      }
    };
    struct DivRemKeyHash {
      size_t operator()(const DivRemKey& key) const
      {
        size_t h = std::hash<uint64_t>{}(key.dividend);
        h ^= std::hash<uint64_t>{}(key.divisor) + 0x9e3779b9u + (h << 6) +
             (h >> 2);
        h ^= std::hash<unsigned>{}(key.width) + 0x9e3779b9u + (h << 6) +
             (h >> 2);
        return h;
      }
    };
    struct DivRemPair {
      size_t divIdx = std::numeric_limits<size_t>::max();
      size_t remIdx = std::numeric_limits<size_t>::max();
    };

    std::unordered_map<DivRemKey, DivRemPair, DivRemKeyHash> pairs;
    for (size_t idx = 0; idx < terms_.size(); ++idx)
    {
      const BVTermAbstraction& abs = terms_[idx];
      if (abs.opKind != BVDIV && abs.opKind != BVMOD)
        continue;
      assert(abs.numOperands == 2);
      const DivRemKey key{abs.operands[0].GetNodeNum(),
                          abs.operands[1].GetNodeNum(), abs.width};
      DivRemPair& pair = pairs[key];
      if (abs.opKind == BVDIV)
        pair.divIdx = idx;
      else
        pair.remIdx = idx;
    }

    const size_t missing = std::numeric_limits<size_t>::max();
    for (const auto& entry : pairs)
    {
      const DivRemPair& pair = entry.second;
      if (pair.divIdx == missing || pair.remIdx == missing)
        continue;
      const BVTermAbstraction& div = terms_[pair.divIdx];
      const BVTermAbstraction& rem = terms_[pair.remIdx];
      const bool fullInstalled =
          div.divRemFullInstalled || rem.divRemFullInstalled;
      const bool lowAvailable =
          lowPairEnabled && !fullInstalled &&
          !div.divRemLowPrefixInstalled && !rem.divRemLowPrefixInstalled;
      const bool fullAvailable =
          fullPairEnabled && !fullInstalled;
      if (!lowAvailable && !fullAvailable)
        continue;
      const unsigned schemaLimit = bm->UserFlags.bv_term_abstraction_rounds;
      if (schemaLimit != 0 &&
          (div.schemaRounds >= schemaLimit || rem.schemaRounds >= schemaLimit))
        continue;

      std::vector<bool> dividendBits, divisorBits, quotientBits, remainderBits;
      getOperandBits(div.operands[0], div.width, nodeToSATVar, solver,
                     dividendBits);
      getOperandBits(div.operands[1], div.width, nodeToSATVar, solver,
                     divisorBits);
      readModelBits(encodedResultBitsOf(div, nodeToSATVar), div.width, solver,
                    quotientBits);
      readModelBits(encodedResultBitsOf(rem, nodeToSATVar), rem.width, solver,
                    remainderBits);

      const unsigned lowPrefix = std::min(3u, div.width);
      BVSchemaGroup chosenGroup = BVSchemaGroup::COUNT;
      ASTNode product;
      unsigned chosenPrefix = 0;
      if (lowAvailable &&
          !divRemLowPrefixHolds(dividendBits, divisorBits, quotientBits,
                                remainderBits, lowPrefix))
      {
        chosenGroup = BVSchemaGroup::DIVREM_PAIR;
        chosenPrefix = lowPrefix;
      }
      else if (fullAvailable &&
               !divRemLowPrefixHolds(dividendBits, divisorBits, quotientBits,
                                     remainderBits, div.width))
      {
        product = bm->defaultNodeFactory->CreateTerm(
            BVMULT, div.width, div.termNode, div.operands[1]);
        // A folded product leaves no multiplication circuit worth splicing.
        // The individual schemas and fallback below remain available.
        if (product.GetKind() != BVMULT)
          continue;
        chosenGroup = BVSchemaGroup::DIVREM_FULL;
        chosenPrefix = div.width;
      }
      else
        continue;

      incDivRemPairs.push_back(
          {pair.divIdx, pair.remIdx, chosenPrefix, chosenGroup, product});
      handledByDivRemPair[pair.divIdx] = true;
      handledByDivRemPair[pair.remIdx] = true;
    }
  }

  for (size_t idx = 0; idx < terms_.size(); ++idx)
  {
    auto& abs = terms_[idx];
    if (handledByDivRemPair[idx])
      continue;
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

      bool carry = carryInit;
      bool consistent = true;
      std::vector<bool> actual(abs.width);
      for (unsigned bit = 0; bit < abs.width; ++bit)
      {
        bool l = leftBits[bit] ^ lNeg;
        bool r = rightBits[bit] ^ rNeg;
        bool s = (solver.modelValue(resultVars[bit]) == solver.true_literal());
        actual[bit] = s;
        bool expectedSum = l ^ r ^ carry;
        carry = (l && r) || (l && carry) || (r && carry);
        if (s != expectedSum)
          consistent = false;
      }
      if (consistent) continue;

      if (lNeg)
        leftBits = negatedValue(leftBits);
      if (rNeg)
        rightBits = negatedValue(rightBits);

      AddSchemaChoice schema;
      const unsigned schemaLimit = bm->UserFlags.bv_term_abstraction_rounds;
      if (bm->UserFlags.bv_term_abstraction_schemas &&
          (schemaLimit == 0 || abs.schemaRounds < schemaLimit))
        schema =
            chooseAddSchema(leftBits, rightBits, actual, abs.installedSchemas,
                            bm->UserFlags.bv_term_abstraction_schema_groups);

      incPlus.push_back({idx, schema});
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
        if (abs.opKind == BVMULT)
          schema =
              chooseMulSchema(aBits, bBits, actual, abs.installedSchemas,
                              bm->UserFlags.bv_term_abstraction_schema_groups);
        else
          divSchema = chooseDivSchema(
              abs.opKind, aBits, bBits, actual, abs.installedSchemas,
              bm->UserFlags.bv_term_abstraction_schema_groups);
      }

      incDivMul.push_back({idx, std::move(aBits), std::move(bBits),
                            std::move(expected), schema, divSchema,
                            lowestWrongBit});
    }
  }

  // Phase 2: Add refinement clauses (no model reads needed).
  unsigned refined = 0;

  for (const InconsistentDivRemPair& inc : incDivRemPairs)
  {
    BVTermAbstraction& div = terms_[inc.divIdx];
    BVTermAbstraction& rem = terms_[inc.remIdx];
    std::vector<unsigned> dividendVars, divisorVars;
    getOperandVars(div.operands[0], div.width, nodeToSATVar, solver,
                   dividendVars);
    getOperandVars(div.operands[1], div.width, nodeToSATVar, solver,
                   divisorVars);
    const std::vector<unsigned>& quotientVars =
        encodedResultBitsOf(div, nodeToSATVar);
    const std::vector<unsigned>& remainderVars =
        encodedResultBitsOf(rem, nodeToSATVar);

    if (inc.group == BVSchemaGroup::DIVREM_PAIR)
    {
      encodeDivRemLowPrefix(solver, dividendVars, divisorVars, quotientVars,
                            remainderVars, div.width, inc.prefixBits);
      div.divRemLowPrefixInstalled = true;
      rem.divRemLowPrefixInstalled = true;
    }
    else
    {
      assert(inc.group == BVSchemaGroup::DIVREM_FULL);
      BVExactEncoder(bm).encodeDivRemIdentity(
          solver, inc.product, div.width, dividendVars, divisorVars,
          quotientVars, remainderVars);
      div.divRemFullInstalled = true;
      rem.divRemFullInstalled = true;
    }
    div.schemaRounds++;
    rem.schemaRounds++;
    countSchemaLemma(bm->UserFlags, inc.group);
    if (bm->UserFlags.stats_flag)
      std::cerr << "BV abstraction: paired BVDIV/BVMOD "
                << (inc.group == BVSchemaGroup::DIVREM_FULL ? "full " : "")
                << "recomposition lemma over " << inc.prefixBits << " bits"
                << std::endl;
    refined++;
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

    if (inc.schema.found)
    {
      if (inc.schema.prefixBits != 0)
      {
        encodeAddLowPrefix(solver, leftVars, rightVars, resultVars, abs.width,
                           inc.schema.prefixBits, lNeg, rNeg);
        abs.installedSchemas |= ADD_SCHEMA_INSTALLED_LOW_PREFIX;
        abs.blastedBits = inc.schema.prefixBits;
        abs.defined = (inc.schema.prefixBits == abs.width);
        abs.schemaRounds++;
        countSchemaLemma(bm->UserFlags, inc.schema.group);
        if (bm->UserFlags.stats_flag)
          std::cerr << "BV abstraction: BVPLUS exact-low-prefix lemma over "
                    << inc.schema.prefixBits << " bits" << std::endl;
        refined++;
        continue;
      }

      const std::vector<unsigned>* rawVars[2] = {&leftVars, &rightVars};
      const bool negated[2] = {lNeg, rNeg};
      const std::vector<unsigned>* effectiveVars[2] = {rawVars[0], rawVars[1]};
      for (unsigned i = 0; i < 2; ++i)
        if (negated[i])
        {
          if (abs.negatedOperand[i].empty())
            abs.negatedOperand[i] = encodeNegate(solver, *rawVars[i], abs.width);
          effectiveVars[i] = &abs.negatedOperand[i];
        }

      const unsigned chosen = inc.schema.operand;
      BVExactEncoder(bm).encodeAddLemma(
          solver, ADD_LEMMAS[inc.schema.lemmaIndex], abs.width,
          *effectiveVars[chosen], *effectiveVars[1 - chosen], resultVars);
      abs.installedSchemas |=
          addLemmaInstalledBit(inc.schema.lemmaIndex, chosen);
      abs.schemaRounds++;
      countSchemaLemma(bm->UserFlags, inc.schema.group);
      if (bm->UserFlags.stats_flag)
        std::cerr << "BV abstraction: BVPLUS "
                  << addLemmaName(ADD_LEMMAS[inc.schema.lemmaIndex])
                  << " lemma over operand " << chosen << std::endl;
      refined++;
      continue;
    }

    // No schema remained: define the whole addition. The same encoder is
    // used for the prefix above, so a polarity fix cannot make the two paths
    // silently disagree.
    encodeAddLowPrefix(solver, leftVars, rightVars, resultVars, abs.width,
                       abs.width, lNeg, rNeg);

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

        case DivSchema::QuotientPow2Threshold:
          assert(abs.opKind == BVDIV);
          encodeDivPow2Threshold(solver, aVars, bVars, resultVars, W,
                                 inc.divSchema.shift);
          break;

        case DivSchema::DivisorMagnitudeBound:
          assert(abs.opKind == BVDIV);
          encodeDivisorMagnitudeBound(solver, aVars, bVars, resultVars, W,
                                      inc.divSchema.shift);
          for (unsigned i = 0; i < DIV_SCHEMA_MAGNITUDE_BOUND_ALLOWANCE; ++i)
            if ((abs.installedSchemas & divMagnitudeBoundBit(i)) == 0)
            {
              abs.installedSchemas |= divMagnitudeBoundBit(i);
              break;
            }
          break;

        case DivSchema::Lemma:
          if (abs.opKind == BVDIV)
            BVExactEncoder(bm).encodeDivLemma(
                solver, DIV_LEMMAS[inc.divSchema.lemmaIndex], W, aVars, bVars,
                resultVars);
          else
          {
            assert(abs.opKind == BVMOD);
            BVExactEncoder(bm).encodeRemLemma(
                solver, REM_LEMMAS[inc.divSchema.lemmaIndex], W, aVars, bVars,
                resultVars);
          }
          abs.installedSchemas |=
              divLemmaInstalledBit(inc.divSchema.lemmaIndex);
          break;

        case DivSchema::None:
          break;
      }

      abs.schemaRounds++;
      countSchemaLemma(bm->UserFlags, inc.divSchema.group);
      if (bm->UserFlags.stats_flag)
        std::cerr << "BV abstraction: " << _kind_names[abs.opKind] << " "
                  << (inc.divSchema.schema == DivSchema::Lemma
                          ? (abs.opKind == BVDIV
                                 ? divLemmaName(
                                       DIV_LEMMAS[inc.divSchema.lemmaIndex])
                                 : remLemmaName(
                                       REM_LEMMAS[inc.divSchema.lemmaIndex]))
                          : divSchemaName(inc.divSchema.schema))
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
          encodeMulLowPrefix(solver, aVars, bVars, resultVars, W,
                             inc.schema.shift);
          abs.installedSchemas |= MUL_SCHEMA_INSTALLED_LOW_PREFIX;
          abs.blastedBits = inc.schema.shift;
          abs.defined = (inc.schema.shift == W);
          break;

        case MulSchema::Lemma:
          BVExactEncoder(bm).encodeMulLemma(
              solver, MUL_LEMMAS[inc.schema.lemmaIndex], W, *opVars[chosen],
              *opVars[1 - chosen], resultVars);
          abs.installedSchemas |=
              mulLemmaInstalledBit(inc.schema.lemmaIndex, chosen);
          break;

        case MulSchema::None:
          break;
      }

      abs.schemaRounds++;
      countSchemaLemma(bm->UserFlags, inc.schema.group);
      if (bm->UserFlags.stats_flag)
      {
        std::cerr << "BV abstraction: BVMULT "
                  << (inc.schema.schema == MulSchema::Lemma
                          ? mulLemmaName(MUL_LEMMAS[inc.schema.lemmaIndex])
                          : mulSchemaName(inc.schema.schema))
                  << " lemma";
        if (inc.schema.schema == MulSchema::LowPrefix)
          std::cerr << " over " << inc.schema.shift << " bits";
        else
          std::cerr << " over operand " << chosen;
        std::cerr << std::endl;
      }
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

      BVExactEncoder(bm).encode(solver, encodeAs, upto, aVars, bVars,
                                resultVars);
      abs.blastedBits = upto;
      abs.defined = (upto == W);

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
