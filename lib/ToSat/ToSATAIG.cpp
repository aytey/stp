/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Dan Liew, Mate Soos
 *
 * BEGIN DATE: November, 2005
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

#include "stp/ToSat/ToSATAIG.h"
#include "stp/ToSat/BVEQCongruenceClosure.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include <sstream>

namespace stp
{

THREAD_LOCAL_IE int ToSATAIG::cnf_calls = 0;

bool ToSATAIG::CallSAT(SATSolver& satSolver, const ASTNode& input,
                       bool needAbsRef)
{
  if (cb != NULL && cb->isUnsatisfiable())
    return false;

  if (!first)
  {
    assert(input == ASTTrue);
    return runSolver(satSolver);
  }

  // Shortcut if known. This avoids calling the setup of the CNF generator.
  // setup of the CNF generator is expensive. NB, these checks have to occur
  // after calling the sat solver (if it's not the first time.)
  if (input == ASTFalse)
    return false;

  if (input == ASTTrue)
  {
    // A formula which preprocessing proved true can still own active UF
    // results and argument names.  They are the sole candidate authority for
    // the checker and future congruence lemmas, so the ordinary constant-root
    // shortcut is legal only when there are no such scalars.  Register and
    // solve the disconnected variables here instead of letting the model
    // evaluator invent values for symbols which never reached SAT.
    UFContext* uf = bm->getUFContextIfAny();
    if (uf == NULL || !uf->activeInSolve() || uf->getSolveScalars().empty())
      return true;

    first = false;
    delete cb;
    cb = NULL;
    assert(satSolver.nVars() == 0);
    mark_variables_as_frozen(satSolver);
    return runSolver(satSolver);
  }

  first = false;
  Cnf_Dat_t* cnfData = bitblast(input, needAbsRef);

  if (cnfData == NULL)
  {
    bm->soft_timeout_expired = true;
    return false;
  }

  handle_cnf_options(cnfData, needAbsRef);

  assert(satSolver.nVars() == 0);
  add_cnf_to_solver(satSolver, cnfData);

  release_cnf_memory(cnfData);

  mark_variables_as_frozen(satSolver);

  return runSolver(satSolver);
}

void ToSATAIG::release_cnf_memory(Cnf_Dat_t* cnfData)
{
  // This releases the memory used by the CNF generator, particularly some data
  // tables.
  // If CNF generation is going to be called lots, we'd rather keep it around.
  // because the datatables are expensive to generate.
  if (cnf_calls == 0)
    Cnf_ManFree();

  Cnf_DataFree(cnfData);
  cnf_calls++;
}

void ToSATAIG::handle_cnf_options(Cnf_Dat_t* cnfData, bool needAbsRef)
{
  if (bm->UserFlags.output_CNF_flag)
  {
    std::stringstream fileName;
    fileName << "output_" << bm->CNFFileNameCounter++ << ".cnf";
    Cnf_DataWriteIntoFile(cnfData, (char*)fileName.str().c_str(), 0,0,0);
  }

  if (bm->UserFlags.exit_after_CNF)
  {
    if (bm->UserFlags.quick_statistics_flag)
      bm->GetRunTimes()->print();

    if (needAbsRef)
    {
      cerr << "Warning: STP is exiting after generating the first CNF."
           << " But the CNF is probably partial which you probably don't want."
           << " You probably want to disable"
           << " refinement with the \"-r\" command line option." << endl;
    }

    exit(0);
  }
}

Cnf_Dat_t* ToSATAIG::bitblast(const ASTNode& input, bool needAbsRef)
{
  stp::SubstitutionMap sm(bm);
  Simplifier simp(bm, &sm);

  BBNodeManagerAIG mgr;
  mgr.nodeBudget = bm->UserFlags.aig_node_budget;
  BitBlaster bb(&mgr, &simp, bm->defaultNodeFactory, &bm->UserFlags, cb);

  bm->GetRunTimes()->start(RunTimes::BitBlasting);

  try
  {
    BBNodeAIG BBFormula = bb.BBForm(input);
    for (const auto& sc : bb.sideConstraints())
      BBFormula = BBNodeAIG(Aig_And(mgr.aigMgr, BBFormula.n, sc.n));
    bm->GetRunTimes()->stop(RunTimes::BitBlasting);

    delete cb;
    cb = NULL;
    bb.cb = NULL;

    bm->GetRunTimes()->start(RunTimes::CNFConversion);
    Cnf_Dat_t* cnfData = NULL;
    toCNF.toCNF(BBFormula, cnfData, nodeToSATVar, needAbsRef, mgr);
    bm->GetRunTimes()->stop(RunTimes::CNFConversion);

    for (const auto& raw : bb.abstractedEQs())
    {
      BVEQAbstraction a;
      a.eqNode = raw.eqNode;
      Aig_Obj_t* pObj = (Aig_Obj_t*)Vec_PtrEntry(
          mgr.aigMgr->vCis, raw.abstractionCI.symbol_index);
      a.abstractionSATVar = cnfData->pVarNums[pObj->Id];
      a.leftSymbol = raw.leftSymbol;
      a.rightSymbol = raw.rightSymbol;
      a.width = std::max(1u, raw.leftSymbol.GetValueWidth());
      bvEQAbstractions_.push_back(std::move(a));
    }

    for (const auto& raw : bb.abstractedTerms())
    {
      BVTermAbstraction a;
      a.termNode = raw.termNode;
      a.opKind = raw.opKind;
      for (unsigned i = 0; i < raw.numOperands; i++)
      {
        a.operands[i] = raw.operands[i];
        a.operandNegated[i] = raw.operandNegated[i];
      }
      a.numOperands = raw.numOperands;
      a.width = raw.width;
      if (raw.condCISymbolIndex >= 0)
      {
        Aig_Obj_t* condObj = (Aig_Obj_t*)Vec_PtrEntry(
            mgr.aigMgr->vCis, raw.condCISymbolIndex);
        a.condSATVar = cnfData->pVarNums[condObj->Id];
      }
      bvTermAbstractions_.push_back(std::move(a));
    }

    BBFormula = BBNodeAIG(); // null node
    mgr.stop();

    return cnfData;
  }
  catch (const AIGBudgetExhausted& e)
  {
    bm->GetRunTimes()->stop(RunTimes::BitBlasting);
    if (bm->UserFlags.stats_flag)
      cerr << "AIG node budget exhausted at " << e.nodeCount << " nodes"
           << endl;
    // Say so here, where the reason is known. The no-answer leaves through the
    // same door a clock expiry does -- soft_timeout_expired, so that the whole
    // pipeline unwinds the one way it knows -- and by the time it surfaces
    // nothing can tell the two apart. This is not a clock: more time on the
    // same machine reproduces it exactly, and what a caller can act on is the
    // flag to raise.
    //
    // Phrased alongside the conflict budget's own sentence, and carrying the
    // count it stopped at, which is the one number that says how much higher
    // to set it. AND gates rather than nodes, because that is what the budget
    // counts.
    std::ostringstream detail;
    detail << "the AIG node budget set by --aig-node-budget ("
           << bm->UserFlags.aig_node_budget << ") ran out at " << e.nodeCount
           << " AND gates; raise it, or set it to 0 for no limit";
    bm->noteUnknown(UnknownReason::AIGBudget, detail.str());
    delete cb;
    cb = NULL;
    bb.cb = NULL;
    mgr.stop();
    return NULL;
  }
}

void ToSATAIG::add_cnf_to_solver(SATSolver& satSolver, Cnf_Dat_t* cnfData)
{
  bm->GetRunTimes()->start(RunTimes::SendingToSAT);

  // Create a new sat variable for each of the variables in the CNF.
  int satV = satSolver.nVars();
  for (int i = 0; i < cnfData->nVars - satV; i++)
    satSolver.newVar();

  SATSolver::vec_literals satSolverClause;
  for (int i = 0; i < cnfData->nClauses; i++)
  {
    satSolverClause.clear();
    for (int *pLit = cnfData->pClauses[i], *pStop = cnfData->pClauses[i + 1];
         pLit < pStop; pLit++)
    {
      uint32_t var = (*pLit) >> 1;
      assert((var < satSolver.nVars()));
      SATSolver::Lit l = SATSolver::mkLit(var, (*pLit) & 1);
      satSolverClause.push(l);
    }

    satSolver.addClause(satSolverClause);
    if (!satSolver.okay())
      break;
  }
  bm->GetRunTimes()->stop(RunTimes::SendingToSAT);
}

void ToSATAIG::mark_variables_as_frozen(SATSolver& satSolver)
{
  for (ArrayTransformer::ArrType::iterator it =
           arrayTransformer->arrayToIndexToRead.begin();
       it != arrayTransformer->arrayToIndexToRead.end(); it++)
  {
    const ArrayTransformer::arrTypeMap& atm = it->second;

    for (ArrayTransformer::arrTypeMap::const_iterator arr_it = atm.begin();
         arr_it != atm.end(); arr_it++)
    {
      // A bit that reached no SAT variable is marked with ~0u rather than
      // omitted, so freezing has to skip it: the sentinel is not a variable
      // index, and a backend that acts on setFrozen() writes out of bounds
      // when handed it. The extensionality loop below already guards this.
      const ArrayTransformer::ArrayRead& ar = arr_it->second;
      ASTNodeToSATVar::iterator it = nodeToSATVar.find(ar.index_symbol);
      if (it != nodeToSATVar.end())
      {
        const vector<unsigned>& v = it->second;
        for (size_t i = 0, size = v.size(); i < size; ++i)
          if (v[i] != ~((unsigned)0))
            satSolver.setFrozen(v[i]);
      }

      ASTNodeToSATVar::iterator it2 = nodeToSATVar.find(ar.symbol);
      if (it2 != nodeToSATVar.end())
      {
        const vector<unsigned>& v = it2->second;
        for (size_t i = 0, size = v.size(); i < size; ++i)
          if (v[i] != ~((unsigned)0))
            satSolver.setFrozen(v[i]);
      }
    }
  }

  // The array-equality procedure encodes its refinement lemmas over
  // the SAT variables of its abstraction variables, witness symbols
  // and scalar names; keep those variables from being eliminated.
  ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  if (ext != NULL && ext->activeInSolve())
  {
    const std::set<ASTNode>& symbols = ext->getFrozenSymbols();
    for (std::set<ASTNode>::const_iterator it = symbols.begin();
         it != symbols.end(); ++it)
    {
      ASTNodeToSATVar::iterator vit = nodeToSATVar.find(*it);
      if (vit == nodeToSATVar.end())
        continue;
      const vector<unsigned>& v = vit->second;
      for (size_t i = 0, size = v.size(); i < size; ++i)
        if (v[i] != ~((unsigned)0))
          satSolver.setFrozen(v[i]);
    }

    // A lemma-only symbol -- an owned read's abstraction variable or
    // index -- may legally never have reached the bit-blast: the
    // read's only occurrence can itself sit inside another abstracted
    // term. Its semantics live entirely in future refinement lemmas,
    // so fresh SAT variables allocated here, before the first solve,
    // are exactly the unconstrained meaning the blasted formula gives
    // it; the model loop then values them like any other symbol, and
    // the lemmas constrain the same variables the candidate was
    // checked against. Names defined by equations are deliberately
    // not treated this way -- for them a missing vector still fails
    // loudly at lemma encoding.
    const std::set<ASTNode>& lemmaOnly = ext->getLemmaOnlySymbols();
    for (std::set<ASTNode>::const_iterator it = lemmaOnly.begin();
         it != lemmaOnly.end(); ++it)
    {
      if (nodeToSATVar.find(*it) != nodeToSATVar.end())
        continue;
      const unsigned width = it->GetValueWidth();
      vector<unsigned> v(width);
      for (unsigned i = 0; i < width; i++)
      {
        v[i] = satSolver.newVar();
        satSolver.setFrozen(v[i]);
      }
      nodeToSATVar.insert(make_pair(*it, v));
    }
  }

  // Give every checker-visible scalar one complete mapping in this backend.
  // Connected bits retain their CNF variables; missing/disconnected bits get
  // fresh unconstrained variables, which is exactly their formula semantics.
  // Registration happens after CNF conversion so no second AIG-side meaning
  // can compete with the mapping the checker and lemma encoder both consume.
  UFContext* ufContext = bm->getUFContextIfAny();
  if (ufContext != NULL && ufContext->activeInSolve())
  {
    for (const ASTNode& symbol : ufContext->getSolveScalars())
    {
      if (symbol.GetKind() != SYMBOL)
        FatalError("UF solve-scalar registrar received a non-symbol", symbol);
      const unsigned width = std::max((unsigned)1, symbol.GetValueWidth());
      ASTNodeToSATVar::iterator found = nodeToSATVar.find(symbol);
      if (found == nodeToSATVar.end())
        found = nodeToSATVar
                    .insert(std::make_pair(
                        symbol, vector<unsigned>(width, ~((unsigned)0))))
                    .first;
      if (found->second.size() > width)
        FatalError("UF batch liveness mapping has the wrong width", symbol);
      if (found->second.size() < width)
        found->second.resize(width, ~((unsigned)0));
      for (unsigned bit = 0; bit < width; ++bit)
      {
        if (found->second[bit] == ~((unsigned)0))
          found->second[bit] = satSolver.newVar();
        satSolver.setFrozen(found->second[bit]);
      }
    }
    suggest_uf_scalar_phases(satSolver);
  }

  for (const auto& a : bvEQAbstractions_)
    satSolver.setFrozen(a.abstractionSATVar);

  for (const auto& a : bvTermAbstractions_)
  {
    auto resultIt = nodeToSATVar.find(a.termNode);
    if (resultIt != nodeToSATVar.end())
      for (unsigned v : resultIt->second)
        if (v != ~((unsigned)0))
          satSolver.setFrozen(v);
    for (unsigned i = 0; i < a.numOperands; i++)
    {
      auto opIt = nodeToSATVar.find(a.operands[i]);
      if (opIt != nodeToSATVar.end())
        for (unsigned v : opIt->second)
          if (v != ~((unsigned)0))
            satSolver.setFrozen(v);
    }
    if (a.condSATVar != 0)
      satSolver.setFrozen(a.condSATVar);
  }
}

// Bias the first candidate so the checker's scalars start out pairwise
// different.
//
// The refinement loop's cost is collisions: two applications whose arguments
// read the same values and whose results do not. Nothing tells the backend
// that spreading unconstrained scalars out is worth anything, so its default
// phase puts many of them on the same value at once and each collision is
// paid for with a lemma and another full solve. Counting the scalars off
// against an increasing value is the same trick Bitwuzla plays for DISTINCT,
// applied to what the congruence checker reads.
//
// This is only a hint: it reorders the search and cannot change which answers
// are reachable, so no soundness argument rests on the choice being good. A
// backend without a phase interface ignores it. Scalars are visited in node
// order rather than the set's, so the same query gets the same hints.
void ToSATAIG::suggest_uf_scalar_phases(SATSolver& satSolver)
{
  if (!bm->UserFlags.uf_phase_hints)
    return;
  UFContext* ufContext = bm->getUFContextIfAny();
  if (ufContext == NULL)
    return;

  std::vector<ASTNode> scalars(ufContext->getSolveScalars().begin(),
                               ufContext->getSolveScalars().end());
  std::sort(scalars.begin(), scalars.end(),
            [](const ASTNode& left, const ASTNode& right)
            { return left.GetNodeNum() < right.GetNodeNum(); });

  // The hints have to land on variables the backend has already declared.
  // CaDiCaL's factoring layer declares lazily -- on a clause, an assumption,
  // or at the start of a solve -- and silently ignores a phase for anything
  // it has not seen, which is every scalar registered above, since those are
  // fresh variables no clause mentions. Declaring is the caller's job, not an
  // advisory hint's: done here, before the first solve, it cannot disturb a
  // model, which is the reason suggestPhase itself must not do it.
  satSolver.declarePendingVariables();

  uint64_t counter = 0;
  for (const ASTNode& symbol : scalars)
  {
    const ASTNodeToSATVar::const_iterator found = nodeToSATVar.find(symbol);
    if (found == nodeToSATVar.end())
      continue;
    const uint64_t value = counter++;
    for (unsigned bit = 0; bit < found->second.size(); ++bit)
    {
      if (found->second[bit] == ~((unsigned)0))
        continue;
      const bool on = bit < 64 && ((value >> bit) & 1ULL) != 0;
      satSolver.suggestPhase(found->second[bit], on);
    }
  }
}

bool ToSATAIG::runSolver(SATSolver& satSolver)
{
  bm->GetRunTimes()->start(RunTimes::Solving);
  bool result = satSolver.solve(bm->soft_timeout_expired);
  bm->GetRunTimes()->stop(RunTimes::Solving);

  if (bm->soft_timeout_expired)
    bm->noteBudgetExhausted(satSolver);

  if (bm->UserFlags.stats_flag)
    satSolver.printStats();

  return result;
}

// Both abstraction families in one call, equalities first: theirs is the
// cheaper scan, and the congruence phase inside it can refute a candidate
// at word level without reading a single bit. A round that refined an
// equality stops there rather than going on to the terms -- the term scan
// reads the same model, and what it would find in it has already been
// ruled out.
unsigned ToSATAIG::refineAbstractions(SATSolver& solver)
{
  unsigned refined = 0;
  if (hasBVEQAbstractions())
    refined = refineBVEQInconsistencies(solver);
  if (refined == 0 && hasBVTermAbstractions())
    refined = refineBVTermInconsistencies(solver);
  if (refined > 0)
  {
    abstractionRefinements_ += refined;
    if (bm->UserFlags.stats_flag)
      std::cerr << "BV abstraction: refined " << refined << " operations"
                << std::endl;
  }
  return refined;
}

unsigned ToSATAIG::refineBVEQInconsistencies(SATSolver& solver)
{
  // Phase 1: Congruence closure — detect transitivity conflicts at word level.
  {
    std::unordered_map<ASTNode, unsigned, ASTNode::ASTNodeHasher,
                       ASTNode::ASTNodeEqual> symbolToIdx;
    unsigned nextIdx = 0;
    for (const auto& abs : bvEQAbstractions_)
    {
      if (abs.defined) continue;
      if (symbolToIdx.find(abs.leftSymbol) == symbolToIdx.end())
        symbolToIdx[abs.leftSymbol] = nextIdx++;
      if (symbolToIdx.find(abs.rightSymbol) == symbolToIdx.end())
        symbolToIdx[abs.rightSymbol] = nextIdx++;
    }

    std::vector<BVEQCongruenceClosure::EqInfo> eqInfos;
    for (const auto& abs : bvEQAbstractions_)
    {
      if (abs.defined) continue;
      bool modelTrue =
          (solver.modelValue(abs.abstractionSATVar) == solver.true_literal());
      eqInfos.push_back({symbolToIdx[abs.leftSymbol],
                          symbolToIdx[abs.rightSymbol],
                          abs.abstractionSATVar,
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
  };
  std::vector<InconsistentEQ> incEQs;

  for (size_t idx = 0; idx < bvEQAbstractions_.size(); ++idx)
  {
    auto& abs = bvEQAbstractions_[idx];
    if (abs.defined)
      continue;

    bool absTrue =
        (solver.modelValue(abs.abstractionSATVar) == solver.true_literal());

    auto leftIt = nodeToSATVar.find(abs.leftSymbol);
    auto rightIt = nodeToSATVar.find(abs.rightSymbol);
    if (leftIt == nodeToSATVar.end() || rightIt == nodeToSATVar.end())
      continue;

    bool actualEqual = true;
    for (unsigned bit = 0; bit < abs.width; ++bit)
    {
      if (solver.modelValue(leftIt->second[bit]) !=
          solver.modelValue(rightIt->second[bit]))
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

    incEQs.push_back({idx, newEnd, &leftIt->second, &rightIt->second});
  }

  // Clause phase: add Tseitin encoding (no model reads).
  unsigned refined = 0;
  for (auto& inc : incEQs)
  {
    auto& abs = bvEQAbstractions_[inc.absIdx];

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

static bool getOperandBits(
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
    return true;
  }
  auto it = nodeToSATVar.find(operand);
  if (it == nodeToSATVar.end()) return false;
  const std::vector<unsigned>& satVars = it->second;
  for (unsigned i = 0; i < width; ++i)
    bits[i] = (solver.modelValue(satVars[i]) == solver.true_literal());
  return true;
}

static bool getOperandVars(
    const ASTNode& operand, unsigned width,
    const ToSATBase::ASTNodeToSATVar& nodeToSATVar, SATSolver& solver,
    std::vector<unsigned>& vars)
{
  vars.resize(width);
  if (operand.GetKind() == BVCONST)
  {
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
    return true;
  }
  auto it = nodeToSATVar.find(operand);
  if (it == nodeToSATVar.end()) return false;
  vars = it->second;
  return true;
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

// Exact CNF for the operations whose refinement would otherwise enumerate.
//
// A blocking lemma rules out one pair of operand values, so a query the solver
// has to search through can need more rounds than there are pairs of operands:
// a 64-bit factorisation spent 5816 of them and ninety seconds on a query the
// unabstracted solve answers in five hundredths of one. Past
// bv_term_abstraction_rounds the refinement stops enumerating and says what
// the operation is, over the same variables it has been talking about all
// along -- the operand proxies and the abstraction's own result bits, which
// are already in the solver and already frozen. The abstraction is then
// defined, so it is never revisited and the solve ends on the next round with
// the answer it would have given had the term never been abstracted.
//
// Everything below is built from three gates, so that nothing here is a fresh
// hand-written clause block; each is written out of the row of the truth table
// it rules out. mkLit(v, sign) is false exactly when v equals sign, so a
// literal at `bit` is false exactly when that input is `bit`, and a clause
// listing one row is falsified only on that row.

// Every bit of this vector reached the CNF. ~0u marks one that did not; a
// lemma written over it would be talking about a variable that does not exist.
static bool usableVars(const std::vector<unsigned>& vars, unsigned width)
{
  if (vars.size() < width)
    return false;
  for (unsigned i = 0; i < width; ++i)
    if (vars[i] == ~((unsigned)0))
      return false;
  return true;
}

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

// z <-> x & y
static unsigned mkAnd(SATSolver& solver, unsigned x, unsigned y)
{
  const unsigned z = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(y, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(y, false)); cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  return z;
}

// z <-> (sel ? t : e)
static unsigned mkMux(SATSolver& solver, unsigned sel, unsigned t, unsigned e)
{
  const unsigned z = freshVar(solver);
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(sel, true));  cl.push(SATSolver::mkLit(t, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(sel, true));  cl.push(SATSolver::mkLit(t, false)); cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(sel, false)); cl.push(SATSolver::mkLit(e, true));  cl.push(SATSolver::mkLit(z, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(sel, false)); cl.push(SATSolver::mkLit(e, false)); cl.push(SATSolver::mkLit(z, true));  solver.addClause(cl);
  return z;
}

// x <-> y
static void addEquiv(SATSolver& solver, unsigned x, unsigned y)
{
  SATSolver::vec_literals cl;
  cl.clear(); cl.push(SATSolver::mkLit(x, true));  cl.push(SATSolver::mkLit(y, false)); solver.addClause(cl);
  cl.clear(); cl.push(SATSolver::mkLit(x, false)); cl.push(SATSolver::mkLit(y, true));  solver.addClause(cl);
}

// sum <-> a ^ b ^ cin, carry <-> at least two of the three. `aNeg` reads a
// complemented, which is how the subtractor below gets its ~b.
static void addFullAdder(SATSolver& solver, unsigned a, bool aNeg, unsigned b,
                         unsigned cin, unsigned& sum, unsigned& carry)
{
  sum = freshVar(solver);
  carry = freshVar(solver);
  SATSolver::vec_literals cl;

  for (unsigned row = 0; row < 8; ++row)
  {
    const bool aBit = (row & 1) != 0;
    const bool bBit = (row & 2) != 0;
    const bool cBit = (row & 4) != 0;
    const bool s = aBit ^ bBit ^ cBit;
    const bool co = (aBit + bBit + cBit) >= 2;
    cl.clear();
    cl.push(SATSolver::mkLit(a, aBit != aNeg));
    cl.push(SATSolver::mkLit(b, bBit));
    cl.push(SATSolver::mkLit(cin, cBit));
    cl.push(SATSolver::mkLit(sum, !s));
    solver.addClause(cl);

    cl.clear();
    cl.push(SATSolver::mkLit(a, aBit != aNeg));
    cl.push(SATSolver::mkLit(b, bBit));
    cl.push(SATSolver::mkLit(cin, cBit));
    cl.push(SATSolver::mkLit(carry, !co));
    solver.addClause(cl);
  }
}

// z <-> (x <= y), unsigned, from the least significant bit up so that the most
// significant differing bit decides -- the same chain the comparison lemma
// uses, for the same reason.
static unsigned mkUnsignedLE(SATSolver& solver, const std::vector<unsigned>& x,
                             const std::vector<unsigned>& y, unsigned width)
{
  unsigned acc = pinnedVar(solver, true);
  SATSolver::vec_literals cl;
  for (unsigned bit = 0; bit < width; ++bit)
  {
    const unsigned nc = freshVar(solver);
    const unsigned a = x[bit];
    const unsigned b = y[bit];
    cl.clear(); cl.push(SATSolver::mkLit(a, false)); cl.push(SATSolver::mkLit(b, true));  cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(a, false)); cl.push(SATSolver::mkLit(acc, true)); cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(b, true));  cl.push(SATSolver::mkLit(acc, true)); cl.push(SATSolver::mkLit(nc, false)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(a, true));  cl.push(SATSolver::mkLit(b, false)); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(a, true));  cl.push(SATSolver::mkLit(acc, false)); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);
    cl.clear(); cl.push(SATSolver::mkLit(b, false)); cl.push(SATSolver::mkLit(acc, false)); cl.push(SATSolver::mkLit(nc, true)); solver.addClause(cl);
    acc = nc;
  }
  return acc;
}

// result <-> a * b, truncated, by shift and add: one conditional row per bit
// of b, each added in at its own offset. Rows below the offset are zero, so
// the accumulator keeps those bits and the row's carry starts there.
static void encodeMultiply(SATSolver& solver, const std::vector<unsigned>& a,
                           const std::vector<unsigned>& b,
                           const std::vector<unsigned>& result, unsigned width)
{
  std::vector<unsigned> acc(width);
  for (unsigned j = 0; j < width; ++j)
    acc[j] = mkAnd(solver, a[j], b[0]);

  for (unsigned i = 1; i < width; ++i)
  {
    unsigned carry = pinnedVar(solver, false);
    for (unsigned j = i; j < width; ++j)
    {
      const unsigned pp = mkAnd(solver, a[j - i], b[i]);
      unsigned sum, cout;
      addFullAdder(solver, acc[j], false, pp, carry, sum, cout);
      acc[j] = sum;
      carry = cout;
    }
  }

  for (unsigned j = 0; j < width; ++j)
    addEquiv(solver, result[j], acc[j]);
}

// result <-> a / b or a % b, by restoring division. A zero divisor needs no
// special case: every shifted remainder is at or above it, so each step
// subtracts nothing and the quotient comes out all ones with the dividend left
// in the remainder -- which is what SMT-LIB asks for and what the unabstracted
// BBDivMod produces.
static void encodeDivMod(SATSolver& solver, const std::vector<unsigned>& a,
                         const std::vector<unsigned>& b,
                         const std::vector<unsigned>& result, unsigned width,
                         bool isDiv)
{
  const unsigned zero = pinnedVar(solver, false);
  std::vector<unsigned> quotient(width, zero);
  std::vector<unsigned> rem(width, zero);

  for (int i = (int)width - 1; i >= 0; --i)
  {
    // rem = (rem << 1) | a[i]
    for (unsigned j = width - 1; j > 0; --j)
      rem[j] = rem[j - 1];
    rem[0] = a[i];

    const unsigned geq = mkUnsignedLE(solver, b, rem, width);
    quotient[i] = geq;

    // rem - b, as rem + ~b + 1, kept only where the subtraction was taken.
    unsigned carry = pinnedVar(solver, true);
    std::vector<unsigned> sub(width);
    for (unsigned j = 0; j < width; ++j)
    {
      unsigned s, cout;
      addFullAdder(solver, b[j], true, rem[j], carry, s, cout);
      sub[j] = s;
      carry = cout;
    }
    for (unsigned j = 0; j < width; ++j)
      rem[j] = mkMux(solver, geq, sub[j], rem[j]);
  }

  const std::vector<unsigned>& answer = isDiv ? quotient : rem;
  for (unsigned j = 0; j < width; ++j)
    addEquiv(solver, result[j], answer[j]);
}

unsigned ToSATAIG::refineBVTermInconsistencies(SATSolver& solver)
{
  // Phase 1: Scan all abstractions, reading model values to find inconsistencies.
  // Cache the data needed for clause generation so we don't need modelValue later.
  struct InconsistentCmp {
    size_t absIdx;
    bool swapOps, negateResult, isSigned;
  };
  struct InconsistentPlus {
    size_t absIdx;
  };
  struct InconsistentITE {
    size_t absIdx;
  };
  struct InconsistentDivMul {
    size_t absIdx;
    std::vector<bool> aBits, bBits, expected;
  };

  std::vector<InconsistentCmp> incCmps;
  std::vector<InconsistentPlus> incPlus;
  std::vector<InconsistentITE> incITE;
  std::vector<InconsistentDivMul> incDivMul;

  for (size_t idx = 0; idx < bvTermAbstractions_.size(); ++idx)
  {
    auto& abs = bvTermAbstractions_[idx];
    if (abs.defined)
      continue;

    if (isBVCompare(abs.opKind))
    {
      if (abs.condSATVar == 0) continue;

      std::vector<bool> aBits, bBits;
      if (!getOperandBits(abs.operands[0], abs.width, nodeToSATVar, solver, aBits))
        continue;
      if (!getOperandBits(abs.operands[1], abs.width, nodeToSATVar, solver, bBits))
        continue;

      bool expected = computeBVCompare(abs.opKind, aBits, bBits);
      bool actual = (solver.modelValue(abs.condSATVar) == solver.true_literal());
      if (expected == actual)
        continue;

      // The same three answers computeBVCompare just used, taken from the
      // same place rather than restated here.
      const CompareForm form = comparisonForm(abs.opKind);

      incCmps.push_back({idx, form.swapOps, form.negateResult, form.isSigned});
      continue;
    }

    auto resultIt = nodeToSATVar.find(abs.termNode);
    if (resultIt == nodeToSATVar.end())
      continue;
    const std::vector<unsigned>& resultVars = resultIt->second;

    if (abs.opKind == BVPLUS)
    {
      std::vector<bool> leftBits, rightBits;
      if (!getOperandBits(abs.operands[0], abs.width, nodeToSATVar, solver, leftBits))
        continue;
      if (!getOperandBits(abs.operands[1], abs.width, nodeToSATVar, solver, rightBits))
        continue;

      const bool lNeg = abs.operandNegated[0];
      const bool rNeg = abs.operandNegated[1];
      const bool carryInit = (lNeg != rNeg);

      bool carry = carryInit;
      bool consistent = true;
      for (unsigned bit = 0; bit < abs.width; ++bit)
      {
        bool l = leftBits[bit] ^ lNeg;
        bool r = rightBits[bit] ^ rNeg;
        bool s = (solver.modelValue(resultVars[bit]) == solver.true_literal());
        bool expectedSum = l ^ r ^ carry;
        carry = (l && r) || (l && carry) || (r && carry);
        if (s != expectedSum) { consistent = false; break; }
      }
      if (consistent) continue;

      incPlus.push_back({idx});
    }
    else if (abs.opKind == ITE)
    {
      if (abs.condSATVar == 0) continue;

      bool condVal = (solver.modelValue(abs.condSATVar) == solver.true_literal());
      unsigned branchIdx = condVal ? 1 : 2;
      std::vector<bool> branchBits;
      if (!getOperandBits(abs.operands[branchIdx], abs.width, nodeToSATVar, solver, branchBits))
        continue;

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
      if (!getOperandBits(abs.operands[0], abs.width, nodeToSATVar, solver, aBits))
        continue;
      if (!getOperandBits(abs.operands[1], abs.width, nodeToSATVar, solver, bBits))
        continue;

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

      bool consistent = true;
      for (unsigned bit = 0; bit < W; ++bit)
      {
        bool r = (solver.modelValue(resultVars[bit]) == solver.true_literal());
        if (r != expected[bit]) { consistent = false; break; }
      }
      if (consistent) continue;

      incDivMul.push_back({idx, std::move(aBits), std::move(bBits),
                            std::move(expected)});
    }
  }

  // Phase 2: Add refinement clauses (no model reads needed).
  unsigned refined = 0;

  for (auto& inc : incCmps)
  {
    auto& abs = bvTermAbstractions_[inc.absIdx];
    std::vector<unsigned> leftVars, rightVars;
    if (!getOperandVars(abs.operands[0], abs.width, nodeToSATVar, solver, leftVars))
      continue;
    if (!getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, rightVars))
      continue;
    const std::vector<unsigned>& lv = inc.swapOps ? rightVars : leftVars;
    const std::vector<unsigned>& rv = inc.swapOps ? leftVars : rightVars;

    unsigned carryVar = solver.newVar();
    solver.setFrozen(carryVar);
    {
      SATSolver::vec_literals cl;
      cl.push(SATSolver::mkLit(carryVar, false));
      solver.addClause(cl);
    }

    // From the least significant bit up, so that the most significant
    // *differing* bit is the one that decides. Each step keeps the accumulator
    // when the two bits agree and overrides it when they differ, so whichever
    // bit is visited last among the differing ones settles the answer -- which
    // is the top one only in this direction. Run downwards, as this was, the
    // bottom differing bit won instead, and the chain answered something that
    // is not a comparison at all: it disagreed with `a <= b` on 31616 of the
    // 65536 pairs of eight-bit values. The lemma then pinned the abstraction
    // to that, and a query whose comparison the pinned value contradicted came
    // back unsat.
    //
    // The sign bit is therefore also the last step, which is where flipping
    // its sense belongs: for a signed comparison a leading 1 is the smaller
    // side, so the roles of the two operands invert at that bit alone.
    for (int bit = 0; bit < (int)abs.width; ++bit)
    {
      unsigned a = lv[bit];
      unsigned b = rv[bit];
      bool flipSign = (inc.isSigned && bit == (int)abs.width - 1);

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
    auto& abs = bvTermAbstractions_[inc.absIdx];
    std::vector<unsigned> leftVars, rightVars;
    if (!getOperandVars(abs.operands[0], abs.width, nodeToSATVar, solver, leftVars))
      continue;
    if (!getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, rightVars))
      continue;
    auto resultIt = nodeToSATVar.find(abs.termNode);
    const std::vector<unsigned>& resultVars = resultIt->second;
    const bool lNeg = abs.operandNegated[0];
    const bool rNeg = abs.operandNegated[1];
    const bool carryInit = (lNeg != rNeg);

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
    auto& abs = bvTermAbstractions_[inc.absIdx];
    std::vector<unsigned> thenVars, elseVars;
    if (!getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, thenVars))
      continue;
    if (!getOperandVars(abs.operands[2], abs.width, nodeToSATVar, solver, elseVars))
      continue;
    auto resultIt = nodeToSATVar.find(abs.termNode);
    const std::vector<unsigned>& resultVars = resultIt->second;
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
    auto& abs = bvTermAbstractions_[inc.absIdx];
    std::vector<unsigned> aVars, bVars;
    if (!getOperandVars(abs.operands[0], abs.width, nodeToSATVar, solver, aVars))
      continue;
    if (!getOperandVars(abs.operands[1], abs.width, nodeToSATVar, solver, bVars))
      continue;
    auto resultIt = nodeToSATVar.find(abs.termNode);
    const std::vector<unsigned>& resultVars = resultIt->second;
    unsigned W = abs.width;

    // Once this abstraction has been blocked its allowance of times, stop
    // ruling out operand pairs one at a time and say what the operation is.
    // Everything the encoding needs is already here and already frozen: the
    // operands, through the proxies tied to their real bits or pinned to a
    // constant, and the result, which is the abstraction's own bits. Only a
    // complete mapping can carry it, so an abstraction any of whose bits never
    // reached the CNF keeps enumerating rather than being defined wrongly.
    const unsigned limit = bm->UserFlags.bv_term_abstraction_rounds;
    const bool mapped = usableVars(aVars, W) && usableVars(bVars, W) &&
                        usableVars(resultVars, W);
    if (limit != 0 && abs.blockedRounds >= limit && mapped)
    {
      if (abs.opKind == BVMULT)
        encodeMultiply(solver, aVars, bVars, resultVars, W);
      else
        encodeDivMod(solver, aVars, bVars, resultVars, W,
                     abs.opKind == BVDIV);
      if (bm->UserFlags.stats_flag)
        std::cerr << "BV abstraction: encoding "
                  << _kind_names[abs.opKind] << " exactly after "
                  << abs.blockedRounds << " blocking lemmas" << std::endl;
      abs.defined = true;
      refined++;
      continue;
    }
    abs.blockedRounds++;

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

ToSATAIG::~ToSATAIG()
{
  ClearAllTables();
}
}
