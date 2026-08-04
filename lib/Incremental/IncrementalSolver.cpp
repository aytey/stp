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

#include "stp/Incremental/IncrementalSolver.h"

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/MinisatCore.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BitBlaster.h"
#include "stp/ToSat/ToSATBase.h"

#ifdef USE_CRYPTOMINISAT
#include "stp/Sat/CryptoMinisat5.h"
#endif
#ifdef USE_RISS
#include "stp/Sat/Riss.h"
#endif
#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif

#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace stp
{

namespace
{

// The one retraction mechanism is SAT assumptions, so the backend must
// support them. Plain MiniSat stands in for the ones that cannot: the
// simplifying MiniSat eliminates variables, and a later batch of definitional
// clauses may mention an eliminated variable again, which it cannot cope
// with -- the same reason cvc5 turns SatELite off under incremental solving.
SATSolver* makeBackend(UserDefinedFlags& uf)
{
  SATSolver* s = NULL;
  switch (uf.solver_to_use)
  {
    case UserDefinedFlags::CRYPTOMINISAT5_SOLVER:
#ifdef USE_CRYPTOMINISAT
      s = new CryptoMiniSat5(uf.num_solver_threads);
#endif
      break;
    case UserDefinedFlags::RISS_SOLVER:
#ifdef USE_RISS
      s = new RissCore();
#endif
      break;
    case UserDefinedFlags::CADICAL_SOLVER:
#ifdef USE_CADICAL
      s = new Cadical();
#endif
      break;
    case UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER:
      std::cerr << "Warning: the simplifying MiniSat cannot retract "
                   "assumptions safely; incremental solving uses plain "
                   "MiniSat instead."
                << std::endl;
      break;
    default:
      break;
  }

  if (s != NULL && !s->supportsAssumptions())
  {
    delete s;
    s = NULL;
  }

  if (s == NULL)
    s = new MinisatCore;

  return s;
}

typedef std::unordered_map<ASTNode, int, ASTNode::ASTNodeHasher,
                           ASTNode::ASTNodeEqual>
    NodeToLitMap;
typedef std::unordered_map<ASTNode, bool, ASTNode::ASTNodeHasher,
                           ASTNode::ASTNodeEqual>
    NodeToBoolMap;

// Split a level's conjunction into its top-level conjuncts. The level node
// is rebuilt (and re-simplified) by the node factory on every check-sat, so
// the split set -- not the node -- is the stable notion of the level's
// content.
void splitConjuncts(const ASTNode& n, const ASTNode& trueNode, ASTVec& out)
{
  if (n == trueNode)
    return;
  if (n.GetKind() == AND)
  {
    for (const ASTNode& c : n)
      splitConjuncts(c, trueNode, out);
    return;
  }
  out.push_back(n);
}

// ARRAY_EQ can only exist when the array-equality option is on; this is the
// same complete-DAG barrier walk TopLevelSTPAux performs.
bool containsArrayEquality(const ASTNode& root)
{
  ASTNodeSet visited;
  ASTVec pending(1, root);
  while (!pending.empty())
  {
    const ASTNode node = pending.back();
    pending.pop_back();
    if (!visited.insert(node).second)
      continue;
    if (node.GetKind() == ARRAY_EQ)
      return true;
    for (unsigned i = 0; i < node.Degree(); ++i)
      pending.push_back(node[i]);
  }
  return false;
}

} // namespace

struct IncrementalSolver::Impl
{
  STPMgr* bm;
  AbsRefine_CounterExample* ce;

  std::unique_ptr<SATSolver> solver;

  // The bit-blaster wants a Simplifier; give it an inert one of its own, as
  // ToSATAIG::bitblast does, so no batch-pipeline substitution state can
  // leak into the persistent encoding.
  SubstitutionMap substitutionMap;
  Simplifier simp;
  BBNodeManagerAIG bbMgr;
  BitBlaster bb;

  // AIG object Id -> CNF variable; -1 = not encoded yet. AIG Ids are dense
  // and only ever grow, since the AIG manager lives as long as this object.
  std::vector<int> aigIdToVar;

  // The variable standing for the AIG's constant-1 node, unit-asserted at
  // creation; -1 until first needed.
  int trueVar;

  // conjunct -> root literal (2*var + sign). Permanent: the encoding of a
  // formula is a definition, valid in every context.
  NodeToLitMap rootLitOf;

  // conjunct -> whether the driver's fragment covers it. Permanent: a
  // node-local property.
  NodeToBoolMap supportedCache;

  // Base-level conjuncts already asserted as permanent units.
  ASTNodeSet level0Asserted;

  // Per-call statistics, printed under --stats.
  uint64_t clausesAdded;

  Impl(STPMgr* bm_, AbsRefine_CounterExample* ce_)
      : bm(bm_), ce(ce_), solver(makeBackend(bm_->UserFlags)),
        substitutionMap(bm_), simp(bm_, &substitutionMap),
        bb(&bbMgr, &simp, bm_->defaultNodeFactory, &bm_->UserFlags, NULL),
        trueVar(-1), clausesAdded(0)
  {
  }

  int varOfAig(Aig_Obj_t* regular)
  {
    const unsigned id = Aig_ObjId(regular);
    if (id >= aigIdToVar.size())
      return -1;
    return aigIdToVar[id];
  }

  void setVarOfAig(Aig_Obj_t* regular, int var)
  {
    const unsigned id = Aig_ObjId(regular);
    if (id >= aigIdToVar.size())
      aigIdToVar.resize(id + 1, -1);
    aigIdToVar[id] = var;
  }

  void addClause(SATSolver::vec_literals& c)
  {
    solver->addClause(c);
    clausesAdded++;
  }

  void addBinary(int lit_a, int lit_b)
  {
    SATSolver::vec_literals c;
    c.push(SATSolver::mkLit(lit_a >> 1, lit_a & 1));
    c.push(SATSolver::mkLit(lit_b >> 1, lit_b & 1));
    addClause(c);
  }

  int ensureTrueVar()
  {
    if (trueVar == -1)
    {
      trueVar = solver->newVar();
      SATSolver::vec_literals unit;
      unit.push(SATSolver::mkLit(trueVar, false));
      addClause(unit);
    }
    return trueVar;
  }

  // Tseitin-encode the cone of `regular` (an uncomplemented AIG node) into
  // the solver, allocating variables and definitional clauses for the nodes
  // not encoded yet. Everything emitted is a conservative extension, so it
  // is never retracted.
  void ensureEncoded(Aig_Obj_t* regular)
  {
    std::vector<Aig_Obj_t*> work;
    work.push_back(regular);

    while (!work.empty())
    {
      Aig_Obj_t* r = work.back();
      assert(!Aig_IsComplement(r));

      if (varOfAig(r) != -1)
      {
        work.pop_back();
        continue;
      }

      if (Aig_ObjIsConst1(r))
      {
        setVarOfAig(r, ensureTrueVar());
        work.pop_back();
        continue;
      }

      if (Aig_ObjIsCi(r))
      {
        setVarOfAig(r, solver->newVar());
        work.pop_back();
        continue;
      }

      assert(Aig_ObjIsAnd(r));
      Aig_Obj_t* f0 = Aig_ObjFanin0(r);
      Aig_Obj_t* f1 = Aig_ObjFanin1(r);

      const int v0 = varOfAig(f0);
      const int v1 = varOfAig(f1);
      if (v0 == -1)
      {
        work.push_back(f0);
        continue;
      }
      if (v1 == -1)
      {
        work.push_back(f1);
        continue;
      }

      // v <-> (l0 & l1)
      const int v = solver->newVar();
      const int l0 = 2 * v0 + (Aig_ObjFaninC0(r) ? 1 : 0);
      const int l1 = 2 * v1 + (Aig_ObjFaninC1(r) ? 1 : 0);

      addBinary(2 * v + 1, l0);
      addBinary(2 * v + 1, l1);

      SATSolver::vec_literals c;
      c.push(SATSolver::mkLit(v, false));
      c.push(SATSolver::mkLit(l0 >> 1, !(l0 & 1)));
      c.push(SATSolver::mkLit(l1 >> 1, !(l1 & 1)));
      addClause(c);

      setVarOfAig(r, v);
      work.pop_back();
    }
  }

  // Bit-blast a conjunct (once, memoised across the session by the
  // persistent BitBlaster) and encode its circuit; the returned literal
  // asserts it.
  int rootLit(const ASTNode& conjunct)
  {
    NodeToLitMap::const_iterator it = rootLitOf.find(conjunct);
    if (it != rootLitOf.end())
      return it->second;

    bm->GetRunTimes()->start(RunTimes::BitBlasting);
    BBNodeAIG root = bb.BBForm(conjunct);
    bm->GetRunTimes()->stop(RunTimes::BitBlasting);

    bm->GetRunTimes()->start(RunTimes::CNFConversion);
    Aig_Obj_t* regular = Aig_Regular(root.n);
    ensureEncoded(regular);
    const int lit =
        2 * varOfAig(regular) + (Aig_IsComplement(root.n) ? 1 : 0);
    bm->GetRunTimes()->stop(RunTimes::CNFConversion);

    rootLitOf[conjunct] = lit;
    return lit;
  }

  bool supported(const ASTNode& n)
  {
    NodeToBoolMap::const_iterator it = supportedCache.find(n);
    if (it != supportedCache.end())
      return it->second;

    bool ok = !containsArrayOps(n, bm);
    if (ok && bm->has_floating_point_theory)
      ok = !containsFloatingPointTheory(n, bm);
    if (ok && bm->UserFlags.enable_array_equality)
      ok = !containsArrayEquality(n);

    supportedCache[n] = ok;
    return ok;
  }

  // Values for every symbol the persistent encoding knows about. Symbols
  // from popped scopes are included -- their SAT variables are merely
  // unconstrained -- and are harmless: the model printers iterate the
  // currently declared symbols, not this map.
  void buildSymbolMap(ToSATBase::ASTNodeToSATVar& out)
  {
    for (BBNodeManagerAIG::SymbolToBBNode::const_iterator it =
             bbMgr.symbolToBBNode.begin();
         it != bbMgr.symbolToBBNode.end(); ++it)
    {
      const vector<BBNodeAIG>& bits = it->second;
      vector<unsigned> vars(bits.size(), ~((unsigned)0));
      for (size_t i = 0; i < bits.size(); i++)
      {
        if (bits[i].IsNull())
          continue;
        const int v = varOfAig(Aig_Regular(bits[i].n));
        if (v != -1)
          vars[i] = (unsigned)v;
      }
      out.insert(std::make_pair(it->first, vars));
    }
  }
};

IncrementalSolver::IncrementalSolver(STPMgr* bm, AbsRefine_CounterExample* ce)
    : impl(new Impl(bm, ce))
{
}

IncrementalSolver::~IncrementalSolver() {}

bool IncrementalSolver::canHandle(const ASTVec& assertionsSMT2)
{
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    if (!impl->supported(levelConjunction))
      return false;
  }
  return true;
}

SOLVER_RETURN_TYPE IncrementalSolver::checkSat(const ASTVec& assertionsSMT2)
{
  STPMgr* bm = impl->bm;
  UserDefinedFlags& uf = bm->UserFlags;

  assert(!assertionsSMT2.empty());

  const uint64_t clausesBefore = impl->clausesAdded;
  uint64_t newConjuncts = 0;

  // Base level: every conjunct becomes a permanent unit clause, once. The
  // base level only grows (reset destroys this object), so this is monotone
  // and sound even though the level's conjunction node is re-collapsed --
  // and possibly re-simplified -- on every call.
  ASTVec conjuncts;
  splitConjuncts(assertionsSMT2[0], bm->ASTTrue, conjuncts);
  for (const ASTNode& c : conjuncts)
  {
    if (!impl->level0Asserted.insert(c).second)
      continue;
    newConjuncts++;
    const int lit = impl->rootLit(c);
    SATSolver::vec_literals unit;
    unit.push(SATSolver::mkLit(lit >> 1, lit & 1));
    impl->addClause(unit);
  }

  // Pushed levels: encode (against the permanent caches) and assume. The
  // assumption set is recomputed from the current stack on every call, so
  // popped levels vanish by simply no longer being here.
  SATSolver::vec_literals assumptions;
  for (size_t level = 1; level < assertionsSMT2.size(); level++)
  {
    conjuncts.clear();
    splitConjuncts(assertionsSMT2[level], bm->ASTTrue, conjuncts);
    for (const ASTNode& c : conjuncts)
    {
      if (impl->rootLitOf.find(c) == impl->rootLitOf.end())
        newConjuncts++;
      const int lit = impl->rootLit(c);
      assumptions.push(SATSolver::mkLit(lit >> 1, lit & 1));
    }
  }

  if (uf.stats_flag)
  {
    std::cerr << "Incremental: encoded " << newConjuncts
              << " new conjuncts, added "
              << (impl->clausesAdded - clausesBefore) << " clauses, assumed "
              << assumptions.size() << " literals, solver has "
              << impl->solver->nVars() << " variables" << std::endl;
  }

  // The counterexample decision the batch pipeline makes per query
  // (TopLevelSTPAux), minus the array cases this driver never sees.
  bool construct =
      uf.check_counterexample_flag || uf.print_counterexample_flag;
#ifndef NDEBUG
  construct = true;
#endif
  uf.construct_counterexample_flag = construct;

  // Budgets are per check-sat, as solve_by_sat_solver arms them per query.
  if (uf.timeout_max_conflicts >= 0)
    impl->solver->setMaxConflicts(uf.timeout_max_conflicts);
  if (uf.timeout_max_time >= 0)
    impl->solver->setMaxTime(uf.timeout_max_time);
  bm->soft_timeout_expired = false;

  bm->GetRunTimes()->start(RunTimes::Solving);
  bool sat;
  if (assumptions.size() == 0)
    sat = impl->solver->solve(bm->soft_timeout_expired);
  else
    sat = impl->solver->solveWithAssumptions(assumptions,
                                             bm->soft_timeout_expired);
  bm->GetRunTimes()->stop(RunTimes::Solving);

  if (uf.stats_flag)
    impl->solver->printStats();

  if (bm->soft_timeout_expired)
    return SOLVER_TIMEOUT;

  if (!sat)
    return SOLVER_UNSATISFIABLE;

  if (construct)
  {
    bm->GetRunTimes()->start(RunTimes::CounterExampleGeneration);
    impl->ce->ClearCounterExampleMap();
    impl->ce->ClearComputeFormulaMap();

    ToSATBase::ASTNodeToSATVar symbolMap;
    impl->buildSymbolMap(symbolMap);
    impl->ce->ConstructCounterExample(*impl->solver, symbolMap);
    bm->GetRunTimes()->stop(RunTimes::CounterExampleGeneration);

    if (uf.check_counterexample_flag)
    {
      // GetCounterExample answers ASTUndefined while ValidFlag claims the
      // last query was unsat; that flag describes the previous query at
      // this point, so clear it before evaluating.
      bm->ValidFlag = false;
      for (const ASTNode& levelConjunction : assertionsSMT2)
      {
        conjuncts.clear();
        splitConjuncts(levelConjunction, bm->ASTTrue, conjuncts);
        for (const ASTNode& c : conjuncts)
        {
          if (impl->ce->GetCounterExample(c) != bm->ASTTrue)
            FatalError("IncrementalSolver: the model does not satisfy an "
                       "asserted formula",
                       c);
        }
      }
    }
  }

  return SOLVER_SATISFIABLE;
}

} // namespace stp
