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
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/FloatBlaster/FpEncodingContext.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/MinisatCore.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/Incremental/IncrementalCBP.h"
#include "stp/Simplifier/RemoveUnconstrained.h"
#include "stp/Simplifier/PropagateEqualities.h"
#include "stp/Simplifier/BVSolver.h"
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

#include <algorithm>
#include <exception>
#include <functional>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#if defined(_WIN32)
#include <windows.h>
#else
#include <pthread.h>
#endif

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

// What the driver knows about a conjunct's content: whether it contains
// array operations (which decide the refinement machinery), whether it
// touches the floating-point theory (which decides totalisation and
// lowering), and whether it carries an opaque whole-array equality (which
// routes the entire check-sat through the extensionality block). All
// node-local, permanent properties.
struct Fragment
{
  bool arrays;
  bool fp;
  bool arrayEq;
};
typedef std::unordered_map<ASTNode, Fragment, ASTNode::ASTNodeHasher,
                           ASTNode::ASTNodeEqual>
    NodeToFragmentMap;

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
  Simplifier* batchSimp;
  ArrayTransformer* batchAT;

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

  // conjunct -> fragment facts. Permanent: node-local properties.
  NodeToFragmentMap fragmentCache;

  // The read registry, persistent across check-sats: array -> index ->
  // ArrayRead, exactly the batch ArrayTransformer's table. The transformer
  // consults it before minting an abstraction variable, so seeding it from
  // here before every transform gives one canonical read symbol per
  // (array, index) for the whole session -- which is what makes refinement
  // axioms (congruence over those symbols) permanently valid clauses.
  // Entries from popped scopes stay: their axioms are tautologies of the
  // abstraction, so clauses already learned over them remain valid. They
  // are NOT harmless everywhere, though -- their defining equations were
  // encoded under root literals that are no longer assumed, so their SAT
  // variables float, and seedActiveReads below must keep them out of the
  // per-solve batch tables.
  ArrayTransformer::ArrType myReads;

  // The (array, index) reads each ENCODING contains, keyed exactly as
  // rootLitOf is -- the raw conjunct on the ordinary path, the rewritten
  // node on the pushed-definitions path -- so per-solve batch tables can
  // be restricted to the reads of the encodings actually assumed this
  // round. (Keying by the raw conjunct would go quietly wrong under
  // pushed definitions: different conjuncts, or one conjunct under
  // different rounds' definitions, can share one rewritten-node entry
  // whose encode never re-runs, and a rewrite that touches an index
  // expression mints a different registry row for the same syntactic
  // read.) Reads of popped encodings have unconstrained anchor/value SAT
  // variables -- their defining equations are guarded by root literals no
  // longer assumed -- and one such row in the counterexample tables
  // shadows an active cell with a floating value, makes the checker
  // reject every candidate, and refinement cannot converge.
  std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>> readsOfEncoded;

  // Under --ackermanize, the transformer's other table: the reads of each
  // array in the order they were seen, from which each NEW read's nested
  // if-then-else over the EXISTING reads is built. That new-versus-existing
  // shape is exactly monotone, so persisting the list keeps pair coverage
  // across check-sats: any two reads are related by whichever was encoded
  // later. A popped read's entry stays as an unconstrained observation of
  // the array -- sound, since an array maps every index to some value.
  std::map<ASTNode, vector<std::pair<ASTNode, ASTNode>>> myAckPairs;

  // Storage handed out by the ToSATBase adapter (the refinement machinery
  // asks for the symbol map by reference), and the adapter itself,
  // constructed on first array use (its class is defined below Impl).
  ToSATBase::ASTNodeToSATVar symbolMapStorage;
  std::unique_ptr<ToSATBase> adapter;

  // Created on first floating-point use; see fpContext().
  std::unique_ptr<FpEncodingContext> fpCtx;

  // Nodes the block cache's determinism depends on. STP garbage-collects
  // unreferenced interior nodes and re-mints their numbers, and the
  // deterministic generated names are keyed on node numbers -- so every
  // stage of a round's spine (raw conjunction, prepared, lowered) is
  // pinned here. Without this, an identical re-pushed stack rebuilds the
  // freed spine under fresh numbers and the whole chain diverges.
  // (The per-conjunct caches never had the problem: their keys hold their
  // nodes by construction.)
  ASTNodeSet extKeepAlive;

  // Base-level conjuncts already asserted as permanent units.
  ASTNodeSet level0Asserted;

  // Substitutions harvested from base-level equations: x -> t for a
  // base-level conjunct (= x t), plus TRUE/FALSE for unit boolean
  // conjuncts. The base level only grows, so this map is monotone and
  // needs no backtracking; and the defining equation is ALWAYS kept
  // asserted, never eliminated, so using an entry to rewrite any conjunct
  // -- at any level, popped and re-pushed or not -- is sound, and no model
  // reconstruction is ever needed. (This is deliberately weaker than
  // variable elimination: completeness is traded for having no leveled
  // state at all.)
  //
  // SubstitutionMap::replace expands entries through each other as it runs
  // ((x -> y) plus (y -> 5) becomes (x -> 5), mutating the map); every
  // rewritten entry is still a permanent truth, so that canonicalisation
  // is welcome. It is also why rewrite caches are per use, never shared
  // across calls: a cache entry can predate an expansion.
  ASTNodeMap sigma0;

  // Defining equations that must reach the solver as real constraints.
  // A variable whose bits were already encoded in an EARLIER check-sat is
  // frozen (z3's rule: a symbol the backend has seen must not be
  // eliminated): its defining equation would otherwise rewrite itself to
  // TRUE under its own entry, and the existing SAT variables would lose
  // the constraint -- sat where unsat lies that way. Such an equation is
  // encoded un-rewritten; the sigma0 entry still simplifies everything
  // encoded afterwards, which is sound exactly because the equation is
  // asserted.
  ASTNodeSet mustKeepRaw;

  // One activation literal per distinct set of root literals a pushed
  // level has ever solved with. Assuming the activation literal asserts
  // exactly those roots through persistent implications, shrinking the
  // assumption set from one literal per conjunct to one per level. The
  // key is the sorted root vector itself -- not the level's formula --
  // because under pushed-level definitions the same formula can encode to
  // different roots in different rounds; identical roots are the only
  // thing that makes reusing the implications sound.
  std::map<std::vector<int>, int> actLitOf;

  // Every literal that ever carried a level (or an extensionality block)
  // as an assumption. The ones not assumed by the current call are
  // retracted content, and hintRetractedLevels steers the decision
  // heuristic away from them.
  std::unordered_set<int> everAssumedLits;

  // Per-call bookkeeping for unsat answers: which level each assumed
  // literal carried, and -- when the caller asked for the last level to be
  // assumed one conjunct at a time (check-sat-assuming wants per-assumption
  // failure granularity) -- which conjunct each of its literals stands
  // for. Consumed by the unsat-assumption accessors; rebuilt every call.
  std::vector<std::pair<int, size_t>> assumedLitLevels;
  std::vector<std::pair<int, ASTNode>> lastLevelLitConjuncts;
  bool lastUnsat;
  bool lastUnsatCoarse;     // ext rounds: one block literal, no granularity
  bool lastLevelIndividual; // the per-conjunct mode actually ran

  // A sat answer whose counterexample nobody has read yet; see
  // materializePendingModel. Cleared at the top of every solve.
  bool modelPending;

  // Trail reuse is a size gamble: on sessions of many small queries the
  // saved per-solve re-descent dominates (the issue #483 KLEE files, 36%
  // and 19% faster at ~11k variables), while on large instances the kept
  // trail suppresses the fresh restarts the search needs (the
  // phase-sensitive QF_ABVFP families: up to 13x slower at ~185k
  // variables, with identical refinement behaviour -- the search itself
  // degrades). The backend accepts the option only in its configuration
  // window, so crossing the boundary retires it for the session by
  // starting the solver over without it; the boundary is measured, not
  // principled.
  bool trailReuseAllowed;
  static const unsigned long trailReuseVarLimit = 100000;
  std::vector<int> lastFailedLits;
  size_t lastLevelCount;

  void recordUnsat(const SATSolver::vec_literals& assumptions,
                   size_t levelCount, bool coarse)
  {
    lastUnsat = true;
    lastUnsatCoarse = coarse;
    lastLevelCount = levelCount;
    if (!coarse)
      solver->unsatAssumptions(assumptions, lastFailedLits);
  }

  // Whether the bounded-variable-addition decision has been taken for the
  // current backend instance. rebuildEncodings resets it: the fresh solver
  // reopens the configuration window. The warning latch is per session --
  // a rebuild does not deserve a repeat of the warning.
  bool bvaDecided;
  bool bvaWarned;

  // ── Speculative simplification pipeline ───────────────────────────
  //
  // Per-call aggressive CBP: uses addConstraintsAggressive (sets each
  // conjunct to TRUE) to discover speculative constants. Results are
  // valid ~99.96% of the time.
  //
  // After SAT, the model is validated against the pre-simplified
  // conjuncts. If any are violated, those conjuncts are re-encoded
  // without speculation and the solver re-runs.
  std::unique_ptr<IncrementalCBP> callCBP;

  // key → pre-simplified lowered form for speculatively-simplified
  // conjuncts. Used for SAT validation.
  std::map<ASTNode, ASTNode> speculativeOriginals;
  bool speculativeThisCall;
  bool speculationDisabled;  // set after validation failure to prevent retry

  // Validate a SAT model against the full assertion stack.
  // Returns true if the model satisfies all assertions; false if any
  // are violated.
  bool validateModel(const ASTVec& assertionsSMT2)
  {
    if (!speculativeThisCall)
      return true;

    // Check every level's assertions against the model.
    for (const ASTNode& levelConj : assertionsSMT2)
    {
      if (levelConj == bm->ASTTrue)
        continue;
      ASTNode val = ce->ComputeFormulaUsingModel(levelConj);
      if (val != bm->ASTTrue)
        return false;
    }
    return true;
  }

  // Per-call statistics, printed under --stats.
  uint64_t clausesAdded;
  uint64_t encodesThisCall;

  Impl(STPMgr* bm_, AbsRefine_CounterExample* ce_, Simplifier* batchSimp_,
       ArrayTransformer* batchAT_)
      : bm(bm_), ce(ce_), batchSimp(batchSimp_), batchAT(batchAT_),
        solver(makeBackend(bm_->UserFlags)), substitutionMap(bm_),
        simp(bm_, &substitutionMap),
        bb(&bbMgr, &simp, bm_->defaultNodeFactory, &bm_->UserFlags, NULL),
        trueVar(-1), bvaDecided(false), bvaWarned(false),
        batchTablesSeeded(false), lastUnsat(false), lastUnsatCoarse(false),
        lastLevelIndividual(false), modelPending(false),
        trailReuseAllowed(true), lastLevelCount(0),
        speculativeThisCall(false), speculationDisabled(false),
        clausesAdded(0), encodesThisCall(0)
  {
    // Refinement adds clauses between solve calls; tell backends that need
    // to know (CryptoMiniSat skips its startup simplification).
    solver->enableRefinement(true);

    // The driver's assumption order is prefix-stable across calls --
    // assumptions are emitted in assertion stack order, and push/pop only
    // ever change the suffix -- which is exactly what lets a backend keep
    // the shared trail between solves instead of re-descending from the
    // root every call. Size-gated: see trailReuseAllowed.
    if (trailReuseAllowed)
      solver->enableTrailReuse();
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

  // Harvest a base-level substitution from a conjunct, if it defines one.
  // The conjunct itself is still encoded and asserted regardless, which is
  // what makes every use of the entry sound forever.
  // Recognise a defining conjunct: SYMBOL / (not SYMBOL) as a boolean unit,
  // or an equation with a symbol on one side. FALSE when the conjunct
  // defines nothing usable; the guards are shared by both harvests.
  bool recogniseDefinition(const ASTNode& c, ASTNode& var, ASTNode& term)
  {
    if (c.GetKind() == SYMBOL)
    {
      var = c;
      term = bm->ASTTrue;
    }
    else if (c.GetKind() == NOT && c[0].GetKind() == SYMBOL)
    {
      var = c[0];
      term = bm->ASTFalse;
    }
    else if ((c.GetKind() == EQ || c.GetKind() == IFF) && c.Degree() == 2)
    {
      if (c[0].GetKind() == SYMBOL)
      {
        var = c[0];
        term = c[1];
      }
      else if (c[1].GetKind() == SYMBOL)
      {
        var = c[1];
        term = c[0];
      }
      else
        return false;
    }
    else
      return false;

    if (var == term)
      return false;

    // Only plain bit-vector/boolean definitions. An array-typed symbol is
    // not a substitutable value; and the replacement must not smuggle
    // theory content -- floating point, array reads, opaque equalities --
    // into conjuncts whose lowering and transform decisions (raw-conjunct
    // properties) were already made without it.
    if (var.GetIndexWidth() != 0)
      return false;
    if (bm->has_floating_point_theory && containsFloatingPointTheory(term, bm))
      return false;
    if (containsArrayOps(term, bm))
      return false;
    if (bm->UserFlags.enable_array_equality && containsArrayEquality(term))
      return false;
    if (term.GetKind() != TRUE && term.GetKind() != FALSE &&
        bm->VarSeenInTerm(var, term))
      return false;

    return true;
  }

  void harvestSigma0(const ASTNode& c)
  {
    ASTNode var, term;
    if (!recogniseDefinition(c, var, term))
      return;
    if (sigma0.find(var) != sigma0.end())
      return;

    // Expand the replacement through what is already known, once. Chains
    // that stay partially expanded are fine: every equation remains
    // asserted, so partial rewriting is merely less simplification.
    ASTNodeMap cache;
    ASTNode expanded = SubstitutionMap::replace(term, sigma0, cache,
                                                bm->defaultNodeFactory);

    // recogniseDefinition occurs-checked the RAW replacement; expansion
    // can smuggle the variable back in (m = a is innocent until a = f(m)
    // is already known, when it expands to m = f(m)). A self-referential
    // entry makes replace() recurse forever, so it is refused -- the
    // equation is still asserted, so refusing only costs rewriting. With
    // every stored entry expanded and occurs-free at insertion, an
    // entry's replacement can only mention variables that were undefined
    // when it was stored, so no chain of entries can loop.
    if (expanded.GetKind() != TRUE && expanded.GetKind() != FALSE &&
        bm->VarSeenInTerm(var, expanded))
      return;

    // Frozen: the variable's bits already live in the solver, so this
    // equation must constrain them for real (see mustKeepRaw).
    if (bbMgr.symbolToBBNode.find(var) != bbMgr.symbolToBBNode.end())
      mustKeepRaw.insert(c);

    sigma0[var] = expanded;
  }

  // A definition found at a PUSHED level. It holds only while its level is
  // live, so nothing about it may persist: entries go into a per-call map,
  // the defining conjunct is remembered so it is never rewritten under its
  // own entry (it stays assumed, which is what makes using the entry
  // sound), and the rewritten conjuncts are cached by their REWRITTEN node
  // -- a formula-level key, valid whenever the same rewrite recurs, and
  // simply not reached in rounds where the definition is gone.
  void harvestPushed(const ASTNode& c, ASTNodeMap& sigmaP,
                     ASTNodeSet& sources)
  {
    ASTNode var, term;
    if (!recogniseDefinition(c, var, term))
      return;
    if (sigma0.find(var) != sigma0.end())
      return;
    if (sigmaP.find(var) != sigmaP.end())
      return;

    // Same discipline as harvestSigma0, against the map this entry will
    // actually be used in: the caller replaces under sigma0 MERGED with
    // sigmaP, so the replacement is expanded under both (sigma0 first --
    // sigmaP replacements are already sigma0-expanded, so one pass each
    // suffices) and refused if its own variable reappears. A pushed
    // m = a against a base a = f(m) is exactly the moo.smt2 cycle split
    // across levels.
    ASTNodeMap cache0, cacheP;
    ASTNode expanded = SubstitutionMap::replace(term, sigma0, cache0,
                                                bm->defaultNodeFactory);
    expanded = SubstitutionMap::replace(expanded, sigmaP, cacheP,
                                        bm->defaultNodeFactory);
    if (expanded.GetKind() != TRUE && expanded.GetKind() != FALSE &&
        bm->VarSeenInTerm(var, expanded))
      return;

    sigmaP[var] = expanded;
    sources.insert(c);
  }

  // Assertion-local, equivalence-preserving simplification, with a fresh
  // Simplifier so no cross-assertion state can exist: its substitution
  // map is empty, so everything it does to this one conjunct is a plain
  // equivalence. Measurably worth it on multi-round workloads; sharing a
  // Simplifier across conjuncts measured slower, so this stays per call.
  ASTNode simplifyAlone(const ASTNode& n)
  {
    SubstitutionMap localSm(bm);
    Simplifier localSimp(bm, &localSm);
    return localSimp.SimplifyFormula_TopLevel(n, false);
  }

  // What actually gets encoded for a conjunct: the conjunct rewritten under
  // the base-level substitutions and then simplified on its own. Keyed by
  // the ORIGINAL conjunct in rootLitOf, so reuse is untouched; encoding
  // under an older, smaller sigma0 stays sound because sigma0 entries are
  // permanent truths.
  ASTNode prepareConjunct(const ASTNode& c)
  {
    if (!bm->UserFlags.optimize_flag)
      return c;

    ASTNode out = c;
    if (!sigma0.empty() && mustKeepRaw.find(c) == mustKeepRaw.end())
    {
      // replace() rebuilds every touched node through the (simplifying)
      // node factory, so the node-local rewrite rules already run over the
      // substituted result as it is built.
      ASTNodeMap cache;
      out = SubstitutionMap::replace(out, sigma0, cache,
                                     bm->defaultNodeFactory);
    }

    return simplifyAlone(out);
  }

  // Lower, transform and bit-blast a fully rewritten word-level formula
  // into the persistent solver, returning its root literal. Everything
  // emitted is a conservative extension; every actual encode is counted
  // for the per-call statistics. `key` is the node this encoding is cached
  // under in rootLitOf -- the raw conjunct on the ordinary path, the
  // rewritten node on the pushed-definitions path -- and the registry rows
  // the transform visits are recorded under the same key, so a later cache
  // hit finds its rows by the node it hit with.
  int encodePrepared(const ASTNode& key, ASTNode toEncode,
                     const Fragment& frag)
  {
    if (frag.fp)
    {
      toEncode = fpContext()->lowerPrepared(toEncode);

      // ── Speculative simplification pipeline ───────────────────────
      // Run aggressive CBP (tier 1: set each conjunct to TRUE) plus
      // the full batch cascade (tier 2: PropagateEqualities,
      // RemoveUnconstrained, BVSolver) on the lowered form.
      //
      // These simplifications are speculative: they assume this
      // conjunct holds, which is valid iff the formula is SAT. If the
      // formula is actually UNSAT, the aggressive simplification may
      // weaken the formula and produce a spurious SAT — caught by
      // model validation after the solve.
      // Speculative simplification runs only when speculation is
      // enabled AND the conjunct is NOT a base-level permanent unit.
      // Base-level encodings are permanent and must be conservative;
      // pushed-level encodings are retractable via assumptions, so
      // aggressive constants that turn out wrong get caught by
      // validation and the encoding is rebuilt.
      const bool canSpeculate = bm->UserFlags.optimize_flag &&
                                !speculationDisabled &&
                                !level0Asserted.count(key);
      if (canSpeculate)
      {
        ASTNode preLowered = toEncode;  // save for validation

        // Tier 1: aggressive cross-conjunct CBP.
        if (bm->UserFlags.bitConstantProp_flag)
        {
          if (!callCBP)
            callCBP.reset(new IncrementalCBP(bm, bm->defaultNodeFactory));
          callCBP->addConstraintsAggressive(toEncode);

          ASTNodeMap fixed = callCBP->getAllFixed();
          if (!fixed.empty())
          {
            ASTNodeMap cache;
            toEncode = SubstitutionMap::replace(toEncode, fixed, cache,
                                                bm->defaultNodeFactory);
          }
        }

        // Tier 2: full batch simplification cascade.
        {
          SubstitutionMap localSm(bm);
          Simplifier localSimp(bm, &localSm);

          toEncode = localSimp.SimplifyFormula_TopLevel(toEncode, false);

          if (bm->UserFlags.propagate_equalities)
          {
            PropagateEqualities pe(&localSimp, bm->defaultNodeFactory, bm);
            toEncode = pe.topLevel(toEncode);
          }

          if (bm->UserFlags.enable_unconstrained)
          {
            RemoveUnconstrained ruc(*bm);
            toEncode = ruc.topLevel(toEncode, &localSimp);
          }

          if (bm->UserFlags.wordlevel_solve_flag)
          {
            BVSolver bvs(bm, &localSimp);
            toEncode = bvs.TopLevelBVSolve(toEncode, false);
          }

          toEncode = localSimp.applySubstitutionMapAtTopLevel(toEncode);
        }

        // Record the RAW conjunct (pre-lowered, pre-prepared) for
        // validation. Validating against the lowered form misses bugs
        // in the lowering step itself; the raw conjunct is the source
        // of truth.
        if (!(toEncode == preLowered))
        {
          speculativeOriginals[key] = key;  // validate against original
          speculativeThisCall = true;
        }
      }
    }

    if (frag.arrays)
    {
      batchAT->arrayToIndexToRead = myReads;
      batchAT->ack_pair = myAckPairs;
      batchAT->recordTouchedReads = true;
      batchAT->touchedReads.clear();
      toEncode = batchAT->TransformFormula_TopLevel(toEncode);
      batchAT->recordTouchedReads = false;
      readsOfEncoded[key] = batchAT->touchedReads;
      myReads = batchAT->arrayToIndexToRead;
      myAckPairs = batchAT->ack_pair;
      batchTablesSeeded = false;
      assert(!containsArrayOps(toEncode, bm));
      totalizeRegistrySymbols();
    }

    // Skip encoding if simplification resolved the conjunct.
    if (toEncode == bm->ASTTrue)
      return 2 * ensureTrueVar();
    if (toEncode == bm->ASTFalse)
      return 2 * ensureTrueVar() + 1;

    bm->GetRunTimes()->start(RunTimes::BitBlasting);
    BBNodeAIG root = bb.BBForm(toEncode);
    bm->GetRunTimes()->stop(RunTimes::BitBlasting);

    bm->GetRunTimes()->start(RunTimes::CNFConversion);
    Aig_Obj_t* regular = Aig_Regular(root.n);
    ensureEncoded(regular);
    const int lit =
        2 * varOfAig(regular) + (Aig_IsComplement(root.n) ? 1 : 0);
    bm->GetRunTimes()->stop(RunTimes::CNFConversion);

    encodesThisCall++;
    return lit;
  }

  // Bit-blast a conjunct (once, memoised across the session by the
  // persistent BitBlaster) and encode its circuit; the returned literal
  // asserts it. Array reads are abstracted through the seeded registry
  // first, so the encoded form is pure bit-vector and the abstraction
  // variables are canonical for the session.
  int rootLit(const ASTNode& conjunct)
  {
    NodeToLitMap::const_iterator it = rootLitOf.find(conjunct);
    if (it != rootLitOf.end())
      return it->second;

    const Fragment& frag = fragment(conjunct);

    ASTNode toEncode = conjunct;

    // Totalise partial floating-point operations and pin rounding modes
    // before the formula is used for anything, as the batch pipeline does;
    // the word-level rewriting runs on the totalised form, and lowering to
    // the packed circuit comes after it.
    if (frag.fp)
      toEncode = fpContext()->prepare(toEncode);

    toEncode = prepareConjunct(toEncode);

    const int lit = encodePrepared(conjunct, toEncode, frag);
    rootLitOf[conjunct] = lit;
    return lit;
  }

  // As rootLit, but under this round's pushed-level definitions as well.
  // The rewritten form is only equivalent to the conjunct together with
  // the defining equations, which are live conjuncts assumed alongside it
  // -- so the encoding is cached by the REWRITTEN node: a round where a
  // definition is gone rewrites differently and simply never reaches the
  // stale entry. Defining conjuncts themselves, and base definitions kept
  // raw by the freeze rule, take the ordinary path; so does any conjunct
  // the round's definitions do not touch, sharing its raw-keyed entry.
  // `encodedAs` reports the node the returned literal is cached under --
  // the conjunct itself or the rewritten node -- which is also the key the
  // encoding's registry rows are recorded by, so the caller can seed the
  // refinement tables for what was actually assumed.
  int rootLitUnder(const ASTNode& conjunct, ASTNodeMap& merged,
                   const ASTNodeSet& sources, ASTNode& encodedAs)
  {
    encodedAs = conjunct;
    if (!bm->UserFlags.optimize_flag ||
        sources.find(conjunct) != sources.end() ||
        mustKeepRaw.find(conjunct) != mustKeepRaw.end())
      return rootLit(conjunct);

    const Fragment& frag = fragment(conjunct);

    ASTNode pre = conjunct;
    if (frag.fp)
      pre = fpContext()->prepare(pre);

    ASTNodeMap cache;
    ASTNode rewritten =
        SubstitutionMap::replace(pre, merged, cache, bm->defaultNodeFactory);
    if (rewritten == pre)
      return rootLit(conjunct);

    ASTNode w = simplifyAlone(rewritten);
    encodedAs = w;

    NodeToLitMap::const_iterator it = rootLitOf.find(w);
    if (it != rootLitOf.end())
      return it->second;

    const int lit = encodePrepared(w, w, frag);
    rootLitOf[w] = lit;
    return lit;
  }

  const Fragment& fragment(const ASTNode& n)
  {
    NodeToFragmentMap::const_iterator it = fragmentCache.find(n);
    if (it != fragmentCache.end())
      return it->second;

    Fragment f;
    f.fp =
        bm->has_floating_point_theory && containsFloatingPointTheory(n, bm);
    f.arrayEq =
        bm->UserFlags.enable_array_equality && containsArrayEquality(n);

    // Arrayness must be judged on the form that will be encoded: totalising
    // a partial floating-point operation (fp.to_ubv of a NaN, say) can
    // introduce reads of an unspecified-value array into a conjunct that
    // had no arrays at all. Judged on the raw conjunct, the introduced READ
    // reached the bit-blaster, and the refinement loop -- which is what
    // enforces congruence between unspecified results at equal indices --
    // was skipped. prepare() is memoised in the session-long context, so
    // rootLit's later call is a cache hit, not repeated work.
    ASTNode basis = n;
    if (f.fp)
      basis = fpContext()->prepare(n);
    f.arrays = containsArrayOps(basis, bm);

    return fragmentCache.insert(std::make_pair(n, f)).first->second;
  }

  SOLVER_RETURN_TYPE extCheckSat(const ASTVec& assertionsSMT2);
  ToSATBase* ensureAdapter();

  // The session-long floating-point encoding context. Its totalisation
  // re-conjoins every side condition (rounding-mode pinning in particular)
  // onto each call's own result -- by design, precisely so the guarantee
  // is independent of the assertion stack -- so per-conjunct preparation
  // over one persistent context is self-contained: a conjunct's lowered
  // form carries its own conditions and retracts with it.
  FpEncodingContext* fpContext()
  {
    if (!fpCtx)
      fpCtx.reset(new FpEncodingContext(bm));
    return fpCtx.get();
  }

  // Give every bit of a symbol a CNF variable, allocating unconstrained
  // ones where the encoded cones never needed the bit. The refinement
  // machinery encodes congruence axioms straight over the bit variables of
  // the registry's symbols (getEquals), with no notion of "this bit never
  // reached the solver" -- and an unconstrained fresh variable is exactly
  // the meaning the blasted formula gives an unused bit, the same argument
  // ToSATAIG makes for lemma-only extensionality symbols.
  void totalizeSymbol(const ASTNode& s)
  {
    // Eager-Ackermann registry rows carry no index symbol at all.
    if (s.IsNull() || s.GetKind() != SYMBOL)
      return;
    const unsigned width = std::max((unsigned)1, s.GetValueWidth());
    for (unsigned i = 0; i < width; i++)
    {
      BBNodeAIG bit = bbMgr.CreateSymbol(s, i);
      ensureEncoded(Aig_Regular(bit.n));
    }
  }

  // What the last refinement-driven check-sat seeded into the batch-side
  // read table; kept for seededReadsForTesting().
  std::vector<std::pair<ASTNode, ASTNode>> lastSeededReads;

  // Whether the batch-side tables still hold exactly what seedActiveReads
  // last put there, and for which active keys (sorted by node number).
  // Rebuilding the filtered tables costs a map lookup per registry row,
  // every refinement-driven solve; sessions that check the same stack
  // repeatedly -- the KLEE bracket pattern -- pay it for an identical
  // result. Every write to the tables outside seedActiveReads clears the
  // flag, and the key fingerprint catches stack changes; rows behind an
  // unchanged key cannot change between rebuilds (they are recorded at
  // encode time, and re-encoding only happens after a rebuild, which
  // clears the flag too).
  bool batchTablesSeeded;
  std::vector<ASTNode> lastSeededKeys;

  // Seed the batch-side read table with only the reads of the given
  // (active) encodings, drawn from the persistent registry. The keys are
  // whatever this round's literals were cached under: base-level conjuncts
  // and, for the pushed levels, the nodes rootLitUnder reported.
  void seedActiveReads(const std::vector<ASTNode>& activeKeys)
  {
    // The fingerprint is only worth computing when a hit is possible: the
    // tables must be clean AND the key count unchanged. Sessions that add
    // content every check fail the size test in O(1) -- copying and
    // sorting an ever-growing key vector for a compare that cannot
    // succeed was measured at a few percent of a whole KLEE-style run.
    std::vector<ASTNode> sortedKeys;
    if (batchTablesSeeded && activeKeys.size() == lastSeededKeys.size())
    {
      sortedKeys = activeKeys;
      std::sort(sortedKeys.begin(), sortedKeys.end(),
                [](const ASTNode& a, const ASTNode& b) {
                  return a.GetNodeNum() < b.GetNodeNum();
                });
      if (sortedKeys == lastSeededKeys)
        return;
    }

    ArrayTransformer::ArrType filtered;
    for (const ASTNode& c : activeKeys)
    {
      std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>>::
          const_iterator rit = readsOfEncoded.find(c);
      if (rit == readsOfEncoded.end())
        continue;
      for (const std::pair<ASTNode, ASTNode>& ai : rit->second)
      {
        ArrayTransformer::ArrType::const_iterator ait = myReads.find(ai.first);
        if (ait == myReads.end())
          continue;
        ArrayTransformer::arrTypeMap::const_iterator iit =
            ait->second.find(ai.second);
        if (iit == ait->second.end())
          continue;
        filtered[ai.first].insert(*iit);
      }
    }

    lastSeededReads.clear();
    for (ArrayTransformer::ArrType::const_iterator ait = filtered.begin();
         ait != filtered.end(); ++ait)
      for (ArrayTransformer::arrTypeMap::const_iterator iit =
               ait->second.begin();
           iit != ait->second.end(); ++iit)
        lastSeededReads.push_back(std::make_pair(ait->first, iit->first));

    batchAT->arrayToIndexToRead = filtered;
    lastSeededKeys.swap(sortedKeys);
    batchTablesSeeded = true;
  }

  void totalizeRegistrySymbols()
  {
    // Only the refinement machinery encodes axioms over registry symbols,
    // and --ackermanize never refines.
    if (bm->UserFlags.ackermannisation)
      return;

    for (ArrayTransformer::ArrType::const_iterator it = myReads.begin();
         it != myReads.end(); ++it)
    {
      for (ArrayTransformer::arrTypeMap::const_iterator rit =
               it->second.begin();
           rit != it->second.end(); ++rit)
      {
        totalizeSymbol(rit->second.symbol);
        totalizeSymbol(rit->second.index_symbol);
      }
    }
  }

  // The same guarantee for the rows an extensionality round refines over.
  // Those rows live in the batch transformer's per-round table, not in the
  // persistent registry -- the round transforms on a fresh table by design
  // -- so totalizeRegistrySymbols cannot cover them. Idempotent (the bit
  // creation is memoised), so calling it before every refinement entry is
  // cheap, and necessary: the checker's lemma encodings can add rows
  // mid-round.
  void totalizeBatchRegistrySymbols()
  {
    for (ArrayTransformer::ArrType::const_iterator it =
             batchAT->arrayToIndexToRead.begin();
         it != batchAT->arrayToIndexToRead.end(); ++it)
    {
      for (ArrayTransformer::arrTypeMap::const_iterator rit =
               it->second.begin();
           rit != it->second.end(); ++rit)
      {
        totalizeSymbol(rit->second.symbol);
        totalizeSymbol(rit->second.index_symbol);
      }
    }
  }

  // Rebuild the SAT side from nothing, keeping every semantic store. The
  // persistent encoding never reclaims anything, so a long session whose
  // popped content never returns pays for it in solver memory and dead
  // decision variables; once that dominates, starting the solver over and
  // re-encoding just the live stack is the standard relief valve. The
  // bit-blast memo and the AIG survive, so re-encoding active content is
  // a walk over existing circuits; refinement axioms die with the solver
  // and are re-derived lazily, which is sound -- they are accelerators.
  // (The finer-grained alternative -- pinning popped variables away from
  // the decision heuristics, as cvc5's CaDiCaL propagator does -- needs
  // the propagator interface and is not portable across our backends.)
  // Steer the decision heuristic away from retracted content: every
  // literal that has ever carried a level or a block is hinted toward
  // its falsifying value while it is not among this call's assumptions.
  // A popped level's literal is unconstrained, and a backend whose
  // default phase is positive would otherwise keep pulling the dead
  // level's cone into the search until the heuristic learns better.
  // Search advice only -- it cannot change a verdict, and assumed
  // literals need no hint because assumptions are forced, not decided.
  void hintRetractedLevels(const SATSolver::vec_literals& assumptions)
  {
    std::unordered_set<int> current;
    for (int i = 0; i < assumptions.size(); i++)
      current.insert(assumptions[i].x);

    for (const int lit : everAssumedLits)
    {
      if (current.count(lit))
        continue;
      solver->suggestPhase(lit >> 1, (lit & 1) != 0);
    }
  }

  void rebuildEncodings()
  {
    solver.reset(makeBackend(bm->UserFlags));
    solver->enableRefinement(true);
    if (trailReuseAllowed)
      solver->enableTrailReuse();
    bvaDecided = false;

    aigIdToVar.clear();
    trueVar = -1;
    rootLitOf.clear();
    actLitOf.clear();
    everAssumedLits.clear();
    batchTablesSeeded = false;
    lastSeededKeys.clear();
    level0Asserted.clear();
  }

  // The batch pipeline's bounded-variable-addition policy, applied to the
  // persistent solver (see TopLevelSTPAux): an explicit ON always asks,
  // AUTO asks only for array problems, and the answer must land inside the
  // backend's configuration window, which closes at its first clause. Here
  // that window is the start of the first engaged check-sat -- and it
  // reopens when the relief valve rebuilds the solver, which is why
  // rebuildEncodings resets the flag. AUTO judges the levels' prepared
  // fragments, so arrays that only appear after floating-point
  // totalisation count, as they do in batch, and whole-array equality
  // counts through the fragment it lowers into reads; the persistent read
  // registry keeps the answer stable across a rebuild whose live stack
  // happens to be array-free at that moment. Under --ackermanize arrays
  // never reach the solver as arrays, so AUTO stays off, as in batch.
  void decideBVA(const ASTVec& assertionsSMT2)
  {
    if (bvaDecided)
      return;
    bvaDecided = true;

    const UserDefinedFlags& uf = bm->UserFlags;
    bool wants = uf.cadical_factor == UserDefinedFlags::BVAMode::ON;
    if (uf.cadical_factor == UserDefinedFlags::BVAMode::AUTO &&
        !uf.ackermannisation)
    {
      wants = !myReads.empty();
      for (size_t i = 0; !wants && i < assertionsSMT2.size(); i++)
      {
        const Fragment& f = fragment(assertionsSMT2[i]);
        wants = f.arrays || f.arrayEq;
      }
    }

    if (!wants)
      return;

    if (!solver->enableBVA() &&
        uf.cadical_factor == UserDefinedFlags::BVAMode::ON && !bvaWarned)
    {
      bvaWarned = true;
      std::cerr << "Warning: --cadical-factor was requested but the SAT "
                   "solver in use has no bounded variable addition to "
                   "enable; using its own settings instead."
                << std::endl;
    }
  }

  // The literal to assume for one pushed level, given the level's root
  // literals: the root itself for a single conjunct, else the (possibly
  // cached) activation literal that implies them all.
  int levelAssumption(std::vector<int>& roots)
  {
    assert(!roots.empty());
    if (roots.size() == 1)
      return roots[0];

    std::sort(roots.begin(), roots.end());
    roots.erase(std::unique(roots.begin(), roots.end()), roots.end());
    if (roots.size() == 1)
      return roots[0];

    std::map<std::vector<int>, int>::const_iterator it = actLitOf.find(roots);
    if (it != actLitOf.end())
      return it->second;

    // Stored and returned as a LITERAL (2*var), like everything else in
    // this file -- a cache hit that handed back the bare variable was a
    // garbage assumption that left the whole level unconstrained.
    const int act = solver->newVar();
    for (const int root : roots)
      addBinary(2 * act + 1, root);
    const int actLit = 2 * act;
    actLitOf[roots] = actLit;
    return actLit;
  }

  // A variable eliminated before it was ever encoded has no SAT bits; its
  // value is its definition, evaluated recursively -- the same SolverMap
  // channel the batch pipeline's eliminations use (and which the batch
  // pipeline clears before every solve of its own). Only never-encoded
  // variables are seeded: an encoded one gets its value from its bits.
  void seedEliminatedIntoModelChannel()
  {
    for (ASTNodeMap::const_iterator it = sigma0.begin(); it != sigma0.end();
         ++it)
    {
      if (bbMgr.symbolToBBNode.find(it->first) == bbMgr.symbolToBBNode.end())
        batchSimp->Return_SolverMap()->insert(*it);
    }
  }

  // Values for every symbol the persistent encoding knows about. Symbols
  // from popped scopes are included -- their SAT variables are merely
  // unconstrained -- which the model printers tolerate (they iterate the
  // currently declared symbols, not this map). The refinement tables do
  // NOT tolerate them: seedActiveReads keeps popped rows away from model
  // construction and the congruence check.
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

// The ToSATBase the refinement machinery drives. Everything is already
// encoded and axioms arrive as direct clauses, so CallSAT only ever needs
// to re-solve -- under the check-sat's captured assumptions, which is what
// keeps refinement lemmas permanent while retractable assertions stay
// retractable.
class IncrementalToSAT : public ToSATBase
{
  IncrementalSolver::Impl* d;
  const SATSolver::vec_literals* assumps;

public:
  IncrementalToSAT(STPMgr* bm, IncrementalSolver::Impl* d_)
      : ToSATBase(bm), d(d_), assumps(NULL)
  {
  }

  void setAssumptions(const SATSolver::vec_literals* a) { assumps = a; }

  bool CallSAT(SATSolver& SatSolver, const ASTNode& input,
               bool /*doesAbsRef*/) override
  {
    // The refinement protocol passes ASTTrue: "the clauses are already in
    // the solver, search again".
    assert(input == ASTTrue);
    (void)input;

    bm->GetRunTimes()->start(RunTimes::Solving);
    bool sat;
    if (assumps != NULL && assumps->size() > 0)
      sat = SatSolver.solveWithAssumptions(*assumps, bm->soft_timeout_expired);
    else
      sat = SatSolver.solve(bm->soft_timeout_expired);
    bm->GetRunTimes()->stop(RunTimes::Solving);
    return sat;
  }

  ASTNodeToSATVar& SATVar_to_SymbolIndexMap() override
  {
    d->symbolMapStorage.clear();
    d->buildSymbolMap(d->symbolMapStorage);
    return d->symbolMapStorage;
  }

  void ClearAllTables(void) override {}
};

ToSATBase* IncrementalSolver::Impl::ensureAdapter()
{
  if (!adapter)
    adapter.reset(new IncrementalToSAT(bm, this));
  return adapter.get();
}

// A check-sat whose active stack carries whole-array equality. The
// extensionality procedure reasons about the COMPLETE array graph of the
// solve -- every transformed read must be owned by it -- so the whole
// active set is lowered, prepared and encoded as ONE per-round block,
// assumed as a single root literal on the persistent solver, mirroring the
// batch choreography (TopLevelSTP/TopLevelSTPAux) step for step. The
// block's registry rows and witness symbols are solve-local by the
// procedure's design (beginSolve wipes them), so nothing here touches the
// driver's persistent lazy registry, and block roots are deliberately not
// cached: a cached root would resurrect circuits over witnesses whose
// records the next round regenerated. Reuse still happens one level down
// -- the bit-blaster's memo shares every unchanged subcircuit, and learned
// clauses over those survive.
SOLVER_RETURN_TYPE
IncrementalSolver::Impl::extCheckSat(const ASTVec& assertionsSMT2)
{
  UserDefinedFlags& uf = bm->UserFlags;

  // Eager Ackermannization expands reads into if-then-else chains,
  // destroying the array structure the lazy procedure works on -- the same
  // per-solve override, warning included, the batch pipeline applies.
  const bool savedAck = uf.ackermannisation;
  if (uf.ackermannisation)
  {
    std::cerr << "Warning: --ackermanize is disabled for queries with "
                 "array equality."
              << std::endl;
    uf.ackermannisation = false;
  }

  ASTNode activeConjunction;
  if (assertionsSMT2.size() > 1)
    activeConjunction = bm->CreateNode(AND, assertionsSMT2);
  else
    activeConjunction = assertionsSMT2[0];

  bool activeHasFp = false;
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    if (fragment(levelConjunction).fp)
    {
      activeHasFp = true;
      break;
    }
  }

  ExtensionalityContext* ext = bm->getExtensionality();
  ext->beginSolve();

  ASTNodeMap arrayEqualityRewrites;
  ASTNode prepared = activeConjunction;
  if (activeHasFp)
  {
    prepared = fpContext()->prepare(prepared);
    fpContext()->copyArrayEqualityRewrites(arrayEqualityRewrites);
  }

  ASTNode semantic = ext->lowerArrayEqualities(prepared, arrayEqualityRewrites);
  ASTNode inputToSat = semantic;

  const bool extActive = ext->active();
  // Releases the record-table seal on every exit from this function.
  ExtensionalityContext::SolveScope extScope(ext);

  if (extActive)
    inputToSat = ext->conjoinRecordConstraints(inputToSat);

  if (activeHasFp)
    inputToSat = fpContext()->lowerPrepared(inputToSat);

  const bool extPrepared = extActive && !inputToSat.isConstant();
  if (extPrepared)
    inputToSat = ext->prepare(inputToSat);

  extKeepAlive.insert(activeConjunction);
  extKeepAlive.insert(prepared);
  extKeepAlive.insert(semantic);
  extKeepAlive.insert(inputToSat);

  if (uf.enable_array_equality && containsArrayEquality(inputToSat))
    FatalError("IncrementalSolver: an opaque array equality reached the "
               "final array transformation boundary",
               inputToSat);

  // A fresh per-round registry: the whole-graph transform must neither see
  // the persistent lazy rows (it refuses reused legacy rows) nor leak its
  // own solve-local rows into them. The rows are left in place afterwards
  // -- model construction reads them -- until the next solve or pop clears
  // the batch tables as usual.
  batchAT->arrayToIndexToRead.clear();
  batchAT->ack_pair.clear();
  batchTablesSeeded = false;

  const bool arrayops = containsArrayOps(inputToSat, bm) || extActive;
  if (arrayops)
    inputToSat = batchAT->TransformFormula_TopLevel(inputToSat);
  if (extPrepared)
    ext->bindAfterTransform(batchAT);

  // Encode the block; its root is assumed, never asserted -- the block
  // spans every level, including the base. Every generated symbol in the
  // block (witnesses, scalar names, read abstractions) is named
  // deterministically by what it stands for, so an identical stack lowers
  // to the identical node and this cache hit makes the repeat round's
  // encoding free -- and the recycled names keep previously encoded
  // checker lemmas attached to the right SAT variables.
  int blockLit;
  bool blockReused = false;
  {
    NodeToLitMap::const_iterator hit = rootLitOf.find(inputToSat);
    if (hit != rootLitOf.end())
    {
      blockLit = hit->second;
      blockReused = true;
    }
    else
    {
      bm->GetRunTimes()->start(RunTimes::BitBlasting);
      BBNodeAIG root = bb.BBForm(inputToSat);
      bm->GetRunTimes()->stop(RunTimes::BitBlasting);
      bm->GetRunTimes()->start(RunTimes::CNFConversion);
      Aig_Obj_t* regular = Aig_Regular(root.n);
      ensureEncoded(regular);
      blockLit = 2 * varOfAig(regular) + (Aig_IsComplement(root.n) ? 1 : 0);
      bm->GetRunTimes()->stop(RunTimes::CNFConversion);
      rootLitOf[inputToSat] = blockLit;
    }
  }

  // Refinement lemmas are encoded over the abstraction/witness/scalar
  // names; give every bit of every such symbol a variable before the
  // first solve, fresh and unconstrained where the blasted block never
  // needed it -- the meaning ToSATAIG's lemma-only path assigns.
  if (extActive)
  {
    for (const ASTNode& s : ext->getFrozenSymbols())
      totalizeSymbol(s);
    for (const ASTNode& s : ext->getLemmaOnlySymbols())
      totalizeSymbol(s);
  }

  if (uf.stats_flag)
  {
    std::cerr << "Incremental: array-equality round, block of "
              << assertionsSMT2.size() << " levels "
              << (blockReused ? "reused" : "encoded") << ", solver has "
              << solver->nVars() << " variables" << std::endl;
  }

  uf.construct_counterexample_flag = true;

  if (fpCtx)
    ce->setFpEncodingContext(fpCtx.get());

  seedEliminatedIntoModelChannel();

  if (uf.timeout_max_conflicts >= 0)
    solver->setMaxConflicts(uf.timeout_max_conflicts);
  if (uf.timeout_max_time >= 0)
    solver->setMaxTime(uf.timeout_max_time);
  bm->soft_timeout_expired = false;

  SATSolver::vec_literals assumptions;
  everAssumedLits.insert(blockLit);
  assumptions.push(SATSolver::mkLit(blockLit >> 1, blockLit & 1));
  hintRetractedLevels(assumptions);

  IncrementalToSAT* tosat = static_cast<IncrementalToSAT*>(ensureAdapter());
  tosat->setAssumptions(&assumptions);

  // Congruence axioms are encoded straight over the bit variables of the
  // round registry's read symbols, and the block's cone may have needed
  // only some of a symbol's bits (the frozen/lemma-only totalisation
  // above covers the checker's symbols, not the registry rows). This
  // matters most for the hybrid below: a round routed here for an array
  // equality that simplified away runs ordinary read refinement with the
  // checker inactive.
  totalizeBatchRegistrySymbols();

  SOLVER_RETURN_TYPE res = ce->CallSAT_ResultCheck(
      *solver, bm->ASTTrue, semantic, prepared, tosat, true);

  // The refinement driver, as in TopLevelSTPAux: with an active equality
  // the checker owns every read, so each undecided candidate must carry a
  // pending theory lemma; without one, ordinary read refinement runs.
  while (res == SOLVER_UNDECIDED)
  {
    // Re-totalize: the checker's lemma encodings can introduce new reads,
    // whose rows joined the table after the pass above. Memoised, so a
    // round that added nothing pays nothing.
    totalizeBatchRegistrySymbols();
    if (extActive)
    {
      if (!ext->hasPendingLemma())
        FatalError("IncrementalSolver: an active array-equality refinement "
                   "round has neither a decision nor a pending lemma");
      ext->encodePendingLemmas(*solver, tosat);
      res = ce->CallSAT_ResultCheck(*solver, bm->ASTTrue, semantic, prepared,
                                    tosat, true);
    }
    else
    {
      res = ce->SATBased_ArrayReadRefinement(*solver, semantic, tosat);
    }
  }

  tosat->setAssumptions(NULL);
  uf.ackermannisation = savedAck;

  // The whole round rode one block literal, so an unsat answer has no
  // per-level or per-assumption granularity: the core is everything.
  if (res == SOLVER_UNSATISFIABLE)
    recordUnsat(assumptions, assertionsSMT2.size(), true);

  return res;
}

IncrementalSolver::IncrementalSolver(STPMgr* bm, AbsRefine_CounterExample* ce,
                                     Simplifier* batchSimp,
                                     ArrayTransformer* batchAT)
    : impl(new Impl(bm, ce, batchSimp, batchAT))
{
}

std::vector<std::pair<ASTNode, ASTNode>>
IncrementalSolver::seededReadsForTesting() const
{
  return impl->lastSeededReads;
}

bool IncrementalSolver::lastSolveWasUnsat() const
{
  return impl->lastUnsat;
}

bool IncrementalSolver::lastUnsatHasAssumptionGranularity() const
{
  return impl->lastUnsat && !impl->lastUnsatCoarse &&
         impl->lastLevelIndividual;
}

std::vector<ASTNode> IncrementalSolver::lastUnsatAssumptionConjuncts() const
{
  std::vector<ASTNode> out;
  if (!lastUnsatHasAssumptionGranularity())
    return out;
  const std::unordered_set<int> failed(impl->lastFailedLits.begin(),
                                       impl->lastFailedLits.end());
  for (const std::pair<int, ASTNode>& lc : impl->lastLevelLitConjuncts)
  {
    if (failed.count(lc.first))
      out.push_back(lc.second);
  }
  return out;
}

std::vector<size_t> IncrementalSolver::lastUnsatCoreLevels() const
{
  std::vector<size_t> out;
  if (!impl->lastUnsat)
    return out;
  if (impl->lastUnsatCoarse)
  {
    for (size_t i = 1; i < impl->lastLevelCount; i++)
      out.push_back(i);
    return out;
  }
  const std::unordered_set<int> failed(impl->lastFailedLits.begin(),
                                       impl->lastFailedLits.end());
  std::unordered_set<size_t> seen;
  for (const std::pair<int, size_t>& ll : impl->assumedLitLevels)
  {
    if (failed.count(ll.first) && seen.insert(ll.second).second)
      out.push_back(ll.second);
  }
  std::sort(out.begin(), out.end());
  return out;
}

IncrementalSolver::~IncrementalSolver()
{
  // The counterexample machinery may still point at our floating-point
  // encoding context; whoever solves next installs their own before any
  // model is read (and model_valid already refuses stale reads).
  if (impl->fpCtx)
    impl->ce->setFpEncodingContext(NULL);
}

bool IncrementalSolver::canHandle(const ASTVec& assertionsSMT2)
{
  // Every construct the SMT-LIB frontend can produce is covered: plain
  // bit-vectors, arrays (lazy or --ackermanize), floating point, and
  // whole-array equality. The method remains the seam for any future
  // exclusion.
  (void)assertionsSMT2;
  return true;
}

namespace
{

// Several passes a check-sat runs -- the per-conjunct Simplifier,
// substitution replace(), the bit-blaster -- walk formulas by recursion,
// so their depth tolerance is the stack size. Parse-time inlining of
// chained define-funs builds nodes tens of thousands deep from flat
// input (27k chained defines reach depth ~25k, needing ~8.3MB right
// where the common default stack ends), so the driver runs each
// check-sat on a worker thread with an explicitly large stack instead
// of inheriting whatever the process got. 256MB is reservation, not
// commitment: pages are only touched as the recursion actually deepens.
// The batch pipeline's smaller frames clear the same benchmarks within
// a default stack, which is why this lives here and not process-wide.
void* bigStackTrampoline(void* p)
{
  // CONSTANTBV keeps its working state -- word-size masks, the constants
  // bits_() decodes every vector's header through -- in thread-local
  // storage, initialised by BitVector_Boot. The frontend booted the main
  // thread at startup; a worker that skips this reads every bit-vector
  // constant through zeroed masks, which shows up as out-of-bounds reads
  // and impossible widths far downstream.
  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if (0 != c)
    FatalError("IncrementalSolver: CONSTANTBV failed to boot on the "
               "solve thread");
  (*static_cast<std::function<void()>*>(p))();
  return NULL;
}

void runOnBigStack(std::function<void()> fn)
{
  static const size_t stackBytes = 256 * 1024 * 1024;
#if defined(_WIN32)
  HANDLE t = CreateThread(NULL, stackBytes,
                          (LPTHREAD_START_ROUTINE)bigStackTrampoline, &fn,
                          STACK_SIZE_PARAM_IS_A_RESERVATION, NULL);
  if (t != NULL)
  {
    WaitForSingleObject(t, INFINITE);
    CloseHandle(t);
    return;
  }
#else
  pthread_attr_t attr;
  if (pthread_attr_init(&attr) == 0)
  {
    pthread_t t;
    const bool created = pthread_attr_setstacksize(&attr, stackBytes) == 0 &&
                         pthread_create(&t, &attr, bigStackTrampoline, &fn) == 0;
    pthread_attr_destroy(&attr);
    if (created)
    {
      pthread_join(t, NULL);
      return;
    }
  }
#endif
  // No thread to be had; the caller's stack is still a correct place to
  // run, just without the extra headroom.
  fn();
}

} // namespace

void IncrementalSolver::runOnDriverStack(const std::function<void()>& body)
{
  std::exception_ptr thrown;

  // The node uid counter is thread-local: the worker continues this
  // thread's numbering and this thread adopts the advanced value back,
  // so a uid names one node across both threads and the caches keyed on
  // node numbers stay sound.
  const uint64_t uidBefore = ASTInternal::getUidCounter();
  uint64_t uidAfter = uidBefore;

  runOnBigStack([&]() {
    ASTInternal::adoptUidCounter(uidBefore);
    try
    {
      body();
    }
    catch (...)
    {
      thrown = std::current_exception();
    }
    uidAfter = ASTInternal::getUidCounter();
  });

  ASTInternal::adoptUidCounter(uidAfter);
  if (thrown)
    std::rethrow_exception(thrown);
}

SOLVER_RETURN_TYPE IncrementalSolver::checkSat(const ASTVec& assertionsSMT2,
                                               bool assumeLastLevelPerConjunct)
{
  SOLVER_RETURN_TYPE result = SOLVER_ERROR;
  runOnDriverStack([&]() {
    result =
        checkSatOnCurrentStack(assertionsSMT2, assumeLastLevelPerConjunct);
  });
  return result;
}

void IncrementalSolver::materializePendingModel()
{
  if (!impl->modelPending)
    return;
  impl->modelPending = false;
  // Construction evaluates terms over deep formulas by recursion, so it
  // gets the same stack the solve itself had.
  runOnDriverStack([&]() { materializeOnCurrentStack(); });
}

void IncrementalSolver::materializeOnCurrentStack()
{
  STPMgr* bm = impl->bm;
  bm->GetRunTimes()->start(RunTimes::CounterExampleGeneration);
  impl->ce->ClearCounterExampleMap();
  impl->ce->ClearComputeFormulaMap();

  impl->seedEliminatedIntoModelChannel();

  ToSATBase::ASTNodeToSATVar symbolMap;
  impl->buildSymbolMap(symbolMap);
  impl->ce->ConstructCounterExample(*impl->solver, symbolMap);
  bm->GetRunTimes()->stop(RunTimes::CounterExampleGeneration);

  if (bm->UserFlags.stats_flag)
    std::cerr << "Incremental: model materialized on demand" << std::endl;
}

SOLVER_RETURN_TYPE
IncrementalSolver::checkSatOnCurrentStack(const ASTVec& assertionsSMT2,
                                          bool assumeLastLevelPerConjunct)
{
  STPMgr* bm = impl->bm;
  UserDefinedFlags& uf = bm->UserFlags;

  assert(!assertionsSMT2.empty());

  // The unsat story is per solve; a stale one must not answer for this
  // call.
  impl->lastUnsat = false;
  impl->lastUnsatCoarse = false;
  impl->lastLevelIndividual = false;
  impl->modelPending = false;
  impl->assumedLitLevels.clear();
  impl->lastLevelLitConjuncts.clear();
  impl->lastFailedLits.clear();

  // The relief valve: once the solver is past the configured size and most
  // of its encodings belong to content no longer on the stack, start it
  // over from the live stack. Checked before routing so extensionality
  // rounds benefit too.
  if (uf.incremental_reencode_limit > 0 &&
      (int64_t)impl->solver->nVars() >= uf.incremental_reencode_limit)
  {
    size_t active = 0;
    ASTVec probe;
    for (const ASTNode& levelConjunction : assertionsSMT2)
      splitConjuncts(levelConjunction, bm->ASTTrue, probe);
    active = probe.size();

    if (impl->rootLitOf.size() >= 4 * (active + 1))
    {
      if (uf.stats_flag)
        std::cerr << "Incremental: re-encoded from scratch (solver had "
                  << impl->solver->nVars() << " variables for " << active
                  << " active conjuncts)" << std::endl;
      impl->rebuildEncodings();
    }
  }

  // Trail reuse pays on the many-small-queries sessions and hurts on the
  // floating-point families, whose search is phase-sensitive and whose
  // instances are large -- every measured loss had FP content, every win
  // was FP-free. The option is configuration-window-only, so retirement
  // means starting the solver over without it: free when FP is present
  // from the first solve (nothing is encoded yet), and one bounded
  // rebuild if FP arrives -- or the encoding outgrows the size belt --
  // mid-session.
  if (impl->trailReuseAllowed)
  {
    bool retire = impl->solver->nVars() >= Impl::trailReuseVarLimit;
    for (size_t i = 0; !retire && i < assertionsSMT2.size(); i++)
      retire = impl->fragment(assertionsSMT2[i]).fp;
    if (retire)
    {
      impl->trailReuseAllowed = false;
      if (uf.stats_flag)
        std::cerr << "Incremental: trail reuse retired ("
                  << impl->solver->nVars()
                  << " variables), solver restarted without it" << std::endl;
      impl->rebuildEncodings();
    }
  }

  // The backend's configuration window closes at its first clause; take
  // the bounded-variable-addition decision while it is still open. This
  // must precede the extensionality routing below: an equality round
  // encodes into the same persistent solver.
  impl->decideBVA(assertionsSMT2);

  // Whole-array equality routes the entire check-sat through the
  // extensionality block: the procedure owns the round's complete array
  // graph, so no conjunct may be encoded separately this round. New
  // base-level conjuncts stay out of level0Asserted and simply become
  // permanent units in a later equality-free round; this round the block
  // covers them.
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    if (impl->fragment(levelConjunction).arrayEq)
      return impl->extCheckSat(assertionsSMT2);
  }

  // No active equality this round, so no stale equality state may survive
  // into it: the consistency checker keys off ext->active(), and a
  // previous round's solve-local records would send this round's model to
  // a checker expecting values for symbols it never encoded. The SMT-LIB2
  // pop clears this itself, but the C API's vc_pop deliberately clears
  // nothing (its model outlives the bracket), and check-sat-assuming's
  // frame pop keeps the model too -- so the round boundary is here.
  ExtensionalityContext* staleExt = bm->getExtensionalityIfAny();
  if (staleExt != NULL && staleExt->active())
    staleExt->beginSolve();

  const uint64_t clausesBefore = impl->clausesAdded;
  impl->encodesThisCall = 0;

  // Fresh per-call speculative state (but don't clear speculationDisabled
  // — that's set by the validation-failure retry to prevent recursion).
  impl->callCBP.reset();
  impl->speculativeOriginals.clear();
  impl->speculativeThisCall = false;

  // Base level: every conjunct becomes a permanent unit clause, once. The
  // base level only grows (reset destroys this object), so this is monotone
  // and sound even though the level's conjunction node is re-collapsed --
  // and possibly re-simplified -- on every call.
  ASTVec conjuncts;
  splitConjuncts(assertionsSMT2[0], bm->ASTTrue, conjuncts);

  ASTVec newLevel0;
  for (const ASTNode& c : conjuncts)
  {
    if (!impl->level0Asserted.insert(c).second)
      continue;
    newLevel0.push_back(c);
    if (uf.optimize_flag)
      impl->harvestSigma0(c);
  }

  for (const ASTNode& c : newLevel0)
  {
    const int lit = impl->rootLit(c);
    SATSolver::vec_literals unit;
    unit.push(SATSolver::mkLit(lit >> 1, lit & 1));
    impl->addClause(unit);
  }

  // Definitions found at the PUSHED levels hold only while their levels are
  // live, so they are collected per call, applied to pushed conjuncts only
  // -- a base-level unit is permanent and must never absorb a retractable
  // truth -- and every defining equation stays assumed. Nothing about them
  // persists between calls.
  ASTNodeMap merged;
  ASTNodeSet pushedSources;
  bool havePushed = false;
  if (uf.optimize_flag)
  {
    ASTNodeMap sigmaP;
    for (size_t level = 1; level < assertionsSMT2.size(); level++)
    {
      conjuncts.clear();
      splitConjuncts(assertionsSMT2[level], bm->ASTTrue, conjuncts);
      for (const ASTNode& c : conjuncts)
        impl->harvestPushed(c, sigmaP, pushedSources);
    }
    if (!sigmaP.empty())
    {
      merged = impl->sigma0;
      merged.insert(sigmaP.begin(), sigmaP.end());
      havePushed = true;
    }
  }

  // Pushed levels: encode (against the permanent caches) and assume one
  // literal per level -- the root itself for a single conjunct, else an
  // activation literal implying the level's roots. The assumption set is
  // recomputed from the current stack on every call, so popped levels
  // vanish by simply no longer being here. Each conjunct's encoding key
  // -- the conjunct itself, or the rewritten node the pushed-definitions
  // path cached under -- is collected so refinement can seed its tables
  // from what was actually assumed.
  SATSolver::vec_literals assumptions;
  std::vector<ASTNode> activeEncodedKeys;
  std::vector<int> levelRoots;
  for (size_t level = 1; level < assertionsSMT2.size(); level++)
  {
    conjuncts.clear();
    splitConjuncts(assertionsSMT2[level], bm->ASTTrue, conjuncts);
    if (conjuncts.empty())
      continue;

    levelRoots.clear();
    for (const ASTNode& c : conjuncts)
    {
      ASTNode encodedAs = c;
      levelRoots.push_back(
          havePushed
              ? impl->rootLitUnder(c, merged, pushedSources, encodedAs)
              : impl->rootLit(c));
      activeEncodedKeys.push_back(encodedAs);
    }

    if (assumeLastLevelPerConjunct && level + 1 == assertionsSMT2.size())
    {
      // Per-assumption failure granularity: each conjunct's own root is
      // assumed, and remembered against its conjunct, so an unsat answer
      // can name exactly the assumptions the refutation used.
      impl->lastLevelIndividual = true;
      for (size_t k = 0; k < conjuncts.size(); k++)
      {
        const int r = levelRoots[k];
        impl->everAssumedLits.insert(r);
        impl->assumedLitLevels.push_back(std::make_pair(r, level));
        impl->lastLevelLitConjuncts.push_back(
            std::make_pair(r, conjuncts[k]));
        assumptions.push(SATSolver::mkLit(r >> 1, r & 1));
      }
      continue;
    }

    const int lit = impl->levelAssumption(levelRoots);
    impl->everAssumedLits.insert(lit);
    impl->assumedLitLevels.push_back(std::make_pair(lit, level));
    assumptions.push(SATSolver::mkLit(lit >> 1, lit & 1));
  }

  impl->hintRetractedLevels(assumptions);

  if (uf.stats_flag)
  {
    std::cerr << "Incremental: encoded " << impl->encodesThisCall
              << " new conjuncts, added "
              << (impl->clausesAdded - clausesBefore) << " clauses, assumed "
              << assumptions.size() << " literals, solver has "
              << impl->solver->nVars() << " variables, "
              << impl->sigma0.size() << " base-level and "
              << (havePushed ? merged.size() - impl->sigma0.size() : 0)
              << " pushed substitutions" << std::endl;
  }

  // Array refinement needs a candidate model to find violated axioms, so
  // arrays force counterexample construction, exactly as in the batch
  // pipeline (TopLevelSTPAux). Under --ackermanize the transform compiles
  // arrays away eagerly -- each new read carries its if-then-else over the
  // existing reads -- so there is nothing to refine and the lean path
  // solves it like plain bit-vectors.
  bool activeHasArrays = false;
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    if (impl->fragment(levelConjunction).arrays)
    {
      activeHasArrays = true;
      break;
    }
  }
  const bool needRefinement = activeHasArrays && !uf.ackermannisation;

  // construct_counterexample_flag is both derived state and a direct
  // input: the C API's 'c' flag sets it explicitly, with no other trace
  // of the request. Folding it into the derivation keeps that request
  // alive across the write-back below, which previously clobbered it --
  // a 'c'-only session on a release build lost its counterexamples.
  bool construct = uf.check_counterexample_flag ||
                   uf.print_counterexample_flag || uf.produce_models ||
                   uf.construct_counterexample_flag || needRefinement;
#ifndef NDEBUG
  construct = true;
#endif
  uf.construct_counterexample_flag = construct;

  // Model evaluation of floating-point terms needs the encoding context
  // that lowered them. Batch fallback rounds install their own per solve;
  // this keeps the driver's rounds coherent the same way.
  if (impl->fpCtx)
    impl->ce->setFpEncodingContext(impl->fpCtx.get());

  // Budgets are per check-sat, as solve_by_sat_solver arms them per query.
  if (uf.timeout_max_conflicts >= 0)
    impl->solver->setMaxConflicts(uf.timeout_max_conflicts);
  if (uf.timeout_max_time >= 0)
    impl->solver->setMaxTime(uf.timeout_max_time);
  bm->soft_timeout_expired = false;

  if (needRefinement)
  {
    // The batch pipeline's own CEGAR: candidate model, violated congruence
    // axioms as direct (permanent -- they are tautologies of the canonical
    // read abstraction) clauses, solve again. The adapter re-solves under
    // this check-sat's assumptions, and the batch-side tables the
    // machinery reads are seeded from the driver's persistent stores.
    IncrementalToSAT* adapter =
        static_cast<IncrementalToSAT*>(impl->ensureAdapter());

    // Restrict the batch tables to the active cone's reads; stale rows
    // from popped scopes must not reach model construction or refinement.
    {
      std::vector<ASTNode> active(impl->level0Asserted.begin(),
                                  impl->level0Asserted.end());
      active.insert(active.end(), activeEncodedKeys.begin(),
                    activeEncodedKeys.end());
      impl->seedActiveReads(active);
    }
    impl->seedEliminatedIntoModelChannel();

    // Idempotent when nothing changed; essential after a re-encode, when
    // registry symbols from earlier sessions have no variables yet and the
    // axiom encoder reads their bits unconditionally.
    impl->totalizeRegistrySymbols();

    ASTNode activeConjunction;
    if (assertionsSMT2.size() > 1)
      activeConjunction = bm->CreateNode(AND, assertionsSMT2);
    else
      activeConjunction = assertionsSMT2[0];

    adapter->setAssumptions(&assumptions);
    SOLVER_RETURN_TYPE res = impl->ce->CallSAT_ResultCheck(
        *impl->solver, bm->ASTTrue, activeConjunction, activeConjunction,
        adapter, true);
    int refinement_rounds = 0;
    while (res == SOLVER_UNDECIDED)
    {
      refinement_rounds++;
      if (uf.stats_flag || refinement_rounds % 10 == 0)
        std::cerr << "Incremental: refinement round " << refinement_rounds
                  << ", solver has " << impl->solver->nVars() << " vars"
                  << std::endl;
      res = impl->ce->SATBased_ArrayReadRefinement(
          *impl->solver, activeConjunction, adapter);
    }
    if (refinement_rounds > 0 && uf.stats_flag)
      std::cerr << "Incremental: refinement converged after "
                << refinement_rounds << " rounds" << std::endl;
    adapter->setAssumptions(NULL);

    if (uf.stats_flag)
      impl->solver->printStats();

    if (res == SOLVER_UNSATISFIABLE)
      impl->recordUnsat(assumptions, assertionsSMT2.size(), false);

    // Speculative validation on the refinement path: if refinement
    // converged to SAT and we used aggressive CBP, validate the model
    // against the pre-simplified originals.
    if (res == SOLVER_SATISFIABLE && impl->speculativeThisCall)
    {
      if (!impl->validateModel(assertionsSMT2))
      {
        if (uf.stats_flag)
          std::cerr << "Incremental: speculative SAT failed validation "
                       "on refinement path"
                    << std::endl;

        impl->rebuildEncodings();
        impl->callCBP.reset();
        impl->speculativeOriginals.clear();
        impl->speculativeThisCall = false;
        impl->speculationDisabled = true;

        SOLVER_RETURN_TYPE retry = checkSatOnCurrentStack(
            assertionsSMT2, assumeLastLevelPerConjunct);

        impl->speculationDisabled = false;
        return retry;
      }
    }

    return res;
  }

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
  {
    // UNSAT is always sound under speculative simplification: the
    // simplified formula is weaker (has fewer constraints), so if
    // the weaker formula is UNSAT, the original is definitely UNSAT.
    impl->recordUnsat(assumptions, assertionsSMT2.size(), false);
    return SOLVER_UNSATISFIABLE;
  }

  // ── Speculative validation ───────────────────────────────────────
  // If we used aggressive simplification, validate the SAT model
  // against the pre-simplified conjuncts. If any are violated, the
  // aggressive simplification dropped a constraint that matters —
  // re-encode those conjuncts conservatively and re-solve.
  if (impl->speculativeThisCall)
  {
    // We need a model to validate against.
    impl->ce->ClearCounterExampleMap();
    impl->ce->ClearComputeFormulaMap();
    impl->seedEliminatedIntoModelChannel();
    ToSATBase::ASTNodeToSATVar symbolMap;
    impl->buildSymbolMap(symbolMap);
    impl->ce->ConstructCounterExample(*impl->solver, symbolMap);

    if (!impl->validateModel(assertionsSMT2))
    {
      if (uf.stats_flag)
        std::cerr << "Incremental: speculative SAT failed validation, "
                     "re-encoding" << std::endl;

      impl->rebuildEncodings();
      impl->callCBP.reset();
      impl->speculativeOriginals.clear();
      impl->speculativeThisCall = false;
      impl->speculationDisabled = true;

      // Re-run the check-sat from scratch without speculation.
      SOLVER_RETURN_TYPE retry = checkSatOnCurrentStack(
          assertionsSMT2, assumeLastLevelPerConjunct);

      // Re-enable speculation for future check-sats.
      impl->speculationDisabled = false;
      return retry;
    }

    if (uf.stats_flag)
      std::cerr << "Incremental: speculative SAT passed validation"
                << std::endl;
  }

  if (construct)
  {
    // Unless the model is read at solve time -- the self-check below is
    // such a reader -- construction is deferred to the first model query
    // and never happens for answers nobody samples. The SAT model this
    // materializes from stays live: the driver adds no clause and runs
    // no solve between user commands.
    if (!uf.check_counterexample_flag)
    {
      impl->modelPending = true;
      return SOLVER_SATISFIABLE;
    }

    bm->GetRunTimes()->start(RunTimes::CounterExampleGeneration);
    impl->ce->ClearCounterExampleMap();
    impl->ce->ClearComputeFormulaMap();

    impl->seedEliminatedIntoModelChannel();

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
