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
  // abstraction, merely dead weight while nothing constrains them.
  ArrayTransformer::ArrType myReads;

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

  // Per-call statistics, printed under --stats.
  uint64_t clausesAdded;

  Impl(STPMgr* bm_, AbsRefine_CounterExample* ce_, Simplifier* batchSimp_,
       ArrayTransformer* batchAT_)
      : bm(bm_), ce(ce_), batchSimp(batchSimp_), batchAT(batchAT_),
        solver(makeBackend(bm_->UserFlags)), substitutionMap(bm_),
        simp(bm_, &substitutionMap),
        bb(&bbMgr, &simp, bm_->defaultNodeFactory, &bm_->UserFlags, NULL),
        trueVar(-1), clausesAdded(0)
  {
    // Refinement adds clauses between solve calls; tell backends that need
    // to know (CryptoMiniSat skips its startup simplification).
    solver->enableRefinement(true);
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
  void harvestSigma0(const ASTNode& c)
  {
    ASTNode var, term;
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
        return;
    }
    else
      return;

    if (var == term)
      return;
    if (sigma0.find(var) != sigma0.end())
      return;
    // Only plain bit-vector/boolean definitions. An array-typed symbol is
    // not a substitutable value, and a floating-point-theory term must not
    // be injected into conjuncts whose lowering decision (a raw-conjunct
    // property) was already made without it.
    if (var.GetIndexWidth() != 0)
      return;
    if (bm->has_floating_point_theory && containsFloatingPointTheory(term, bm))
      return;
    if (term.GetKind() != TRUE && term.GetKind() != FALSE &&
        bm->VarSeenInTerm(var, term))
      return;

    // Frozen: the variable's bits already live in the solver, so this
    // equation must constrain them for real (see mustKeepRaw).
    if (bbMgr.symbolToBBNode.find(var) != bbMgr.symbolToBBNode.end())
      mustKeepRaw.insert(c);

    // Expand the replacement through what is already known, once. Chains
    // that stay partially expanded are fine: every equation remains
    // asserted, so partial rewriting is merely less simplification.
    ASTNodeMap cache;
    sigma0[var] = SubstitutionMap::replace(term, sigma0, cache,
                                           bm->defaultNodeFactory);
  }

  // What actually gets encoded for a conjunct: the conjunct rewritten under
  // the base-level substitutions and then simplified on its own
  // (assertion-local, equivalence-preserving; a fresh Simplifier per call
  // so no cross-assertion state exists to leak). Keyed by the ORIGINAL
  // conjunct in rootLitOf, so reuse is untouched; encoding under an older,
  // smaller sigma0 stays sound because sigma0 entries are permanent truths.
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

    // Assertion-local, equivalence-preserving simplification, with a fresh
    // Simplifier so no cross-assertion state can exist: its substitution
    // map is empty, so everything it does to this one conjunct is a plain
    // equivalence. Measurably worth it on multi-round workloads; sharing a
    // Simplifier across conjuncts measured slower, so this stays per call.
    SubstitutionMap localSm(bm);
    Simplifier localSimp(bm, &localSm);
    out = localSimp.SimplifyFormula_TopLevel(out, false);

    return out;
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

    if (frag.fp)
      toEncode = fpContext()->lowerPrepared(toEncode);

    if (frag.arrays)
    {
      batchAT->arrayToIndexToRead = myReads;
      batchAT->ack_pair = myAckPairs;
      toEncode = batchAT->TransformFormula_TopLevel(toEncode);
      myReads = batchAT->arrayToIndexToRead;
      myAckPairs = batchAT->ack_pair;
      assert(!containsArrayOps(toEncode, bm));
      totalizeRegistrySymbols();
    }

    bm->GetRunTimes()->start(RunTimes::BitBlasting);
    BBNodeAIG root = bb.BBForm(toEncode);
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
  assumptions.push(SATSolver::mkLit(blockLit >> 1, blockLit & 1));

  IncrementalToSAT* tosat = static_cast<IncrementalToSAT*>(ensureAdapter());
  tosat->setAssumptions(&assumptions);

  SOLVER_RETURN_TYPE res = ce->CallSAT_ResultCheck(
      *solver, bm->ASTTrue, semantic, prepared, tosat, true);

  // The refinement driver, as in TopLevelSTPAux: with an active equality
  // the checker owns every read, so each undecided candidate must carry a
  // pending theory lemma; without one, ordinary read refinement runs.
  while (res == SOLVER_UNDECIDED)
  {
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
  return res;
}

IncrementalSolver::IncrementalSolver(STPMgr* bm, AbsRefine_CounterExample* ce,
                                     Simplifier* batchSimp,
                                     ArrayTransformer* batchAT)
    : impl(new Impl(bm, ce, batchSimp, batchAT))
{
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

SOLVER_RETURN_TYPE IncrementalSolver::checkSat(const ASTVec& assertionsSMT2)
{
  STPMgr* bm = impl->bm;
  UserDefinedFlags& uf = bm->UserFlags;

  assert(!assertionsSMT2.empty());

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
  uint64_t newConjuncts = 0;

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
              << impl->solver->nVars() << " variables, "
              << impl->sigma0.size() << " base-level substitutions"
              << std::endl;
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

  bool construct = uf.check_counterexample_flag ||
                   uf.print_counterexample_flag || needRefinement;
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

    impl->batchAT->arrayToIndexToRead = impl->myReads;
    impl->seedEliminatedIntoModelChannel();

    ASTNode activeConjunction;
    if (assertionsSMT2.size() > 1)
      activeConjunction = bm->CreateNode(AND, assertionsSMT2);
    else
      activeConjunction = assertionsSMT2[0];

    adapter->setAssumptions(&assumptions);
    SOLVER_RETURN_TYPE res = impl->ce->CallSAT_ResultCheck(
        *impl->solver, bm->ASTTrue, activeConjunction, activeConjunction,
        adapter, true);
    while (res == SOLVER_UNDECIDED)
    {
      res = impl->ce->SATBased_ArrayReadRefinement(
          *impl->solver, activeConjunction, adapter);
    }
    adapter->setAssumptions(NULL);

    if (uf.stats_flag)
      impl->solver->printStats();

    // SOLVER_INVALID and SOLVER_SATISFIABLE (resp. VALID/UNSATISFIABLE)
    // are the same enum values, so this is already in check-sat terms.
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
    return SOLVER_UNSATISFIABLE;

  if (construct)
  {
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
