#include "stp/UninterpretedFunctions/UFRefinement.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolver.h"
#include "stp/ToSat/ToSATBase.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "extlib-constbv/constantbv.h"
#include <algorithm>
#include <map>
#include <set>
#include <sstream>

namespace stp
{

namespace
{

struct EqualityKey
{
  ASTNode left;
  ASTNode right;
  SourceSort sort;

  bool operator<(const EqualityKey& other) const
  {
    if (sort.kind() != other.sort.kind())
      return static_cast<int>(sort.kind()) <
             static_cast<int>(other.sort.kind());
    if (sort.kind() == SourceSort::Kind::BitVector &&
        sort.bitVectorWidth() != other.sort.bitVectorWidth())
      return sort.bitVectorWidth() < other.sort.bitVectorWidth();
    if (left != other.left)
      return left < other.left;
    return right < other.right;
  }
};

EqualityKey equalityKey(ASTNode left, ASTNode right, const SourceSort& sort)
{
  if (right < left)
    std::swap(left, right);
  EqualityKey key;
  key.left = left;
  key.right = right;
  key.sort = sort;
  return key;
}

struct PersistentScopeKey
{
  uint64_t epoch = 0;
  uint64_t block = 0;

  bool operator<(const PersistentScopeKey& other) const
  {
    return epoch != other.epoch ? epoch < other.epoch : block < other.block;
  }
};

class CounterExampleCandidate final : public UFScalarCandidate
{
public:
  CounterExampleCandidate(AbsRefine_CounterExample& ce,
                          const UFContext& context, uint64_t version)
      : ce_(ce), context_(context), version_(version)
  {
  }

  uint64_t version() const override { return version_; }

  bool read(const ASTNode& scalar, const SourceSort& expected,
            UFConcreteValue& value,
            std::string& diagnostic) const override
  {
    if (scalar.IsNull() || scalar.GetKind() != SYMBOL ||
        scalar.GetSourceSort() != expected)
    {
      diagnostic = "UF adapter was asked to read a non-symbol or wrong-sort "
                   "candidate scalar";
      return false;
    }
    ASTNode assigned = ce_.LookupAssignedValue(scalar);
    if (assigned.IsNull() || !assigned.isConstant())
    {
      // Generated names/results are the liveness contract itself and must be
      // present as direct SAT scalars. Ordinary source-symbol actuals may have
      // been eliminated by sound preprocessing; concretize those through the
      // host's completed scalar model instead of mistaking a symbolic
      // SolverMap definition for a candidate value.
      if (context_.isProtected(scalar))
      {
        diagnostic = "UF generated scalar has no direct up-front SAT "
                     "assignment";
        return false;
      }
      assigned = expected.kind() == SourceSort::Kind::Bool
                     ? ce_.ModelValueOfFormula(scalar)
                     : ce_.ModelValueOfTerm(scalar);
      if (assigned.IsNull() || !assigned.isConstant())
      {
        diagnostic = "UF source scalar could not be concretized from the "
                     "candidate model";
        return false;
      }
    }
    return UFConcreteValue::fromConstant(assigned, expected, value,
                                         diagnostic);
  }

private:
  AbsRefine_CounterExample& ce_;
  const UFContext& context_;
  const uint64_t version_;
};

struct MutableAdapterState
{
  explicit MutableAdapterState(STPMgr* manager_) : manager(manager_) {}

  STPMgr* manager;
  const LoweredApplicationView* view = NULL;
  UFAbstractLemma pendingLemma;
  bool pending = false;
  bool certified = false;
  UFFunctionModelSeedSet seed;
  std::map<ASTNode, UFConcreteValue> handleValues;
  std::string diagnostic;
  uint64_t nextCandidateVersion = 0;
  uint64_t candidateCheckCount = 0;
  uint64_t emittedLemmaCount = 0;

  void clearRound()
  {
    pending = false;
    pendingLemma = UFAbstractLemma();
    certified = false;
    seed = UFFunctionModelSeedSet();
    handleValues.clear();
    diagnostic.clear();
  }

  void clearActive()
  {
    clearRound();
    view = NULL;
  }
};

UFCandidateOutcome checkOneCandidate(
    MutableAdapterState& state,
    AbsRefine_CounterExample& counterexample)
{
  state.clearRound();
  if (state.view == NULL || !state.view->active())
    return UFCandidateOutcome::Skipped;
  UFContext* context = state.manager->getUFContextIfAny();
  if (context == NULL)
  {
    state.diagnostic = "UF adapter has an active view but no UF context";
    return UFCandidateOutcome::InternalError;
  }

  const uint64_t version = ++state.nextCandidateVersion;
  state.candidateCheckCount++;
  CounterExampleCandidate candidate(counterexample, *context, version);
  UFCheckResult result = UFChecker::check(context->activeDeclarations(),
                                          *state.view, candidate);
  if (result.status == UFCheckResult::Status::InternalError)
  {
    state.diagnostic = result.diagnostic;
    return UFCandidateOutcome::InternalError;
  }
  if (result.hasConflict())
  {
    if (!UFLemmaOracle::buildAndValidate(result.conflict,
                                         state.pendingLemma,
                                         state.diagnostic))
      return UFCandidateOutcome::InternalError;
    if (state.pendingLemma.candidateVersion != version)
    {
      state.diagnostic = "UF lemma retained the wrong candidate version";
      return UFCandidateOutcome::InternalError;
    }
    state.pending = true;
    return UFCandidateOutcome::Conflict;
  }

  if (!result.consistent() || result.modelSeed.candidateVersion != version)
  {
    state.diagnostic = "UF checker returned a malformed consistency seed";
    return UFCandidateOutcome::InternalError;
  }

  // Preserve every active durable handle, including duplicate applications
  // omitted from the finite table's one representative per concrete tuple.
  for (const LoweredApplicationRecord& record : state.view->applications)
  {
    UFConcreteValue value;
    if (!candidate.read(record.resultSymbol,
                        record.declaration->signature().codomain(), value,
                        state.diagnostic))
      return UFCandidateOutcome::InternalError;
    state.handleValues.insert(std::make_pair(record.durableHandle, value));
  }
  if (candidate.version() != version)
  {
    state.diagnostic = "UF candidate changed while retaining certified "
                       "handle values";
    return UFCandidateOutcome::InternalError;
  }
  state.seed = result.modelSeed;
  state.certified = true;
  return UFCandidateOutcome::Consistent;
}

bool supportedSort(const SourceSort& sort)
{
  return sort.kind() == SourceSort::Kind::Bool ||
         (sort.kind() == SourceSort::Kind::BitVector &&
          sort.bitVectorWidth() > 0);
}

unsigned scalarWidth(const SourceSort& sort)
{
  return sort.kind() == SourceSort::Kind::Bool ? 1 : sort.bitVectorWidth();
}

const char* validateLeaf(
    const ASTNode& leaf, const SourceSort& sort,
    const ToSATBase::ASTNodeToSATVar& bindings)
{
  if (!supportedSort(sort) || leaf.IsNull() || leaf.GetSourceSort() != sort)
    return "UF CNF leaf has the wrong SourceSort";
  if (leaf.isConstant())
  {
    if (sort.kind() == SourceSort::Kind::Bool)
      return leaf.GetKind() == TRUE || leaf.GetKind() == FALSE
                 ? NULL
                 : "UF CNF Boolean constant is malformed";
    return leaf.GetKind() == BVCONST &&
                   leaf.GetValueWidth() == sort.bitVectorWidth()
               ? NULL
               : "UF CNF bit-vector constant is malformed";
  }
  if (leaf.GetKind() != SYMBOL)
    return "UF CNF leaf is neither a constant nor a symbol";
  const ToSATBase::ASTNodeToSATVar::const_iterator found = bindings.find(leaf);
  if (found == bindings.end())
    return "UF CNF leaf was not registered before the first candidate";
  if (found->second.size() != scalarWidth(sort))
    return "UF CNF leaf has a wrong-width SAT mapping";
  for (const unsigned variable : found->second)
    if (variable == ~((unsigned)0))
      return "UF CNF leaf has an unencoded SAT bit";
  return NULL;
}

void validateLemmaBeforeMutation(
    const UFAbstractLemma& lemma,
    const ToSATBase::ASTNodeToSATVar& bindings, SATSolver& solver,
    int guardLiteral)
{
  std::vector<const UFEqualityAtom*> atoms;
  atoms.reserve(lemma.premise.size() + 1);
  for (const UFEqualityAtom& atom : lemma.premise)
    atoms.push_back(&atom);
  atoms.push_back(&lemma.conclusion);
  for (const UFEqualityAtom* atom : atoms)
  {
    const char* reason = validateLeaf(atom->left, atom->sort, bindings);
    if (reason != NULL)
      FatalError(reason, atom->left);
    reason = validateLeaf(atom->right, atom->sort, bindings);
    if (reason != NULL)
      FatalError(reason, atom->right);
  }
  // Backends expose different variable bases through this historical API
  // (CaDiCaL is one-based, MiniSat-family wrappers are zero-based), so nVars
  // cannot portably validate the upper bound. The exact-stack encoder handed
  // us a nonnegative literal obtained from its own live AIG binding; retain
  // that provenance check without inventing a backend-specific comparison.
  (void)solver;
  if (guardLiteral < -1)
    FatalError("UF persistent block guard is malformed");
  const std::vector<bool> premises(lemma.premise.size(), true);
  if (lemma.evaluate(false, premises))
    FatalError("UF abstract lemma does not reject its triggering candidate");
}

struct BitOperand
{
  bool constant = false;
  bool value = false;
  unsigned variable = 0;
};

BitOperand bitOperand(const ASTNode& leaf, const SourceSort& sort,
                      unsigned bit,
                      const ToSATBase::ASTNodeToSATVar& bindings)
{
  BitOperand result;
  if (!leaf.isConstant())
  {
    result.variable = bindings.find(leaf)->second[bit];
    return result;
  }
  result.constant = true;
  if (sort.kind() == SourceSort::Kind::Bool)
    result.value = leaf.GetKind() == TRUE;
  else
    result.value =
        CONSTANTBV::BitVector_bit_test(leaf.GetBVConst(), bit) != 0;
  return result;
}

struct ClauseTerm
{
  bool constant = false;
  bool value = false;
  int literal = -1;

  static ClauseTerm constantValue(bool value_)
  {
    ClauseTerm term;
    term.constant = true;
    term.value = value_;
    return term;
  }
  static ClauseTerm satLiteral(int literal_)
  {
    ClauseTerm term;
    term.literal = literal_;
    return term;
  }
};

ClauseTerm exclusionLiteral(const BitOperand& operand, bool assignment)
{
  if (operand.constant)
    return ClauseTerm::constantValue(operand.value != assignment);
  return ClauseTerm::satLiteral(
      static_cast<int>(2 * operand.variable + (assignment ? 1 : 0)));
}

void addGuardedClause(SATSolver& solver,
                      const std::vector<ClauseTerm>& terms,
                      int guardLiteral)
{
  SATSolver::vec_literals clause;
  for (const ClauseTerm& term : terms)
  {
    if (term.constant)
    {
      if (term.value)
        return; // tautology
      continue;
    }
    clause.push(SATSolver::mkLit(term.literal >> 1,
                                 (term.literal & 1) != 0));
  }
  if (guardLiteral >= 0)
    clause.push(SATSolver::mkLit(guardLiteral >> 1,
                                 (guardLiteral & 1) != 0));
  solver.addClause(clause);
}

// Fully reify one bit equality with the four XNOR truth-table clauses. The
// same routine is the mandatory explicit Bool path and each BV bit's helper.
int encodeBitEquality(SATSolver& solver, const BitOperand& left,
                      const BitOperand& right, int guardLiteral)
{
  const unsigned q = solver.newVar();
  solver.setFrozen(q);
  for (unsigned lv = 0; lv < 2; ++lv)
    for (unsigned rv = 0; rv < 2; ++rv)
      for (unsigned qv = 0; qv < 2; ++qv)
      {
        if ((qv != 0) == (lv == rv))
          continue;
        std::vector<ClauseTerm> clause;
        clause.push_back(exclusionLiteral(left, lv != 0));
        clause.push_back(exclusionLiteral(right, rv != 0));
        clause.push_back(ClauseTerm::satLiteral(
            static_cast<int>(2 * q + (qv != 0 ? 1 : 0))));
        addGuardedClause(solver, clause, guardLiteral);
      }
  return static_cast<int>(2 * q);
}

int equalityLiteral(SATSolver& solver,
                    const ToSATBase::ASTNodeToSATVar& bindings,
                    const UFEqualityAtom& atom, int guardLiteral,
                    std::map<EqualityKey, int>& cache)
{
  const EqualityKey key = equalityKey(atom.left, atom.right, atom.sort);
  const std::map<EqualityKey, int>::const_iterator hit = cache.find(key);
  if (hit != cache.end())
    return hit->second;

  const unsigned width = scalarWidth(atom.sort);
  std::vector<int> bitEqualities;
  bitEqualities.reserve(width);
  for (unsigned bit = 0; bit < width; ++bit)
  {
    const BitOperand left = bitOperand(key.left, atom.sort, bit, bindings);
    const BitOperand right = bitOperand(key.right, atom.sort, bit, bindings);
    bitEqualities.push_back(
        encodeBitEquality(solver, left, right, guardLiteral));
  }

  int result = bitEqualities[0];
  if (bitEqualities.size() > 1)
  {
    const unsigned q = solver.newVar();
    solver.setFrozen(q);
    result = static_cast<int>(2 * q);
    for (const int bitEquality : bitEqualities)
    {
      std::vector<ClauseTerm> clause;
      clause.push_back(ClauseTerm::satLiteral(result ^ 1));
      clause.push_back(ClauseTerm::satLiteral(bitEquality));
      addGuardedClause(solver, clause, guardLiteral);
    }
    std::vector<ClauseTerm> reverse;
    reverse.push_back(ClauseTerm::satLiteral(result));
    for (const int bitEquality : bitEqualities)
      reverse.push_back(ClauseTerm::satLiteral(bitEquality ^ 1));
    addGuardedClause(solver, reverse, guardLiteral);
  }
  cache.insert(std::make_pair(key, result));
  return result;
}

void encodeLemma(MutableAdapterState& state, SATSolver& solver,
                 ToSATBase* tosat, int guardLiteral,
                 std::map<EqualityKey, int>& cache)
{
  if (!state.pending || tosat == NULL)
    FatalError("UF lemma encoding began without a pending certificate");
  ToSATBase::ASTNodeToSATVar& bindings =
      tosat->SATVar_to_SymbolIndexMap();
  validateLemmaBeforeMutation(state.pendingLemma, bindings, solver,
                              guardLiteral);

  std::vector<ClauseTerm> body;
  body.reserve(state.pendingLemma.premise.size() + 1);
  for (const UFEqualityAtom& premise : state.pendingLemma.premise)
  {
    const int q = equalityLiteral(solver, bindings, premise, guardLiteral,
                                  cache);
    body.push_back(ClauseTerm::satLiteral(q ^ 1));
  }
  const int conclusion = equalityLiteral(
      solver, bindings, state.pendingLemma.conclusion, guardLiteral, cache);
  body.push_back(ClauseTerm::satLiteral(conclusion));
  addGuardedClause(solver, body, guardLiteral);
  // Some backends detect at insertion time that this validated blocking
  // clause closes the entire instance.  That is a normal refinement outcome:
  // leave the solver in its UNSAT state so the coordinator's next solve can
  // certify it, rather than misclassifying progress as an internal error.
  state.pending = false;
  state.pendingLemma = UFAbstractLemma();
  state.emittedLemmaCount++;
}

bool lookupCertified(const MutableAdapterState& state,
                     const ASTNode& durableHandle, UFConcreteValue& value)
{
  if (!state.certified)
    return false;
  const std::map<ASTNode, UFConcreteValue>::const_iterator found =
      state.handleValues.find(durableHandle);
  if (found == state.handleValues.end())
    return false;
  value = found->second;
  return true;
}

} // namespace

class UFBatchAdapter::Impl
{
public:
  explicit Impl(STPMgr* manager) : state(manager) {}
  MutableAdapterState state;
  std::map<EqualityKey, int> equalityCache;
};

UFBatchAdapter::UFBatchAdapter(STPMgr* manager) : impl_(new Impl(manager))
{
  assert(manager != NULL);
}
UFBatchAdapter::~UFBatchAdapter() = default;
void UFBatchAdapter::beginQuery(const LoweredApplicationView* view)
{
  clear();
  impl_->state.view = view;
}
void UFBatchAdapter::clear()
{
  impl_->state.clearActive();
  impl_->equalityCache.clear();
}
bool UFBatchAdapter::active() const
{
  return impl_->state.view != NULL && impl_->state.view->active();
}
UFCandidateOutcome UFBatchAdapter::checkCandidate(
    AbsRefine_CounterExample& counterexample)
{
  return checkOneCandidate(impl_->state, counterexample);
}
bool UFBatchAdapter::hasPendingLemma() const { return impl_->state.pending; }
void UFBatchAdapter::encodePendingLemma(SATSolver& solver, ToSATBase* tosat)
{
  encodeLemma(impl_->state, solver, tosat, -1, impl_->equalityCache);
}
bool UFBatchAdapter::hasCertifiedModel() const
{
  return impl_->state.certified;
}
void UFBatchAdapter::invalidateCertifiedModel()
{
  impl_->state.certified = false;
  impl_->state.seed = UFFunctionModelSeedSet();
  impl_->state.handleValues.clear();
}
const UFFunctionModelSeedSet* UFBatchAdapter::certifiedModelSeed() const
{
  return impl_->state.certified ? &impl_->state.seed : NULL;
}
bool UFBatchAdapter::lookupCertifiedApplication(
    const ASTNode& durableHandle, UFConcreteValue& value) const
{
  return lookupCertified(impl_->state, durableHandle, value);
}
const LoweredApplicationView* UFBatchAdapter::applicationView() const
{
  return impl_->state.view;
}
const std::string& UFBatchAdapter::diagnostic() const
{
  return impl_->state.diagnostic;
}
uint64_t UFBatchAdapter::candidateChecks() const
{
  return impl_->state.candidateCheckCount;
}
uint64_t UFBatchAdapter::lemmasEmitted() const
{
  return impl_->state.emittedLemmaCount;
}

class UFPersistentAdapter::Impl
{
public:
  explicit Impl(STPMgr* manager) : state(manager) {}
  MutableAdapterState state;
  PersistentScopeKey activeScope;
  int positiveBlockLiteral = -1;
  std::map<PersistentScopeKey, std::map<EqualityKey, int>> equalityCaches;
};

UFPersistentAdapter::UFPersistentAdapter(STPMgr* manager)
    : impl_(new Impl(manager))
{
  assert(manager != NULL);
}
UFPersistentAdapter::~UFPersistentAdapter() = default;
void UFPersistentAdapter::beginBlock(const LoweredApplicationView* view,
                                     uint64_t epoch, uint64_t blockId,
                                     int positiveBlockLiteral)
{
  impl_->state.clearRound();
  impl_->state.view = view;
  impl_->activeScope.epoch = epoch;
  impl_->activeScope.block = blockId;
  impl_->positiveBlockLiteral = positiveBlockLiteral;
}
void UFPersistentAdapter::clearActiveBlock()
{
  impl_->state.clearActive();
  impl_->positiveBlockLiteral = -1;
}
void UFPersistentAdapter::clearEncodingEpoch()
{
  clearActiveBlock();
  impl_->equalityCaches.clear();
}
void UFPersistentAdapter::invalidateCertifiedModel()
{
  impl_->state.certified = false;
  impl_->state.seed = UFFunctionModelSeedSet();
  impl_->state.handleValues.clear();
}
bool UFPersistentAdapter::active() const
{
  return impl_->state.view != NULL && impl_->state.view->active() &&
         impl_->positiveBlockLiteral >= 0;
}
UFCandidateOutcome UFPersistentAdapter::checkCandidate(
    AbsRefine_CounterExample& counterexample)
{
  return checkOneCandidate(impl_->state, counterexample);
}
bool UFPersistentAdapter::hasPendingLemma() const
{
  return impl_->state.pending;
}
void UFPersistentAdapter::encodePendingLemma(SATSolver& solver,
                                             ToSATBase* tosat)
{
  if (!active())
    FatalError("persistent UF lemma has no active block scope");
  std::map<EqualityKey, int>& cache =
      impl_->equalityCaches[impl_->activeScope];
  encodeLemma(impl_->state, solver, tosat,
              impl_->positiveBlockLiteral ^ 1, cache);
}
bool UFPersistentAdapter::hasCertifiedModel() const
{
  return impl_->state.certified;
}
const UFFunctionModelSeedSet* UFPersistentAdapter::certifiedModelSeed() const
{
  return impl_->state.certified ? &impl_->state.seed : NULL;
}
bool UFPersistentAdapter::lookupCertifiedApplication(
    const ASTNode& durableHandle, UFConcreteValue& value) const
{
  return lookupCertified(impl_->state, durableHandle, value);
}
const LoweredApplicationView* UFPersistentAdapter::applicationView() const
{
  return impl_->state.view;
}
const std::string& UFPersistentAdapter::diagnostic() const
{
  return impl_->state.diagnostic;
}
uint64_t UFPersistentAdapter::candidateChecks() const
{
  return impl_->state.candidateCheckCount;
}
uint64_t UFPersistentAdapter::lemmasEmitted() const
{
  return impl_->state.emittedLemmaCount;
}

} // namespace stp
