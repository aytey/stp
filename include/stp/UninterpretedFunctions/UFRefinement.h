/********************************************************************
 * Mode-specific UF refinement adapters and shared CNF semantics.
 ********************************************************************/
#ifndef STP_UFREFINEMENT_H
#define STP_UFREFINEMENT_H

#include "stp/UninterpretedFunctions/UFLemma.h"
#include <cstdint>
#include <memory>
#include <string>

namespace stp
{

class AbsRefine_CounterExample;
class SATSolver;
class STPMgr;
class ToSATBase;

enum class UFCandidateOutcome
{
  Skipped,
  Consistent,
  Conflict,
  InternalError
};

// Candidate-coordinator seam used by CallSAT_ResultCheck. Logical checking is
// shared in UFChecker; implementations below deliberately keep all mutable
// cache, clause-lifetime and publication state mode-local.
class DLL_PUBLIC UFTheoryAdapter
{
public:
  virtual ~UFTheoryAdapter() = default;

  virtual bool active() const = 0;
  virtual UFCandidateOutcome
  checkCandidate(AbsRefine_CounterExample& counterexample) = 0;
  virtual bool hasPendingLemma() const = 0;
  // Installs every lemma the last refuted candidate produced. All of them are
  // validated before any of them mutates SAT, so the batch is as atomic as a
  // single clause was.
  virtual void encodePendingLemmas(SATSolver& solver, ToSATBase* tosat) = 0;

  virtual bool hasCertifiedModel() const = 0;
  virtual void invalidateCertifiedModel() = 0;
  virtual const UFFunctionModelSeedSet* certifiedModelSeed() const = 0;
  virtual bool lookupCertifiedApplication(const ASTNode& durableHandle,
                                          UFConcreteValue& value) const = 0;
  virtual const LoweredApplicationView* applicationView() const = 0;
  virtual const std::string& diagnostic() const = 0;
  virtual uint64_t candidateChecks() const = 0;
  virtual uint64_t lemmasEmitted() const = 0;
};

// One fresh-query owner. Clauses and equality literals are intentionally
// unguarded because the SAT instance dies with the query.
class DLL_PUBLIC UFBatchAdapter final : public UFTheoryAdapter
{
public:
  explicit UFBatchAdapter(STPMgr* manager);
  ~UFBatchAdapter() override;

  UFBatchAdapter(const UFBatchAdapter&) = delete;
  UFBatchAdapter& operator=(const UFBatchAdapter&) = delete;

  void beginQuery(const LoweredApplicationView* view);
  void clear();

  bool active() const override;
  UFCandidateOutcome
  checkCandidate(AbsRefine_CounterExample& counterexample) override;
  bool hasPendingLemma() const override;
  void encodePendingLemmas(SATSolver& solver, ToSATBase* tosat) override;
  bool hasCertifiedModel() const override;
  void invalidateCertifiedModel() override;
  const UFFunctionModelSeedSet* certifiedModelSeed() const override;
  bool lookupCertifiedApplication(const ASTNode& durableHandle,
                                  UFConcreteValue& value) const override;
  const LoweredApplicationView* applicationView() const override;
  const std::string& diagnostic() const override;
  uint64_t candidateChecks() const override;
  uint64_t lemmasEmitted() const override;

private:
  class Impl;
  std::unique_ptr<Impl> impl_;
};

// Persistent exact-stack owner. Every helper definition and semantic clause
// carries the negated current block literal. Equality caches are partitioned
// by semantic encoding epoch, SAT-backend generation, and block identity.
// A backend replacement invalidates them even when its AIG epoch survives.
class DLL_PUBLIC UFPersistentAdapter final : public UFTheoryAdapter
{
public:
  explicit UFPersistentAdapter(STPMgr* manager);
  ~UFPersistentAdapter() override;

  UFPersistentAdapter(const UFPersistentAdapter&) = delete;
  UFPersistentAdapter& operator=(const UFPersistentAdapter&) = delete;

  void beginBlock(const LoweredApplicationView* view, uint64_t epoch,
                  uint64_t backendGeneration, uint64_t blockId,
                  int positiveBlockLiteral);
  void advanceBackendGeneration(uint64_t backendGeneration);
  void clearActiveBlock();
  void clearEncodingEpoch();
  void invalidateCertifiedModel() override;

  bool active() const override;
  UFCandidateOutcome
  checkCandidate(AbsRefine_CounterExample& counterexample) override;
  bool hasPendingLemma() const override;
  void encodePendingLemmas(SATSolver& solver, ToSATBase* tosat) override;
  bool hasCertifiedModel() const override;
  const UFFunctionModelSeedSet* certifiedModelSeed() const override;
  bool lookupCertifiedApplication(const ASTNode& durableHandle,
                                  UFConcreteValue& value) const override;
  const LoweredApplicationView* applicationView() const override;
  const std::string& diagnostic() const override;
  uint64_t candidateChecks() const override;
  uint64_t lemmasEmitted() const override;

private:
  class Impl;
  std::unique_ptr<Impl> impl_;
};

} // namespace stp

#endif
