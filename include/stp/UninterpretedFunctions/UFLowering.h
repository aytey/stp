/********************************************************************
 * Completed-root lowering for durable uninterpreted-function nodes.
 ********************************************************************/
#ifndef STP_UFLOWERING_H
#define STP_UFLOWERING_H

#include "stp/AST/AST.h"
#include "stp/UninterpretedFunctions/UFDecl.h"
#include <cstdint>
#include <map>
#include <vector>

namespace stp
{

class STPMgr;
class UFContext;

// The semantic owner of one lowering. Batch scopes live for one fresh SAT
// query. Persistent scopes identify one exact-stack block in one encoding
// epoch; the block guard is filled by the persistent adapter once encoded.
struct DLL_PUBLIC UFSolveScope
{
  enum class Mode
  {
    Batch,
    Persistent
  };

  Mode mode = Mode::Batch;
  uint64_t id = 0;
  uint64_t epoch = 0;
  ASTNode blockGuard;

  static UFSolveScope batch(uint64_t id_)
  {
    UFSolveScope scope;
    scope.mode = Mode::Batch;
    scope.id = id_;
    return scope;
  }

  static UFSolveScope persistent(uint64_t id_, uint64_t epoch_)
  {
    UFSolveScope scope;
    scope.mode = Mode::Persistent;
    scope.id = id_;
    scope.epoch = epoch_;
    return scope;
  }
};

// One application as seen after all frontend substitution and after nested
// UF applications in its actuals have themselves been lowered.
struct DLL_PUBLIC LoweredApplicationRecord
{
  ASTNode durableHandle;
  const UFDecl* declaration = NULL;
  ASTVec loweredActuals;
  ASTVec namedActuals;
  ASTNode resultSymbol;
  UFSolveScope scope;
  size_t stableOrder = 0;
};

// Value object owned by a solve-mode adapter. It deliberately contains no SAT
// state: M3's checker consumes it as immutable semantic input, while the batch
// and persistent adapters own their distinct clause/cache lifetimes.
class DLL_PUBLIC LoweredApplicationView final
{
public:
  UFSolveScope scope;
  ASTNode publicRoot;
  ASTNode semanticRoot;
  std::vector<LoweredApplicationRecord> applications;
  ASTNodeMap handleToResult;
  ASTNodeMap nameToTerm;
  ASTVec namingDefinitions;
  ASTNodeSet protectedSymbols;

  bool active() const { return !applications.empty(); }
  size_t size() const { return applications.size(); }

  // Attach the query/block-local name definitions to the lowered semantic
  // formula. Result symbols intentionally have no eager UF definition.
  ASTNode semanticRootWithDefinitions(STPMgr* manager) const;
};

class DLL_PUBLIC UFLowering final
{
public:
  explicit UFLowering(STPMgr* manager);

  UFLowering(const UFLowering&) = delete;
  UFLowering& operator=(const UFLowering&) = delete;

  LoweredApplicationView lowerCompletedRoot(const ASTNode& publicRoot,
                                            const UFSolveScope& scope) const;

private:
  STPMgr* const manager_;
};

} // namespace stp

#endif
