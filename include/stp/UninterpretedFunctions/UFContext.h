/********************************************************************
 * Manager-owned declaration and durable-application registry.
 ********************************************************************/
#ifndef STP_UFCONTEXT_H
#define STP_UFCONTEXT_H

#include "stp/AST/AST.h"
#include "stp/UninterpretedFunctions/UFDecl.h"
#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

namespace stp
{

class STPMgr;

class DLL_PUBLIC UFContext final
{
public:
  explicit UFContext(STPMgr* manager);
  ~UFContext();

  UFContext(const UFContext&) = delete;
  UFContext& operator=(const UFContext&) = delete;

  // Nonfatal public funnel. A failure returns NULL/ASTUndefined, writes a
  // stable diagnostic, and changes no declaration/application registry.
  const UFDecl* declareFunction(const std::string& name,
                                const std::vector<SourceSort>& domain,
                                const SourceSort& codomain,
                                std::string* error = NULL);
  bool deactivate(const UFDecl* decl, std::string* error = NULL);
  void deactivateAll();

  const UFDecl* lookup(const std::string& name) const;
  const UFDecl* lookupIdentity(const ASTNode& identity) const;
  bool isActive(const UFDecl* decl) const;
  bool owns(const UFDecl* decl) const;
  std::vector<const UFDecl*> activeDeclarations() const;

  ASTNode apply(const UFDecl* decl, const ASTVec& actuals,
                std::string* error = NULL);

  // HashingNodeFactory's backstop for rebuilds (define-fun, let and generic
  // substitutions). It validates the immutable signature/context but does not
  // require declaration liveness: a pre-existing durable node may outlive its
  // parser scope and must remain structurally readable as a stale handle.
  bool validateApplicationChildren(ASTChildren children,
                                   std::string* error = NULL) const;
  void noteApplication(const ASTNode& application);
  bool isRegisteredApplication(const ASTNode& application) const;
  bool isActiveApplication(const ASTNode& application) const;

  // Generated lowering scalars are solve-local protected objects. The
  // lowering view itself is adapter-owned; the context retains only this
  // membership index so existing preprocessing components can ask the
  // manager whether a proposed substitution/elimination is legal.
  void beginSolveProtection();
  void installSolveProtection(const ASTNodeSet& protectedSymbols);
  void releaseSolveProtection();
  bool activeInSolve() const { return solveProtectionActive_; }
  bool isProtected(const ASTNode& symbol) const;
  const ASTNodeSet& getProtectedSymbols() const { return protectedSymbols_; }

  size_t declarationCount() const { return declarations_.size(); }
  size_t activeDeclarationCount() const { return activeByName_.size(); }
  size_t registeredApplicationCount() const { return applications_.size(); }
  STPMgr* manager() const { return manager_; }

private:
  void setError(std::string* error, const std::string& message) const;

  STPMgr* const manager_;
  uint64_t nextDeclarationId_ = 0;
  std::vector<std::unique_ptr<UFDecl>> declarations_;
  std::map<std::string, const UFDecl*> activeByName_;
  std::map<uint64_t, const UFDecl*> allById_;
  std::map<ASTNode, const UFDecl*> byIdentity_;
  std::set<const UFDecl*> owned_;
  ASTNodeSet applications_;
  ASTNodeSet protectedSymbols_;
  bool solveProtectionActive_ = false;
};

} // namespace stp

#endif
