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

  // SMT-LIB commands are transactions. Applications built while reducing a
  // command become durable only if the outer command is accepted; a later
  // malformed subexpression rolls back every application first introduced
  // by that command.
  void beginParserCommand();
  void finishParserCommand(bool accepted);

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
  // lowering view itself is adapter-owned; the context retains membership
  // indexes for preprocessing protection and explicit SAT registration.
  void beginSolveProtection();
  void installSolveProtection(const ASTNodeSet& protectedSymbols,
                              const ASTNodeSet& solveScalars);
  void releaseSolveProtection();
  bool activeInSolve() const
  {
    return solveProtectionActive_ && !solveScalars_.empty();
  }
  bool isProtected(const ASTNode& symbol) const;
  bool isSolveScalar(const ASTNode& symbol) const;
  const ASTNodeSet& getProtectedSymbols() const { return protectedSymbols_; }
  const ASTNodeSet& getSolveScalars() const { return solveScalars_; }

  // Only this lexical window lets preprocessing, candidate construction and
  // SAT registration consume the just-installed solve-local indexes.  The
  // lowered view/certified model may outlive it for get-value, without making
  // a later frontend command look like part of the preceding solve.
  class DLL_PUBLIC SolveScope final
  {
  public:
    explicit SolveScope(UFContext* context);
    ~SolveScope();

    SolveScope(const SolveScope&) = delete;
    SolveScope& operator=(const SolveScope&) = delete;

  private:
    UFContext* const context_;
  };

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
  std::vector<ASTNode> parserCommandApplications_;
  ASTNodeSet protectedSymbols_;
  ASTNodeSet solveScalars_;
  bool parserCommandActive_ = false;
  bool solveProtectionActive_ = false;
};

} // namespace stp

#endif
