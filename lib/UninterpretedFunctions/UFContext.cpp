#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/STPManager/STPManager.h"
#include <algorithm>
#include <cctype>
#include <sstream>

namespace stp
{

namespace
{
bool isRenderableExternalName(const std::string& name)
{
  // UF models quote every external declaration name. SMT-LIB quoted symbols
  // have no escape for either delimiter character and admit only printable
  // characters. Rejecting at declaration keeps every later model operation
  // total and nonfatal.
  for (const unsigned char c : name)
    if (c == '|' || c == '\\' || !std::isprint(c))
      return false;
  return true;
}
} // namespace

UFContext::UFContext(STPMgr* manager) : manager_(manager)
{
  assert(manager_ != NULL);
}

UFContext::~UFContext()
{
  releaseSolveProtection();
  applications_.clear();
  byIdentity_.clear();
  activeByName_.clear();
  owned_.clear();
  allById_.clear();
  declarations_.clear();
}

void UFContext::setError(std::string* error, const std::string& message) const
{
  if (error != NULL)
    *error = message;
}

const UFDecl*
UFContext::declareFunction(const std::string& name,
                           const std::vector<SourceSort>& domain,
                           const SourceSort& codomain, std::string* error)
{
  if (!manager_->UserFlags.enable_uninterpreted_functions)
  {
    setError(error, "uninterpreted functions are disabled");
    return NULL;
  }
  if (name.empty())
  {
    setError(error, "uninterpreted-function name must not be empty");
    return NULL;
  }
  if (!isRenderableExternalName(name))
  {
    setError(error, "uninterpreted-function name is not representable as an "
                    "SMT-LIB2 quoted symbol");
    return NULL;
  }
  if (STPMgr::isReservedSymbolName(name.c_str()))
  {
    setError(error, "an uninterpreted-function name beginning with '@' or "
                    "'.' is reserved for solver use");
    return NULL;
  }
  std::string signatureError;
  if (!UFSignature::validate(domain, codomain, &signatureError))
  {
    setError(error, signatureError);
    return NULL;
  }
  if (activeByName_.find(name) != activeByName_.end())
  {
    setError(error, "uninterpreted function '" + name +
                    "' is already declared in the active namespace");
    return NULL;
  }

  const uint64_t id = nextDeclarationId_++;
  std::ostringstream identityName;
  identityName << "@uf_decl_" << id;
  const ASTNode identity =
      manager_->CreateSourceSymbol(identityName.str().c_str(), codomain);
  manager_->noteIntroducedSymbol(identity);

  std::unique_ptr<UFDecl> record(new UFDecl(
      manager_, id, name, UFSignature(domain, codomain), identity));
  const UFDecl* result = record.get();
  declarations_.push_back(std::move(record));
  activeByName_.insert(std::make_pair(name, result));
  allById_.insert(std::make_pair(id, result));
  byIdentity_.insert(std::make_pair(identity, result));
  owned_.insert(result);
  return result;
}

bool UFContext::deactivate(const UFDecl* decl, std::string* error)
{
  if (!owns(decl))
  {
    setError(error, "uninterpreted-function declaration belongs to another "
                    "context or is invalid");
    return false;
  }
  const std::map<std::string, const UFDecl*>::iterator found =
      activeByName_.find(decl->name());
  if (found == activeByName_.end() || found->second != decl)
  {
    setError(error, "uninterpreted-function declaration is no longer active");
    return false;
  }
  activeByName_.erase(found);
  return true;
}

void UFContext::deactivateAll()
{
  activeByName_.clear();
}

const UFDecl* UFContext::lookup(const std::string& name) const
{
  const std::map<std::string, const UFDecl*>::const_iterator found =
      activeByName_.find(name);
  return found == activeByName_.end() ? NULL : found->second;
}

const UFDecl* UFContext::lookupIdentity(const ASTNode& identity) const
{
  if (identity.IsNull() || !identity.IsOwnedBy(manager_))
    return NULL;
  const std::map<ASTNode, const UFDecl*>::const_iterator found =
      byIdentity_.find(identity);
  return found == byIdentity_.end() ? NULL : found->second;
}

bool UFContext::owns(const UFDecl* decl) const
{
  return decl != NULL && owned_.find(decl) != owned_.end();
}

bool UFContext::isActive(const UFDecl* decl) const
{
  if (!owns(decl))
    return false;
  const std::map<std::string, const UFDecl*>::const_iterator found =
      activeByName_.find(decl->name());
  return found != activeByName_.end() && found->second == decl;
}

std::vector<const UFDecl*> UFContext::activeDeclarations() const
{
  std::vector<const UFDecl*> result;
  result.reserve(activeByName_.size());
  for (const std::pair<const std::string, const UFDecl*>& entry :
       activeByName_)
    result.push_back(entry.second);
  std::sort(result.begin(), result.end(),
            [](const UFDecl* left, const UFDecl* right)
            { return left->id() < right->id(); });
  return result;
}

bool UFContext::validateApplicationChildren(ASTChildren children,
                                            std::string* error) const
{
  if (children.size() < 2)
  {
    setError(error, "UF_APPLY requires a declaration identity and at least "
                    "one actual argument");
    return false;
  }
  if (!children[0].IsOwnedBy(manager_))
  {
    setError(error, "UF_APPLY declaration identity belongs to another context");
    return false;
  }
  const UFDecl* decl = lookupIdentity(children[0]);
  if (decl == NULL)
  {
    setError(error, "UF_APPLY child 0 is not a registered declaration identity");
    return false;
  }
  if (children.size() - 1 != decl->signature().arity())
  {
    setError(error, "uninterpreted-function application arity mismatch");
    return false;
  }
  for (size_t i = 1; i < children.size(); ++i)
  {
    if (!children[i].IsOwnedBy(manager_))
    {
      setError(error, "uninterpreted-function actual belongs to another context");
      return false;
    }
    if (children[i].GetSourceSort() != decl->signature().domain()[i - 1])
    {
      setError(error, "uninterpreted-function argument " +
                      std::to_string(i - 1) + " has the wrong source sort");
      return false;
    }
  }
  return true;
}

ASTNode UFContext::apply(const UFDecl* decl, const ASTVec& actuals,
                         std::string* error)
{
  if (!manager_->UserFlags.enable_uninterpreted_functions)
  {
    setError(error, "uninterpreted functions are disabled");
    return manager_->ASTUndefined;
  }
  if (!owns(decl))
  {
    setError(error, "uninterpreted-function declaration belongs to another "
                    "context or is invalid");
    return manager_->ASTUndefined;
  }
  if (!isActive(decl))
  {
    setError(error, "uninterpreted-function declaration is no longer active");
    return manager_->ASTUndefined;
  }

  ASTVec children;
  children.reserve(actuals.size() + 1);
  children.push_back(decl->identityNode());
  children.insert(children.end(), actuals.begin(), actuals.end());
  if (!validateApplicationChildren(children, error))
    return manager_->ASTUndefined;

  const SourceSort& resultSort = decl->signature().codomain();
  ASTNode result;
  if (resultSort.kind() == SourceSort::Kind::Bool)
    result = manager_->defaultNodeFactory->CreateNode(UF_APPLY, children);
  else
    result = manager_->defaultNodeFactory->CreateTerm(
        UF_APPLY, resultSort.bitVectorWidth(), children);
  noteApplication(result);
  return result;
}

void UFContext::noteApplication(const ASTNode& application)
{
  assert(application.GetKind() == UF_APPLY);
  applications_.insert(application);
}

bool UFContext::isRegisteredApplication(const ASTNode& application) const
{
  return !application.IsNull() && application.IsOwnedBy(manager_) &&
         application.GetKind() == UF_APPLY &&
         applications_.find(application) != applications_.end();
}

bool UFContext::isActiveApplication(const ASTNode& application) const
{
  return isRegisteredApplication(application) && application.Degree() >= 1 &&
         isActive(lookupIdentity(application[0]));
}

void UFContext::beginSolveProtection()
{
  protectedSymbols_.clear();
  solveProtectionActive_ = true;
}

void UFContext::installSolveProtection(
    const ASTNodeSet& protectedSymbols)
{
  if (!solveProtectionActive_)
    beginSolveProtection();
  protectedSymbols_ = protectedSymbols;
}

void UFContext::releaseSolveProtection()
{
  protectedSymbols_.clear();
  solveProtectionActive_ = false;
}

bool UFContext::isProtected(const ASTNode& symbol) const
{
  return solveProtectionActive_ && !symbol.IsNull() &&
         symbol.IsOwnedBy(manager_) && symbol.GetKind() == SYMBOL &&
         protectedSymbols_.find(symbol) != protectedSymbols_.end();
}

} // namespace stp
