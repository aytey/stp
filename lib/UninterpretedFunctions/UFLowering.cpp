#include "stp/UninterpretedFunctions/UFLowering.h"
#include "stp/Globals/Globals.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include <algorithm>

namespace stp
{

namespace
{

bool nodeNumberLess(const ASTNode& left, const ASTNode& right)
{
  return left.GetNodeNum() < right.GetNodeNum();
}

// A heap-backed walk: completed roots may contain input-controlled nesting
// depths, so lowering must not recurse on the C++ stack.
ASTVec reachableApplications(const ASTNode& root)
{
  ASTNodeSet visited;
  ASTNodeSet applications;
  ASTVec pending(1, root);
  while (!pending.empty())
  {
    const ASTNode current = pending.back();
    pending.pop_back();
    if (!visited.insert(current).second)
      continue;
    if (current.GetKind() == UF_APPLY)
      applications.insert(current);
    for (size_t i = current.Degree(); i > 0; --i)
      pending.push_back(current[i - 1]);
  }

  ASTVec ordered(applications.begin(), applications.end());
  std::sort(ordered.begin(), ordered.end(), nodeNumberLess);
  return ordered;
}

bool isLeafActual(const ASTNode& actual)
{
  return actual.GetKind() == SYMBOL || actual.isConstant();
}

ASTNode rewriteKnownApplications(const ASTNode& root,
                                 ASTNodeMap& handleToResult,
                                 STPMgr* manager)
{
  if (handleToResult.empty())
    return root;
  ASTNodeMap cache;
  return SubstitutionMap::replace(root, handleToResult, cache,
                                  manager->defaultNodeFactory);
}

} // namespace

ASTNode
LoweredApplicationView::semanticRootWithDefinitions(STPMgr* manager) const
{
  assert(manager != NULL);
  if (namingDefinitions.empty())
    return semanticRoot;
  ASTVec conjuncts;
  conjuncts.reserve(namingDefinitions.size() + 1);
  conjuncts.push_back(semanticRoot);
  conjuncts.insert(conjuncts.end(), namingDefinitions.begin(),
                   namingDefinitions.end());
  return manager->defaultNodeFactory->CreateNode(AND, conjuncts);
}

UFLowering::UFLowering(STPMgr* manager) : manager_(manager)
{
  assert(manager_ != NULL);
}

LoweredApplicationView
UFLowering::lowerCompletedRoot(const ASTNode& publicRoot,
                               const UFSolveScope& scope) const
{
  if (publicRoot.IsNull() || !publicRoot.IsOwnedBy(manager_))
    FatalError("UF lowering requires a completed root owned by its context");

  LoweredApplicationView view;
  view.scope = scope;
  view.publicRoot = publicRoot;
  view.semanticRoot = publicRoot;

  UFContext* context = manager_->getUFContextIfAny();
  if (!manager_->UserFlags.enable_uninterpreted_functions)
  {
    if (context != NULL)
      context->releaseSolveProtection();
    return view;
  }

  if (context == NULL)
  {
    if (containsKind(publicRoot, UF_APPLY))
      FatalError("UF lowering found UF_APPLY without a manager context",
                 publicRoot);
    return view;
  }
  context->beginSolveProtection();

  const ASTVec applications = reachableApplications(publicRoot);
  if (applications.empty())
  {
    context->installSolveProtection(view.protectedSymbols);
    return view;
  }

  // A name is canonical per lowered expression, matching the reference
  // oracle. This both avoids redundant definitions and makes an identical
  // persistent block reconstruct the identical semantic root.
  ASTNodeMap scalarNames;

  for (const ASTNode& application : applications)
  {
    std::string diagnostic;
    if (!context->isRegisteredApplication(application) ||
        !context->validateApplicationChildren(application.GetChildren(),
                                              &diagnostic))
      FatalError(("UF lowering rejected a malformed durable application: " +
                  diagnostic)
                     .c_str(),
                 application);
    if (!context->isActiveApplication(application))
      FatalError("UF lowering rejected a stale or inactive durable "
                 "application",
                 application);

    const UFDecl* declaration = context->lookupIdentity(application[0]);
    if (declaration == NULL)
      FatalError("UF lowering could not recover declaration identity",
                 application);

    LoweredApplicationRecord record;
    record.durableHandle = application;
    record.declaration = declaration;
    record.scope = scope;
    record.stableOrder = view.applications.size();
    record.loweredActuals.reserve(application.Degree() - 1);
    record.namedActuals.reserve(application.Degree() - 1);

    for (size_t i = 1; i < application.Degree(); ++i)
    {
      const ASTNode lowered = rewriteKnownApplications(
          application[i], view.handleToResult, manager_);
      if (containsKind(lowered, UF_APPLY))
        FatalError("UF lowering order did not lower a nested application "
                   "before its parent",
                   application);
      const SourceSort& expected = declaration->signature().domain()[i - 1];
      if (application[i].GetSourceSort() != expected ||
          lowered.GetSourceSort() != expected)
        FatalError("UF lowering crossed a SourceSort boundary", application);
      record.loweredActuals.push_back(lowered);

      if (isLeafActual(lowered))
      {
        record.namedActuals.push_back(lowered);
        // A source symbol is already its own canonical scalar name, but it
        // still participates in future direct-CNF lemmas. Protect/register it
        // exactly like an introduced name so ordinary preprocessing cannot
        // substitute it away and leave the lemma talking about an unlinked
        // fresh SAT value. Constants need no mapping or protection.
        if (lowered.GetKind() == SYMBOL)
          view.protectedSymbols.insert(lowered);
        continue;
      }

      ASTNode name;
      const ASTNodeMap::const_iterator found = scalarNames.find(lowered);
      if (found != scalarNames.end())
        name = found->second;
      else
      {
        name = manager_->CreateDeterministicSourceVariable(
            expected, "uf_arg", lowered);
        if (name.GetSourceSort() != expected)
          FatalError("UF lowering allocated an argument name at the wrong "
                     "SourceSort",
                     name);
        scalarNames.insert(std::make_pair(lowered, name));
        view.nameToTerm.insert(std::make_pair(name, lowered));
        view.protectedSymbols.insert(name);
        view.namingDefinitions.push_back(
            manager_->defaultNodeFactory->CreateNode(
                expected.kind() == SourceSort::Kind::Bool ? IFF : EQ, name,
                lowered));
      }
      record.namedActuals.push_back(name);
    }

    const SourceSort& codomain = declaration->signature().codomain();
    if (application.GetSourceSort() != codomain)
      FatalError("UF lowering found a durable result with the wrong "
                 "SourceSort",
                 application);
    record.resultSymbol = manager_->CreateDeterministicSourceVariable(
        codomain, "uf_result", application);
    if (record.resultSymbol.GetSourceSort() != codomain)
      FatalError("UF lowering allocated a result at the wrong SourceSort",
                 record.resultSymbol);
    view.protectedSymbols.insert(record.resultSymbol);
    view.handleToResult.insert(
        std::make_pair(application, record.resultSymbol));
    view.applications.push_back(record);
  }

  view.semanticRoot =
      rewriteKnownApplications(publicRoot, view.handleToResult, manager_);
  if (containsKind(view.semanticRoot, UF_APPLY))
    FatalError("UF_APPLY crossed the completed-root lowering barrier",
               view.semanticRoot);

  context->installSolveProtection(view.protectedSymbols);
  return view;
}

} // namespace stp
