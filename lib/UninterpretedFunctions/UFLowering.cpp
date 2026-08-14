#include "stp/UninterpretedFunctions/UFLowering.h"
#include "stp/Globals/Globals.h"
#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/Util/DagWalk.h"

namespace stp
{

namespace
{
bool isLeafActual(const ASTNode& actual)
{
  return actual.GetKind() == SYMBOL || actual.isConstant();
}

ASTNode rebuildWithChildren(const ASTNode& original,
                            const ASTVec& loweredChildren, STPMgr* manager)
{
  assert(original.Degree() == loweredChildren.size());
  bool changed = false;
  for (size_t i = 0; i < loweredChildren.size(); ++i)
    changed = changed || loweredChildren[i] != original[i];
  if (!changed)
    return original;

  NodeFactory* const factory = manager->defaultNodeFactory;
  ASTNode rebuilt;
  if (original.GetValueWidth() == 0)
    rebuilt = factory->CreateNode(original.GetKind(), loweredChildren);
  else
    // Mirror SubstitutionMap's rebuild funnel: CreateArrayTerm preserves both
    // widths for arrays and is also the width-preserving CreateTerm path for
    // non-Boolean bit-vector terms when the index width is zero.
    rebuilt =
        factory->CreateArrayTerm(original.GetKind(), original.GetIndexWidth(),
                                 original.GetValueWidth(), loweredChildren);

  if (rebuilt.GetSourceSort() != original.GetSourceSort())
    FatalError("UF lowering rebuilt a node at the wrong SourceSort", rebuilt);
  return rebuilt;
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

  // A name is canonical per lowered expression, matching the reference
  // oracle. This both avoids redundant definitions and makes an identical
  // persistent block reconstruct the identical semantic root.
  ASTNodeMap scalarNames;

  // Rewrite the completed root once, bottom-up. The explicit walk keeps its
  // frames on the heap (input controls AST depth), visits each shared DAG node
  // once, and guarantees that a nested UF application has become its scalar
  // result before an enclosing application's actual is recorded.
  DenseNodeMap rewritten;
  view.semanticRoot = postOrderRebuild(
      publicRoot, rewritten,
      [&](const ASTNode& application, const ASTVec& loweredChildren) -> ASTNode
      {
        if (application.GetKind() != UF_APPLY)
          return rebuildWithChildren(application, loweredChildren, manager_);

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
        if (loweredChildren.size() != application.Degree() ||
            loweredChildren.empty() || loweredChildren[0] != application[0])
          FatalError("UF lowering rewrote a declaration identity", application);

        LoweredApplicationRecord record;
        record.durableHandle = application;
        record.declaration = declaration;
        record.scope = scope;
        record.stableOrder = view.applications.size();
        record.loweredActuals.reserve(application.Degree() - 1);
        record.namedActuals.reserve(application.Degree() - 1);

        for (size_t i = 1; i < loweredChildren.size(); ++i)
        {
          const ASTNode& lowered = loweredChildren[i];
          const SourceSort& expected = declaration->signature().domain()[i - 1];
          if (application[i].GetSourceSort() != expected ||
              lowered.GetSourceSort() != expected)
            FatalError("UF lowering crossed a SourceSort boundary",
                       application);
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
            {
              view.protectedSymbols.insert(lowered);
              view.solveScalars.insert(lowered);
            }
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
            view.solveScalars.insert(name);
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
        view.solveScalars.insert(record.resultSymbol);
        view.handleToResult.insert(
            std::make_pair(application, record.resultSymbol));
        view.applications.push_back(record);
        return record.resultSymbol;
      });

  // This checks the whole barrier once, including the naming definitions.
  // Scanning every progressively larger actual separately would turn a
  // linear post-order rewrite back into a quadratic algorithm on shared
  // nested DAGs.
  if (containsKind(view.semanticRootWithDefinitions(manager_), UF_APPLY))
    FatalError("UF_APPLY crossed the completed-root lowering barrier",
               view.semanticRoot);

  context->installSolveProtection(view.protectedSymbols, view.solveScalars);
  return view;
}

} // namespace stp
