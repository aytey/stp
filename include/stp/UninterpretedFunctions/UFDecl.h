/********************************************************************
 * Typed declaration identities for UFSTP v2.
 ********************************************************************/
#ifndef STP_UFDECL_H
#define STP_UFDECL_H

#include "stp/AST/ASTNode.h"
#include "stp/AST/SourceSort.h"
#include "stp/Util/Attributes.h"
#include <cstdint>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace stp
{

class UFContext;
class STPMgr;

// An immutable, ordered source-language signature. Carrier widths are not a
// substitute for the sorts themselves: Bool has carrier width zero, and
// RoundingMode's 5-bit carrier has thirty-two patterns where the sort has
// five values.
class DLL_PUBLIC UFSignature final
{
public:
  UFSignature(std::vector<SourceSort> domain, SourceSort codomain);

  const std::vector<SourceSort>& domain() const { return domain_; }
  const SourceSort& codomain() const { return codomain_; }
  size_t arity() const { return domain_.size(); }

  // The single admission gate for a signature position. Everything in the UF
  // core -- the checker, the lemma oracle, the CNF encoder, the model printer
  // and BVTypeCheck's UF_APPLY rule -- asks this rather than repeating the
  // sort list, so admitting a sort is one edit rather than six.
  static bool isSupportedSort(const SourceSort& sort);
  // The parenthetical the diagnostics share; kept beside the gate so the two
  // cannot drift.
  static const char* supportedSortsPhrase();
  static bool validate(const std::vector<SourceSort>& domain,
                       const SourceSort& codomain, std::string* error = NULL);

  friend bool operator==(const UFSignature& left, const UFSignature& right)
  {
    return left.domain_ == right.domain_ && left.codomain_ == right.codomain_;
  }
  friend bool operator!=(const UFSignature& left, const UFSignature& right)
  {
    return !(left == right);
  }

private:
  const std::vector<SourceSort> domain_;
  const SourceSort codomain_;
};

// Context-owned immutable declaration identity. Liveness is intentionally
// not stored here: a declaration object remains address-stable until its
// STPMgr dies, while UFContext separately activates/deactivates it as parser
// scopes come and go. That makes stale handles rejectable without dangling.
class DLL_PUBLIC UFDecl final
{
public:
  uint64_t id() const { return id_; }
  const std::string& name() const { return name_; }
  const UFSignature& signature() const { return signature_; }
  const ASTNode& identityNode() const { return identity_; }
  const STPMgr* owner() const { return owner_; }

  UFDecl(const UFDecl&) = delete;
  UFDecl& operator=(const UFDecl&) = delete;

private:
  friend class UFContext;

  UFDecl(STPMgr* owner, uint64_t id, std::string name,
         UFSignature signature, ASTNode identity)
      : owner_(owner), id_(id), name_(std::move(name)),
        signature_(std::move(signature)), identity_(std::move(identity))
  {
  }

  STPMgr* const owner_;
  const uint64_t id_;
  const std::string name_;
  const UFSignature signature_;
  const ASTNode identity_;
};

} // namespace stp

#endif
