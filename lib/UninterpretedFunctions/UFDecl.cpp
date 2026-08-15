#include "stp/UninterpretedFunctions/UFDecl.h"

namespace stp
{

bool UFSignature::isSupportedSort(const SourceSort& sort)
{
  if (sort.kind() == SourceSort::Kind::Bool)
    return true;
  return sort.kind() == SourceSort::Kind::BitVector &&
         sort.bitVectorWidth() > 0;
}

bool UFSignature::validate(const std::vector<SourceSort>& domain,
                           const SourceSort& codomain, std::string* error)
{
  if (domain.empty())
  {
    if (error != NULL)
      *error = "a zero-arity declaration is an ordinary symbol, not an "
               "uninterpreted function";
    return false;
  }

  for (size_t i = 0; i < domain.size(); ++i)
  {
    if (!isSupportedSort(domain[i]))
    {
      if (error != NULL)
        *error = "unsupported domain sort " +
                 sourceSortToSMTLib(domain[i]) + " at argument " +
                 std::to_string(i) + " (only Bool and nonzero-width "
                 "bit-vector sorts are supported)";
      return false;
    }
  }

  if (!isSupportedSort(codomain))
  {
    if (error != NULL)
      *error = "unsupported result sort " + sourceSortToSMTLib(codomain) +
               " (only Bool and nonzero-width bit-vector sorts are "
               "supported)";
    return false;
  }
  return true;
}

UFSignature::UFSignature(std::vector<SourceSort> domain,
                         SourceSort codomain)
    : domain_(std::move(domain)), codomain_(std::move(codomain))
{
  std::string error;
  if (!validate(domain_, codomain_, &error))
    throw std::invalid_argument(error);
}

} // namespace stp
