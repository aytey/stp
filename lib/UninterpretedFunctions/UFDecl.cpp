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
      *error = "uninterpreted-function declarations must have a non-empty "
               "domain; zero-arity declare-fun is an ordinary symbol";
    return false;
  }

  for (size_t i = 0; i < domain.size(); ++i)
  {
    if (!isSupportedSort(domain[i]))
    {
      if (error != NULL)
        *error = "uninterpreted-function domain sort " +
                 std::to_string(i) + " must be Bool or a non-empty BitVec";
      return false;
    }
  }

  if (!isSupportedSort(codomain))
  {
    if (error != NULL)
      *error = "uninterpreted-function codomain must be Bool or a non-empty "
               "BitVec";
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
