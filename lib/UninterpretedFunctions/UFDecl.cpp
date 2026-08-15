#include "stp/UninterpretedFunctions/UFDecl.h"

namespace stp
{

const char* UFSignature::supportedSortsPhrase()
{
  return "only Bool, RoundingMode and nonzero-width bit-vector sorts are "
         "supported";
}

bool UFSignature::isSupportedSort(const SourceSort& sort)
{
  // RoundingMode joins Bool and BitVec because its carrier's bit-equality is
  // its own equality: each of the five modes is exactly one 5-bit one-hot
  // pattern, so nothing in the checker or the lemma encoder has to learn a
  // second notion of "equal". What it does need is the pin -- see
  // UFLowering::lowerCompletedRoot -- because the carrier has thirty-two
  // patterns and the sort has five.
  if (sort.kind() == SourceSort::Kind::Bool ||
      sort.kind() == SourceSort::Kind::RoundingMode)
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
                 std::to_string(i) + " (" + supportedSortsPhrase() + ")";
      return false;
    }
  }

  if (!isSupportedSort(codomain))
  {
    if (error != NULL)
      *error = "unsupported result sort " + sourceSortToSMTLib(codomain) +
               " (" + supportedSortsPhrase() + ")";
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
