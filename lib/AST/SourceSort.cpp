#include "stp/AST/SourceSort.h"

namespace stp
{

std::string sourceSortToSMTLib(const SourceSort& sort)
{
  switch (sort.kind())
  {
    case SourceSort::Kind::Bool:
      return "Bool";
    case SourceSort::Kind::BitVector:
      return "(_ BitVec " + std::to_string(sort.bitVectorWidth()) + ")";
    case SourceSort::Kind::FloatingPoint:
      return "(_ FloatingPoint " + std::to_string(sort.exponentWidth()) +
             " " + std::to_string(sort.significandWidth()) + ")";
    case SourceSort::Kind::RoundingMode:
      return "RoundingMode";
    case SourceSort::Kind::Array:
      return "(Array " + sourceSortToSMTLib(sort.index()) + " " +
             sourceSortToSMTLib(sort.element()) + ")";
    case SourceSort::Kind::Unknown:
      return "Unknown";
  }
  return "Unknown";
}

} // namespace stp
