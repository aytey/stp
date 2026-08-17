#include "stp/AST/SourceSort.h"
#include <mutex>
#include <vector>

namespace stp
{

namespace
{

// The declared-sort name table. Process-global, append-only, never recycled;
// see registerUninterpretedSort in the header for why each of those three is
// forced rather than chosen. Guarded by a mutex because a manager per thread
// is a supported use and declare-sort is a parse-time event, so contention is
// a handful of locks per query.
struct UninterpretedSortNames
{
  std::mutex guard;
  std::vector<std::string> byId; // index 0 unused: id 0 means "not a sort"
};

UninterpretedSortNames& sortNames()
{
  static UninterpretedSortNames names;
  return names;
}

} // namespace

SourceSort registerUninterpretedSort(const std::string& name, unsigned width)
{
  UninterpretedSortNames& names = sortNames();
  std::lock_guard<std::mutex> held(names.guard);
  if (names.byId.empty())
    names.byId.push_back(std::string());
  names.byId.push_back(name);
  return SourceSort::uninterpreted((unsigned)(names.byId.size() - 1), width);
}

std::string uninterpretedSortName(unsigned id)
{
  UninterpretedSortNames& names = sortNames();
  std::lock_guard<std::mutex> held(names.guard);
  if (id == 0 || id >= names.byId.size())
    return std::string();
  return names.byId[id];
}

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
    case SourceSort::Kind::Uninterpreted:
    {
      // The name it was declared under. An id this process did not issue
      // cannot be spelled, and saying so is better than printing a carrier
      // width that the sort deliberately is not.
      const std::string name = uninterpretedSortName(sort.uninterpretedId());
      return name.empty() ? "Unknown" : name;
    }
    case SourceSort::Kind::Unknown:
      return "Unknown";
  }
  return "Unknown";
}

} // namespace stp
