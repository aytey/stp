#include "stp/UninterpretedFunctions/UFChecker.h"
#include "extlib-constbv/constantbv.h"
#include <algorithm>
#include <map>
#include <set>

namespace stp
{

namespace
{

bool supportedSort(const SourceSort& sort)
{
  return sort.kind() == SourceSort::Kind::Bool ||
         (sort.kind() == SourceSort::Kind::BitVector &&
          sort.bitVectorWidth() > 0);
}

size_t byteWidth(const SourceSort& sort)
{
  return sort.kind() == SourceSort::Kind::Bool
             ? 1
             : (sort.bitVectorWidth() + 7) / 8;
}

int compareSort(const SourceSort& left, const SourceSort& right)
{
  const int lk = left.kind() == SourceSort::Kind::Bool ? 0 : 1;
  const int rk = right.kind() == SourceSort::Kind::Bool ? 0 : 1;
  if (lk != rk)
    return lk < rk ? -1 : 1;
  if (lk == 0)
    return 0;
  if (left.bitVectorWidth() == right.bitVectorWidth())
    return 0;
  return left.bitVectorWidth() < right.bitVectorWidth() ? -1 : 1;
}

bool readScalar(const ASTNode& scalar, const SourceSort& expected,
                const UFScalarCandidate& candidate, UFConcreteValue& value,
                std::string& diagnostic)
{
  if (scalar.IsNull() ||
      (scalar.GetKind() != SYMBOL && !scalar.isConstant()) ||
      scalar.GetSourceSort() != expected)
  {
    diagnostic = "UFCHK scalar is not a canonical leaf of the expected "
                 "SourceSort";
    return false;
  }
  if (scalar.isConstant())
    return UFConcreteValue::fromConstant(scalar, expected, value, diagnostic);
  if (!candidate.read(scalar, expected, value, diagnostic))
    return false;
  if (value.sort() != expected)
  {
    diagnostic = "UFCHK candidate returned a value at the wrong SourceSort";
    return false;
  }
  return true;
}

struct Observation
{
  const LoweredApplicationRecord* record = NULL;
  UFConcreteValue result;
};

} // namespace

UFConcreteValue UFConcreteValue::boolean(bool value)
{
  UFConcreteValue out;
  out.sort_ = SourceSort::boolean();
  out.bytes_.push_back(value ? 1 : 0);
  return out;
}

UFConcreteValue UFConcreteValue::bitVector(
    unsigned width, const std::vector<uint8_t>& bytes)
{
  assert(width > 0);
  UFConcreteValue out;
  out.sort_ = SourceSort::bitVector(width);
  out.bytes_ = bytes;
  out.bytes_.resize((width + 7) / 8, 0);
  if (out.bytes_.size() > (width + 7) / 8)
    out.bytes_.resize((width + 7) / 8);
  const unsigned used = width % 8;
  if (used != 0)
    out.bytes_.back() &= static_cast<uint8_t>((1u << used) - 1u);
  return out;
}

UFConcreteValue UFConcreteValue::fromUInt(unsigned width, uint64_t value)
{
  std::vector<uint8_t> bytes((width + 7) / 8, 0);
  for (size_t i = 0; i < bytes.size() && i < sizeof(value); ++i)
    bytes[i] = static_cast<uint8_t>((value >> (8 * i)) & 0xffu);
  return bitVector(width, bytes);
}

UFConcreteValue UFConcreteValue::zero(const SourceSort& sort)
{
  if (sort.kind() == SourceSort::Kind::Bool)
    return boolean(false);
  assert(sort.kind() == SourceSort::Kind::BitVector &&
         sort.bitVectorWidth() > 0);
  return bitVector(sort.bitVectorWidth(),
                   std::vector<uint8_t>(byteWidth(sort), 0));
}

bool UFConcreteValue::fromConstant(const ASTNode& constant,
                                   const SourceSort& sort,
                                   UFConcreteValue& value,
                                   std::string& diagnostic)
{
  if (!supportedSort(sort))
  {
    diagnostic = "UFCHK constant was requested at an unsupported SourceSort";
    return false;
  }
  if (constant.GetSourceSort() != sort)
  {
    diagnostic = "UFCHK constant does not match its expected SourceSort";
    return false;
  }
  if (sort.kind() == SourceSort::Kind::Bool)
  {
    if (constant.GetKind() != TRUE && constant.GetKind() != FALSE)
    {
      diagnostic = "UFCHK expected a concrete Boolean value";
      return false;
    }
    value = boolean(constant.GetKind() == TRUE);
    return true;
  }
  if (constant.GetKind() != BVCONST ||
      constant.GetValueWidth() != sort.bitVectorWidth())
  {
    diagnostic = "UFCHK expected a concrete bit-vector value";
    return false;
  }
  std::vector<uint8_t> bytes(byteWidth(sort), 0);
  const CBV bits = constant.GetBVConst();
  for (unsigned i = 0; i < sort.bitVectorWidth(); ++i)
    if (CONSTANTBV::BitVector_bit_test(bits, i))
      bytes[i / 8] |= static_cast<uint8_t>(1u << (i % 8));
  value = bitVector(sort.bitVectorWidth(), bytes);
  return true;
}

bool UFConcreteValue::booleanValue() const
{
  assert(sort_.kind() == SourceSort::Kind::Bool && bytes_.size() == 1);
  return bytes_[0] != 0;
}

bool operator==(const UFConcreteValue& left, const UFConcreteValue& right)
{
  return left.sort_ == right.sort_ && left.bytes_ == right.bytes_;
}

bool operator<(const UFConcreteValue& left, const UFConcreteValue& right)
{
  const int sortOrder = compareSort(left.sort_, right.sort_);
  if (sortOrder != 0)
    return sortOrder < 0;
  // Numeric order: compare the most significant byte first.
  return std::lexicographical_compare(left.bytes_.rbegin(), left.bytes_.rend(),
                                      right.bytes_.rbegin(),
                                      right.bytes_.rend());
}

UFCheckResult UFChecker::check(
    const std::vector<const UFDecl*>& activeDeclarations,
    const LoweredApplicationView& view, const UFScalarCandidate& candidate)
{
  UFCheckResult out;
  const uint64_t candidateVersion = candidate.version();
  out.modelSeed.candidateVersion = candidateVersion;
  out.stats.activeApplications = view.applications.size();

  std::vector<const UFDecl*> declarations = activeDeclarations;
  std::sort(declarations.begin(), declarations.end(),
            [](const UFDecl* left, const UFDecl* right)
            {
              if (left == NULL || right == NULL)
                return left < right;
              return left->id() < right->id();
            });
  if (std::find(declarations.begin(), declarations.end(), nullptr) !=
      declarations.end())
  {
    out.diagnostic = "UFCHK received a null active declaration";
    return out;
  }
  if (std::adjacent_find(declarations.begin(), declarations.end()) !=
      declarations.end())
  {
    out.diagnostic = "UFCHK received a duplicate active declaration";
    return out;
  }
  for (size_t i = 1; i < declarations.size(); ++i)
  {
    if (declarations[i - 1]->id() == declarations[i]->id())
    {
      out.diagnostic = "UFCHK received duplicate declaration identities";
      return out;
    }
    if (declarations[i - 1]->owner() != declarations[i]->owner())
    {
      out.diagnostic = "UFCHK active declarations cross manager ownership";
      return out;
    }
  }
  out.stats.functions = declarations.size();

  std::map<const UFDecl*, std::vector<const LoweredApplicationRecord*>> byDecl;
  std::set<ASTNode> handles;
  size_t previousOrder = 0;
  bool firstRecord = true;
  for (const LoweredApplicationRecord& record : view.applications)
  {
    if (record.declaration == NULL || record.durableHandle.IsNull() ||
        record.resultSymbol.IsNull() ||
        record.durableHandle.GetKind() != UF_APPLY ||
        record.resultSymbol.GetKind() != SYMBOL ||
        !record.durableHandle.IsOwnedBy(record.declaration->owner()) ||
        !record.resultSymbol.IsOwnedBy(record.declaration->owner()) ||
        record.loweredActuals.size() != record.declaration->signature().arity() ||
        record.namedActuals.size() != record.declaration->signature().arity())
    {
      out.diagnostic = "UFCHK received a malformed lowered application view";
      return out;
    }
    if (!firstRecord && record.stableOrder <= previousOrder)
    {
      out.diagnostic = "UFCHK application order is not strictly stable";
      return out;
    }
    firstRecord = false;
    previousOrder = record.stableOrder;
    if (!handles.insert(record.durableHandle).second)
    {
      out.diagnostic = "UFCHK received a duplicate durable application";
      return out;
    }
    const std::vector<const UFDecl*>::const_iterator declarationIt =
        std::lower_bound(declarations.begin(), declarations.end(),
                         record.declaration,
                         [](const UFDecl* left, const UFDecl* right)
                         { return left->id() < right->id(); });
    if (declarationIt == declarations.end() ||
        *declarationIt != record.declaration)
    {
      out.diagnostic = "UFCHK view references an inactive declaration";
      return out;
    }
    const UFSignature& signature = record.declaration->signature();
    if (record.resultSymbol.GetSourceSort() != signature.codomain())
    {
      out.diagnostic = "UFCHK result symbol has the wrong SourceSort";
      return out;
    }
    for (size_t i = 0; i < signature.arity(); ++i)
    {
      if (record.loweredActuals[i].IsNull() ||
          record.namedActuals[i].IsNull() ||
          !record.loweredActuals[i].IsOwnedBy(record.declaration->owner()) ||
          !record.namedActuals[i].IsOwnedBy(record.declaration->owner()) ||
          record.loweredActuals[i].GetSourceSort() != signature.domain()[i] ||
          record.namedActuals[i].GetSourceSort() != signature.domain()[i] ||
          (record.namedActuals[i].GetKind() != SYMBOL &&
           !record.namedActuals[i].isConstant()))
      {
        out.diagnostic = "UFCHK argument record is not a typed canonical "
                         "scalar pair";
        return out;
      }
    }
    const ASTNodeMap::const_iterator resultIt =
        view.handleToResult.find(record.durableHandle);
    if (resultIt == view.handleToResult.end() ||
        resultIt->second != record.resultSymbol)
    {
      out.diagnostic = "UFCHK durable-handle result mapping is inconsistent";
      return out;
    }
    byDecl[record.declaration].push_back(&record);
  }

  size_t conflictOrder = 0;
  for (const UFDecl* declaration : declarations)
  {
    if (!supportedSort(declaration->signature().codomain()))
    {
      out.diagnostic = "UFCHK active declaration has an unsupported codomain";
      return out;
    }
    for (const SourceSort& sort : declaration->signature().domain())
      if (!supportedSort(sort))
      {
        out.diagnostic = "UFCHK active declaration has an unsupported domain";
        return out;
      }

    std::map<UFConcreteTuple, Observation> table;
    const std::vector<const LoweredApplicationRecord*>& records =
        byDecl[declaration];
    for (const LoweredApplicationRecord* record : records)
    {
      UFConcreteTuple tuple;
      tuple.reserve(record->namedActuals.size());
      for (size_t i = 0; i < record->namedActuals.size(); ++i)
      {
        UFConcreteValue value;
        if (!readScalar(record->namedActuals[i],
                        declaration->signature().domain()[i], candidate,
                        value, out.diagnostic))
          return out;
        tuple.push_back(value);
      }
      UFConcreteValue result;
      if (!readScalar(record->resultSymbol,
                      declaration->signature().codomain(), candidate, result,
                      out.diagnostic))
        return out;

      const std::map<UFConcreteTuple, Observation>::const_iterator found =
          table.find(tuple);
      if (found == table.end())
      {
        Observation observation;
        observation.record = record;
        observation.result = result;
        table.insert(std::make_pair(tuple, observation));
        out.stats.insertions++;
        continue;
      }

      out.stats.comparisons++;
      conflictOrder++;
      if (found->second.result == result)
        continue;

      const LoweredApplicationRecord& representative =
          *found->second.record;
      out.status = UFCheckResult::Status::Conflict;
      out.conflict.declaration = declaration;
      out.conflict.representativeHandle = representative.durableHandle;
      out.conflict.conflictingHandle = record->durableHandle;
      out.conflict.representativeOrder = representative.stableOrder;
      out.conflict.conflictingOrder = record->stableOrder;
      out.conflict.leftResult = representative.resultSymbol;
      out.conflict.rightResult = record->resultSymbol;
      out.conflict.leftResultValue = found->second.result;
      out.conflict.rightResultValue = result;
      if (candidate.version() != candidateVersion)
      {
        out.status = UFCheckResult::Status::InternalError;
        out.diagnostic = "UFCHK candidate changed during one logical check";
        return out;
      }
      out.conflict.candidateVersion = candidateVersion;
      out.conflict.stableConflictOrder = conflictOrder;
      for (size_t i = 0; i < tuple.size(); ++i)
      {
        UFCongruenceArgument argument;
        argument.position = i;
        argument.sort = declaration->signature().domain()[i];
        argument.leftTheory = representative.loweredActuals[i];
        argument.rightTheory = record->loweredActuals[i];
        argument.leftScalar = representative.namedActuals[i];
        argument.rightScalar = record->namedActuals[i];
        argument.concreteValue = tuple[i];
        out.conflict.arguments.push_back(argument);
      }
      return out;
    }

    UFFunctionModelSeed function;
    function.declaration = declaration;
    function.defaultValue =
        UFConcreteValue::zero(declaration->signature().codomain());
    for (const std::pair<const UFConcreteTuple, Observation>& entry : table)
    {
      UFModelCase modelCase;
      modelCase.arguments = entry.first;
      modelCase.result = entry.second.result;
      modelCase.representativeHandle =
          entry.second.record->durableHandle;
      function.cases.push_back(modelCase);
    }
    out.modelSeed.functions.push_back(function);
  }

  if (candidate.version() != candidateVersion)
  {
    out.status = UFCheckResult::Status::InternalError;
    out.diagnostic = "UFCHK candidate changed during one logical check";
    out.modelSeed = UFFunctionModelSeedSet();
    return out;
  }
  out.status = UFCheckResult::Status::Consistent;
  return out;
}

} // namespace stp
