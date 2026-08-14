#include "stp/UninterpretedFunctions/UFLemma.h"
#include <set>

namespace stp
{

namespace
{

struct EqualityKey
{
  ASTNode left;
  ASTNode right;
  SourceSort sort;

  bool operator<(const EqualityKey& other) const
  {
    if (sort.kind() != other.sort.kind())
      return static_cast<int>(sort.kind()) <
             static_cast<int>(other.sort.kind());
    if (sort.kind() == SourceSort::Kind::BitVector &&
        sort.bitVectorWidth() != other.sort.bitVectorWidth())
      return sort.bitVectorWidth() < other.sort.bitVectorWidth();
    if (left != other.left)
      return left < other.left;
    return right < other.right;
  }
};

EqualityKey keyFor(ASTNode left, ASTNode right, const SourceSort& sort)
{
  if (right < left)
    std::swap(left, right);
  EqualityKey key;
  key.left = left;
  key.right = right;
  key.sort = sort;
  return key;
}

bool supported(const SourceSort& sort)
{
  return sort.kind() == SourceSort::Kind::Bool ||
         (sort.kind() == SourceSort::Kind::BitVector &&
          sort.bitVectorWidth() > 0);
}

} // namespace

bool UFAbstractLemma::evaluate(
    bool conclusionEquality,
    const std::vector<bool>& premiseEqualities) const
{
  if (premiseEqualities.size() != premise.size())
    return false;
  bool premiseValue = true;
  for (const bool value : premiseEqualities)
    premiseValue = premiseValue && value;
  return !premiseValue || conclusionEquality;
}

bool UFLemmaOracle::buildAndValidate(const UFCongruenceConflict& conflict,
                                     UFAbstractLemma& lemma,
                                     std::string& diagnostic)
{
  lemma = UFAbstractLemma();
  diagnostic.clear();
  if (conflict.declaration == NULL || conflict.leftResult.IsNull() ||
      conflict.rightResult.IsNull() ||
      conflict.leftResultValue == conflict.rightResultValue)
  {
    diagnostic = "UF lemma certificate has no result conflict";
    return false;
  }
  const SourceSort& codomain = conflict.declaration->signature().codomain();
  if (!supported(codomain) || conflict.leftResult.GetSourceSort() != codomain ||
      conflict.rightResult.GetSourceSort() != codomain ||
      conflict.leftResultValue.sort() != codomain ||
      conflict.rightResultValue.sort() != codomain)
  {
    diagnostic = "UF lemma certificate has an invalid result sort";
    return false;
  }

  std::set<EqualityKey> seen;
  size_t expectedPosition = 0;
  for (const UFCongruenceArgument& argument : conflict.arguments)
  {
    if (argument.position != expectedPosition++ ||
        argument.position >= conflict.declaration->signature().arity() ||
        argument.sort != conflict.declaration->signature().domain()[argument.position] ||
        argument.concreteValue.sort() != argument.sort ||
        argument.leftTheory.IsNull() || argument.rightTheory.IsNull() ||
        argument.leftTheory.GetSourceSort() != argument.sort ||
        argument.rightTheory.GetSourceSort() != argument.sort ||
        argument.leftScalar.IsNull() || argument.rightScalar.IsNull() ||
        argument.leftScalar.GetSourceSort() != argument.sort ||
        argument.rightScalar.GetSourceSort() != argument.sort ||
        (argument.leftScalar.GetKind() != SYMBOL &&
         !argument.leftScalar.isConstant()) ||
        (argument.rightScalar.GetKind() != SYMBOL &&
         !argument.rightScalar.isConstant()))
    {
      diagnostic = "UF lemma certificate has an invalid argument pair";
      return false;
    }

    // Exact identity makes this premise a reflexive true atom. Concrete
    // equality alone is deliberately insufficient to omit it.
    if (argument.leftScalar == argument.rightScalar)
      continue;

    // A constant/constant atom is decided without a SAT circuit. The
    // collided tuple says every premise is true, so unequal constants expose
    // a corrupt certificate; equal constants are canonical `true` and drop.
    if (argument.leftScalar.isConstant() &&
        argument.rightScalar.isConstant())
    {
      UFConcreteValue left;
      UFConcreteValue right;
      if (!UFConcreteValue::fromConstant(argument.leftScalar, argument.sort,
                                         left, diagnostic) ||
          !UFConcreteValue::fromConstant(argument.rightScalar, argument.sort,
                                         right, diagnostic))
        return false;
      if (left != right)
      {
        diagnostic = "UF lemma contains a structurally false constant "
                     "premise";
        return false;
      }
      continue;
    }

    const EqualityKey key = keyFor(argument.leftScalar, argument.rightScalar,
                                   argument.sort);
    if (!seen.insert(key).second)
      continue;

    UFEqualityAtom atom;
    atom.left = key.left;
    atom.right = key.right;
    atom.sort = argument.sort;
    atom.originalPosition = argument.position;
    lemma.premise.push_back(atom);
  }

  const EqualityKey conclusion =
      keyFor(conflict.leftResult, conflict.rightResult, codomain);
  if (conclusion.left == conclusion.right)
  {
    diagnostic = "UF lemma conflict has a reflexive result equality";
    return false;
  }
  lemma.conclusion.left = conclusion.left;
  lemma.conclusion.right = conclusion.right;
  lemma.conclusion.sort = codomain;
  lemma.conclusion.originalPosition = conflict.arguments.size();
  lemma.candidateVersion = conflict.candidateVersion;

  // The tuple collision proves every retained premise true; the distinct
  // result values prove the conclusion false. Evaluate the abstract clause
  // explicitly so validate-before-mutate is exercised in every build mode,
  // with assertions providing an additional debug audit rather than the only
  // enforcement.
  const std::vector<bool> premiseValues(lemma.premise.size(), true);
  if (lemma.evaluate(false, premiseValues))
  {
    diagnostic = "UF lemma does not reject its triggering candidate";
    return false;
  }
  return true;
}

} // namespace stp
