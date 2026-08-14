/********************************************************************
 * Pure dynamic-Ackermann consistency checker.
 ********************************************************************/
#ifndef STP_UFCHECKER_H
#define STP_UFCHECKER_H

#include "stp/UninterpretedFunctions/UFLowering.h"
#include <cstdint>
#include <string>
#include <vector>

namespace stp
{

// Normalized, width-aware scalar value. The byte vector is little-endian;
// unused high bits are always zero. It owns no AST or SAT object.
class DLL_PUBLIC UFConcreteValue final
{
public:
  UFConcreteValue() = default;

  static UFConcreteValue boolean(bool value);
  static UFConcreteValue bitVector(unsigned width,
                                   const std::vector<uint8_t>& bytes);
  static UFConcreteValue fromUInt(unsigned width, uint64_t value);
  static UFConcreteValue zero(const SourceSort& sort);
  static bool fromConstant(const ASTNode& constant, const SourceSort& sort,
                           UFConcreteValue& value, std::string& diagnostic);

  const SourceSort& sort() const { return sort_; }
  const std::vector<uint8_t>& bytes() const { return bytes_; }
  bool booleanValue() const;

  friend bool operator==(const UFConcreteValue& left,
                         const UFConcreteValue& right);
  friend bool operator!=(const UFConcreteValue& left,
                         const UFConcreteValue& right)
  {
    return !(left == right);
  }
  friend bool operator<(const UFConcreteValue& left,
                        const UFConcreteValue& right);

private:
  SourceSort sort_;
  std::vector<uint8_t> bytes_;
};

typedef std::vector<UFConcreteValue> UFConcreteTuple;

// Read-only host bridge. Implementations may read a batch model map or a
// persistent totalized assignment, but the checker neither knows nor mutates
// either representation.
class DLL_PUBLIC UFScalarCandidate
{
public:
  virtual ~UFScalarCandidate() = default;
  virtual uint64_t version() const = 0;
  virtual bool read(const ASTNode& scalar, const SourceSort& expected,
                    UFConcreteValue& value,
                    std::string& diagnostic) const = 0;
};

struct DLL_PUBLIC UFCongruenceArgument
{
  size_t position = 0;
  SourceSort sort;
  ASTNode leftTheory;
  ASTNode rightTheory;
  ASTNode leftScalar;
  ASTNode rightScalar;
  UFConcreteValue concreteValue;
};

struct DLL_PUBLIC UFCongruenceConflict
{
  const UFDecl* declaration = NULL;
  ASTNode representativeHandle;
  ASTNode conflictingHandle;
  size_t representativeOrder = 0;
  size_t conflictingOrder = 0;
  std::vector<UFCongruenceArgument> arguments;
  ASTNode leftResult;
  ASTNode rightResult;
  UFConcreteValue leftResultValue;
  UFConcreteValue rightResultValue;
  uint64_t candidateVersion = 0;
  size_t stableConflictOrder = 0;
};

struct DLL_PUBLIC UFModelCase
{
  UFConcreteTuple arguments;
  UFConcreteValue result;
  ASTNode representativeHandle;
};

struct DLL_PUBLIC UFFunctionModelSeed
{
  const UFDecl* declaration = NULL;
  std::vector<UFModelCase> cases;
  UFConcreteValue defaultValue;
};

struct DLL_PUBLIC UFFunctionModelSeedSet
{
  uint64_t candidateVersion = 0;
  std::vector<UFFunctionModelSeed> functions;
};

struct DLL_PUBLIC UFCheckStats
{
  size_t functions = 0;
  size_t activeApplications = 0;
  size_t insertions = 0;
  size_t comparisons = 0;
};

class DLL_PUBLIC UFCheckResult final
{
public:
  enum class Status
  {
    Consistent,
    Conflict,
    InternalError
  };

  Status status = Status::InternalError;
  UFCongruenceConflict conflict;
  UFFunctionModelSeedSet modelSeed;
  UFCheckStats stats;
  std::string diagnostic;

  bool consistent() const { return status == Status::Consistent; }
  bool hasConflict() const { return status == Status::Conflict; }
};

// Stateless logical core. Every candidate table is local to check(), making
// reset across refinement rounds a structural property rather than a caller
// obligation.
class DLL_PUBLIC UFChecker final
{
public:
  static UFCheckResult
  check(const std::vector<const UFDecl*>& activeDeclarations,
        const LoweredApplicationView& view,
        const UFScalarCandidate& candidate);
};

} // namespace stp

#endif
