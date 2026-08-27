/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#include "stp/STPManager/UserDefinedFlags.h"

#include <cctype>
#include <ostream>
#include <sstream>
#include <vector>

namespace stp
{
namespace
{

const char* const GROUP_NAMES[] = {"base",
                                   "udiv15",
                                   "udiv-extra",
                                   "urem",
                                   "mul8",
                                   "mul-ref3",
                                   "mul-extra",
                                   "add",
                                   "quotient-thresholds",
                                   "low-prefix",
                                   "quotient-one-rem",
                                   "divrem-pair",
                                   "quotient-one-quot",
                                   "divisor-magnitude",
                                   "divrem-full",
                                   "udiv-observed"};

static_assert(sizeof(GROUP_NAMES) / sizeof(GROUP_NAMES[0]) ==
                  BV_SCHEMA_GROUP_COUNT,
              "BV schema group names are out of step with the enum");

std::string trim(const std::string& text)
{
  size_t first = 0;
  while (first < text.size() &&
         std::isspace(static_cast<unsigned char>(text[first])))
    ++first;
  size_t last = text.size();
  while (last > first &&
         std::isspace(static_cast<unsigned char>(text[last - 1])))
    --last;
  return text.substr(first, last - first);
}

std::string expectedGroups()
{
  std::ostringstream out;
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
  {
    if (i != 0)
      out << ", ";
    out << GROUP_NAMES[i];
  }
  out << ", udiv, mul6, quotient-one, divrem-prefix, divrem-identity, all, or "
         "none";
  return out.str();
}

bool groupAliasMask(const std::string& token, uint32_t& aliasMask)
{
  if (token == "udiv")
    aliasMask = bvSchemaGroupBit(BVSchemaGroup::UDIV15) |
                bvSchemaGroupBit(BVSchemaGroup::UDIV_OBSERVED);
  else if (token == "mul6")
    aliasMask = bvSchemaGroupBit(BVSchemaGroup::MUL_REF3);
  else if (token == "quotient-one")
    aliasMask = bvSchemaGroupBit(BVSchemaGroup::QUOTIENT_ONE_REM) |
                bvSchemaGroupBit(BVSchemaGroup::QUOTIENT_ONE_QUOT);
  else if (token == "divrem-prefix")
    aliasMask = bvSchemaGroupBit(BVSchemaGroup::DIVREM_PAIR);
  else if (token == "divrem-identity")
    aliasMask = bvSchemaGroupBit(BVSchemaGroup::DIVREM_FULL);
  else
    return false;
  return true;
}

} // namespace

const char* bvSchemaGroupName(BVSchemaGroup group)
{
  const unsigned index = static_cast<unsigned>(group);
  return index < BV_SCHEMA_GROUP_COUNT ? GROUP_NAMES[index] : "unknown";
}

bool parseBVSchemaGroups(const std::string& text, uint32_t& mask,
                         std::string& error)
{
  std::vector<std::string> tokens;
  size_t begin = 0;
  while (begin <= text.size())
  {
    const size_t comma = text.find(',', begin);
    const size_t end = comma == std::string::npos ? text.size() : comma;
    const std::string token = trim(text.substr(begin, end - begin));
    if (token.empty())
    {
      error = "empty BV schema group; expected " + expectedGroups();
      return false;
    }
    tokens.push_back(token);
    if (comma == std::string::npos)
      break;
    begin = comma + 1;
  }

  if (tokens.size() != 1 && (tokens[0] == "all" || tokens[0] == "none"))
  {
    error = "'all' and 'none' must be used alone";
    return false;
  }
  for (size_t i = 1; i < tokens.size(); ++i)
    if (tokens[i] == "all" || tokens[i] == "none")
    {
      error = "'all' and 'none' must be used alone";
      return false;
    }

  if (tokens.size() == 1 && tokens[0] == "all")
  {
    mask = BV_SCHEMA_GROUP_ALL;
    error.clear();
    return true;
  }
  if (tokens.size() == 1 && tokens[0] == "none")
  {
    mask = 0;
    error.clear();
    return true;
  }

  uint32_t parsed = 0;
  for (const std::string& token : tokens)
  {
    bool found = false;
    for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
      if (token == GROUP_NAMES[i])
      {
        parsed |= bvSchemaGroupBit(static_cast<BVSchemaGroup>(i));
        found = true;
        break;
      }
    uint32_t aliasMask = 0;
    if (!found && groupAliasMask(token, aliasMask))
    {
      parsed |= aliasMask;
      found = true;
    }
    if (!found)
    {
      error = "unknown BV schema group '" + token + "'; expected " +
              expectedGroups();
      return false;
    }
  }

  mask = parsed;
  error.clear();
  return true;
}

std::string formatBVSchemaGroups(uint32_t mask)
{
  if (mask == 0)
    return "none";
  if (mask == BV_SCHEMA_GROUP_ALL)
    return "all";

  std::ostringstream out;
  bool first = true;
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
    if (bvSchemaGroupEnabled(mask, static_cast<BVSchemaGroup>(i)))
    {
      if (!first)
        out << ',';
      out << GROUP_NAMES[i];
      first = false;
    }
  return out.str();
}

bool parseBVTermAbstractionProfile(const std::string& text, uint32_t& mask,
                                   unsigned& rounds, std::string& error)
{
  uint32_t parsedMask;
  unsigned parsedRounds;
  if (text == "qualified")
  {
    parsedMask = BV_SCHEMA_GROUP_QUALIFIED;
    parsedRounds = BV_TERM_ABSTRACTION_QUALIFIED_ROUNDS;
  }
  else if (text == "aggressive")
  {
    parsedMask = BV_SCHEMA_GROUP_AGGRESSIVE;
    parsedRounds = BV_TERM_ABSTRACTION_AGGRESSIVE_ROUNDS;
  }
  else if (text == "spear" || text == "broad-no-pair")
  {
    parsedMask = BV_SCHEMA_GROUP_SPEAR;
    parsedRounds = BV_TERM_ABSTRACTION_SPEAR_ROUNDS;
  }
  else if (text == "broad-prefix" || text == "klee")
  {
    parsedMask = BV_SCHEMA_GROUP_BROAD_PREFIX;
    parsedRounds = BV_TERM_ABSTRACTION_BROAD_PREFIX_ROUNDS;
  }
  else
  {
    error = "unknown BV term-abstraction profile '" + text +
            "'; expected qualified, aggressive, spear, or broad-prefix";
    return false;
  }

  mask = parsedMask;
  rounds = parsedRounds;
  error.clear();
  return true;
}

void printAbstractionCoverage(const UserDefinedFlags& uf, std::ostream& out)
{
  const UserDefinedFlags::EncodingCoverage& c = uf.coverage;
  // In AbstractionKind order; a kind added there needs a name here.
  static const char* kindNames[] = {"eq",   "compare", "ite",
                                    "plus", "mult",    "divmod"};
  static_assert(sizeof(kindNames) / sizeof(kindNames[0]) ==
                    UserDefinedFlags::EncodingCoverage::KINDS,
                "abstraction kind names are out of step with the counters");

  out << "Abstraction coverage (candidates -> abstracted):";
  for (unsigned i = 0; i < UserDefinedFlags::EncodingCoverage::KINDS; ++i)
    out << " " << kindNames[i] << "=" << c.bv_candidates[i] << "->"
        << c.bv_abstracted[i];
  out << std::endl
      << "Abstraction refinement: rounds=" << c.bv_refinement_rounds
      << " blocking=" << c.bv_blocking_lemmas
      << " schema=" << c.bv_schema_lemmas
      << " exact=" << c.bv_exact_escalations
      << " exact-mult=" << c.bv_exact_escalations_mult
      << " exact-divmod=" << c.bv_exact_escalations_divmod
      << " exact-clauses=" << c.bv_exact_clauses
      << " exact-vars=" << c.bv_exact_variables
      << " exact-us=" << c.bv_exact_microseconds << std::endl;

  // Preserve Codex's always-present partition: a zero says that an enabled
  // family fired nothing, and can be interpreted alongside the selected mask.
  out << "Abstraction schemas by group:";
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
    out << " " << bvSchemaGroupName(static_cast<BVSchemaGroup>(i)) << "="
        << c.bv_schema_group_lemmas[i];
  out << std::endl;
}

} // namespace stp
