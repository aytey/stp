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
#include <sstream>
#include <vector>

namespace stp
{

namespace
{

// In BVSchemaGroup order, which is also the counter order. The static
// assertion below is the whole guard against the two drifting apart.
const char* const GROUP_NAMES[] = {
    "base",   "udiv",       "urem",       "mul6",
    "mul8",   "divisor-magnitude",        "quotient-one",
    "divrem-identity",      "udiv-extra", "mul-extra",
    "add"};

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
  out << ", all, or none";
  return out.str();
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

  // `all` and `none` say something about the whole mask, so a list holding
  // one of them alongside a family name is asking for two different things
  // and is refused rather than resolved by an ordering rule.
  for (const std::string& token : tokens)
    if ((token == "all" || token == "none") && tokens.size() != 1)
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

  // Accumulated apart from `mask` so that a name misspelt halfway down a
  // list leaves the caller with the mask it started with.
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

    if (!found)
    {
      error =
          "unknown BV schema group '" + token + "'; expected " + expectedGroups();
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
  if ((mask & BV_SCHEMA_GROUP_ALL) == BV_SCHEMA_GROUP_ALL)
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

} // namespace stp
