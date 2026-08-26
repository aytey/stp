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

// The schema-family mask: its spelling, and what the choosers do with it.
//
// The mask decides nothing about soundness -- every fact behind it is a
// theorem whatever the mask says, and BVAbstractionLemma_Test is where that
// is established. What it decides is which facts are offered, and the thing
// worth checking here is that "offered" and "in an enabled family" are the
// same set: a fact reachable with its family off would make the measurements
// the mask exists to support meaningless.

#include "stp/STPManager/UserDefinedFlags.h"
#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/c_interface.h"

#include <gtest/gtest.h>

#include <string>
#include <vector>

using namespace stp;

namespace
{

std::vector<bool> bitsOf(unsigned value, unsigned width)
{
  std::vector<bool> bits(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

// SMT-LIB's totalised operations, as the unabstracted circuit answers them.
unsigned referenceDiv(unsigned x, unsigned s, unsigned width)
{
  return (s == 0) ? ((1u << width) - 1) : (x / s);
}

unsigned referenceRem(unsigned x, unsigned s, unsigned)
{
  return (s == 0) ? x : (x % s);
}

unsigned referenceMul(unsigned x, unsigned s, unsigned width)
{
  return (x * s) & ((1u << width) - 1);
}

} // namespace

TEST(BVSchemaGroups, every_group_has_a_name_and_the_names_are_distinct)
{
  std::vector<std::string> seen;
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
  {
    const std::string name = bvSchemaGroupName((BVSchemaGroup)i);
    ASSERT_FALSE(name.empty());
    ASSERT_NE(name, "unknown") << "group " << i << " has no name";
    for (const std::string& other : seen)
      ASSERT_NE(name, other) << name << " names two groups";
    seen.push_back(name);
  }
}

// Round-tripping is what makes --help honest: the default the option prints
// is this spelling of the default mask, so a spelling that did not parse
// back would advertise something the parser refuses.
TEST(BVSchemaGroups, format_and_parse_round_trip)
{
  const uint32_t masks[] = {0u, BV_SCHEMA_GROUP_ALL, BV_SCHEMA_GROUP_DEFAULT,
                            bvSchemaGroupBit(BVSchemaGroup::UREM),
                            bvSchemaGroupBit(BVSchemaGroup::BASE) |
                                bvSchemaGroupBit(BVSchemaGroup::ADD)};

  for (uint32_t mask : masks)
  {
    uint32_t parsed = ~0u;
    std::string error;
    ASSERT_TRUE(parseBVSchemaGroups(formatBVSchemaGroups(mask), parsed, error))
        << formatBVSchemaGroups(mask) << ": " << error;
    EXPECT_EQ(parsed, mask) << "round trip through '"
                            << formatBVSchemaGroups(mask) << "'";
  }

  // ... and each family alone.
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
  {
    uint32_t parsed = 0;
    std::string error;
    ASSERT_TRUE(
        parseBVSchemaGroups(bvSchemaGroupName((BVSchemaGroup)i), parsed, error))
        << error;
    EXPECT_EQ(parsed, bvSchemaGroupBit((BVSchemaGroup)i));
  }
}

TEST(BVSchemaGroups, aliases_and_whitespace)
{
  uint32_t mask = 0;
  std::string error;

  ASSERT_TRUE(parseBVSchemaGroups("all", mask, error));
  EXPECT_EQ(mask, BV_SCHEMA_GROUP_ALL);

  ASSERT_TRUE(parseBVSchemaGroups("none", mask, error));
  EXPECT_EQ(mask, 0u);

  ASSERT_TRUE(parseBVSchemaGroups("  base , urem ,base", mask, error));
  EXPECT_EQ(mask, bvSchemaGroupBit(BVSchemaGroup::BASE) |
                      bvSchemaGroupBit(BVSchemaGroup::UREM));
}

// A malformed list leaves the caller with what it had. Half a mask is worse
// than no mask: it is a run whose configuration nobody wrote down.
TEST(BVSchemaGroups, a_rejected_list_changes_nothing)
{
  const char* bad[] = {"", "base,", ",base", "nonsense", "base,nonsense",
                       "all,base", "base,none", "none,all"};

  for (const char* text : bad)
  {
    uint32_t mask = BV_SCHEMA_GROUP_DEFAULT;
    std::string error;
    EXPECT_FALSE(parseBVSchemaGroups(text, mask, error))
        << "'" << text << "' was accepted";
    EXPECT_FALSE(error.empty()) << "'" << text << "' failed without saying why";
    EXPECT_EQ(mask, BV_SCHEMA_GROUP_DEFAULT)
        << "'" << text << "' changed the mask on the way out";
  }
}

// The C API publishes the same bits by a different spelling, and a caller
// that ORs the C names has to get the mask the C++ side would.
TEST(BVSchemaGroups, the_c_api_bits_match_the_enum)
{
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_BASE,
            bvSchemaGroupBit(BVSchemaGroup::BASE));
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_UDIV,
            bvSchemaGroupBit(BVSchemaGroup::UDIV));
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_UREM,
            bvSchemaGroupBit(BVSchemaGroup::UREM));
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_MUL6,
            bvSchemaGroupBit(BVSchemaGroup::MUL6));
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_MUL8,
            bvSchemaGroupBit(BVSchemaGroup::MUL8));
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_DIVISOR_MAGNITUDE,
            bvSchemaGroupBit(BVSchemaGroup::DIVISOR_MAGNITUDE));
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_QUOTIENT_ONE,
            bvSchemaGroupBit(BVSchemaGroup::QUOTIENT_ONE));
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_DIVREM_IDENTITY,
            bvSchemaGroupBit(BVSchemaGroup::DIVREM_IDENTITY));
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_UDIV_EXTRA,
            bvSchemaGroupBit(BVSchemaGroup::UDIV_EXTRA));
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_MUL_EXTRA,
            bvSchemaGroupBit(BVSchemaGroup::MUL_EXTRA));
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_ADD,
            bvSchemaGroupBit(BVSchemaGroup::ADD));

  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_ALL, BV_SCHEMA_GROUP_ALL);
  EXPECT_EQ((uint32_t)STP_BV_SCHEMA_GROUP_DEFAULT, BV_SCHEMA_GROUP_DEFAULT);
}

// The claim the mask has to keep, and the only one that matters: a chooser
// never returns a fact whose family is off.
//
// Swept over every four-bit candidate the choosers are ever called on -- one
// whose result already disagrees with its operands -- for each family alone
// and for the empty mask. A fact reachable with its family off would be
// installed in a run that said it was measuring without it.
TEST(BVSchemaGroups, a_disabled_family_is_never_chosen)
{
  const unsigned width = 4;
  const unsigned values = 1u << width;

  for (unsigned g = 0; g <= BV_SCHEMA_GROUP_COUNT; ++g)
  {
    // g == COUNT is the empty mask; below that, that family alone.
    const uint32_t mask =
        (g == BV_SCHEMA_GROUP_COUNT) ? 0u : bvSchemaGroupBit((BVSchemaGroup)g);

    for (unsigned x = 0; x < values; ++x)
      for (unsigned s = 0; s < values; ++s)
        for (unsigned t = 0; t < values; ++t)
        {
          const std::vector<bool> xb = bitsOf(x, width);
          const std::vector<bool> sb = bitsOf(s, width);
          const std::vector<bool> tb = bitsOf(t, width);

          if (t != referenceMul(x, s, width))
          {
            const MulSchemaChoice choice =
                chooseMulSchema(xb, sb, tb, 0, mask);
            if (choice.schema != MulSchema::None)
              EXPECT_EQ(choice.group, (BVSchemaGroup)g)
                  << "a product fact from " << bvSchemaGroupName(choice.group)
                  << " was offered under mask " << formatBVSchemaGroups(mask);
          }

          if (t != referenceDiv(x, s, width))
          {
            const DivSchemaChoice choice =
                chooseDivSchema(stp::BVDIV, xb, sb, tb, 0, mask);
            if (choice.schema != DivSchema::None)
              EXPECT_EQ(choice.group, (BVSchemaGroup)g)
                  << "a quotient fact from " << bvSchemaGroupName(choice.group)
                  << " was offered under mask " << formatBVSchemaGroups(mask);
          }

          if (t != referenceRem(x, s, width))
          {
            const DivSchemaChoice choice =
                chooseDivSchema(stp::BVMOD, xb, sb, tb, 0, mask);
            if (choice.schema != DivSchema::None)
              EXPECT_EQ(choice.group, (BVSchemaGroup)g)
                  << "a remainder fact from " << bvSchemaGroupName(choice.group)
                  << " was offered under mask " << formatBVSchemaGroups(mask);
          }
        }
  }
}

// ... and the converse, which is what says the partition is a partition:
// under the full mask every wrong candidate that any family can refute is
// refuted by exactly the family that owns the fact, and the group the choice
// reports is one of the eleven rather than a default that happens to be
// BASE.
TEST(BVSchemaGroups, a_choice_reports_the_family_that_owns_the_fact)
{
  const unsigned width = 4;
  const unsigned values = 1u << width;

  bool sawBeyondBase = false;
  for (unsigned x = 0; x < values; ++x)
    for (unsigned s = 0; s < values; ++s)
      for (unsigned t = 0; t < values; ++t)
      {
        const std::vector<bool> xb = bitsOf(x, width);
        const std::vector<bool> sb = bitsOf(s, width);
        const std::vector<bool> tb = bitsOf(t, width);

        if (t != referenceDiv(x, s, width))
        {
          const DivSchemaChoice choice =
              chooseDivSchema(stp::BVDIV, xb, sb, tb, 0, BV_SCHEMA_GROUP_ALL);
          if (choice.schema != DivSchema::None)
          {
            ASSERT_LT((unsigned)choice.group, BV_SCHEMA_GROUP_COUNT);
            // The same fact has to be reachable with only its own family on.
            const DivSchemaChoice alone = chooseDivSchema(
                stp::BVDIV, xb, sb, tb, 0, bvSchemaGroupBit(choice.group));
            EXPECT_NE(alone.schema, DivSchema::None)
                << "a fact charged to " << bvSchemaGroupName(choice.group)
                << " is unreachable with that family on by itself";
            if (choice.group != BVSchemaGroup::BASE)
              sawBeyondBase = true;
          }
        }
      }

  EXPECT_TRUE(sawBeyondBase)
      << "no quotient fact outside base was ever chosen, so this test is "
         "not checking what it claims to";
}
