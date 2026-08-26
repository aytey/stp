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

// Central contract for schema-family ownership. Per-operation tests establish
// the meaning of each fact; this file establishes that the public mask, the
// chooser-reported owner, CLI spelling, and C spelling are one partition.

#include "stp/STPManager/UserDefinedFlags.h"
#include "stp/ToSat/BVAbstractionRefiner.h"
#include "stp/c_interface.h"

#include <gtest/gtest.h>

#include <set>
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

} // namespace

TEST(BVSchemaGroups, every_group_has_a_unique_round_tripping_name)
{
  std::set<std::string> names;
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
  {
    const BVSchemaGroup group = static_cast<BVSchemaGroup>(i);
    const std::string name = bvSchemaGroupName(group);
    ASSERT_FALSE(name.empty());
    ASSERT_NE("unknown", name);
    ASSERT_TRUE(names.insert(name).second) << name;

    uint32_t parsed = 0;
    std::string error;
    ASSERT_TRUE(parseBVSchemaGroups(name, parsed, error)) << error;
    EXPECT_EQ(bvSchemaGroupBit(group), parsed);
    EXPECT_EQ(name, formatBVSchemaGroups(parsed));
  }

  const uint32_t masks[] = {0u, BV_SCHEMA_GROUP_ALL, BV_SCHEMA_GROUP_DEFAULT,
                            BV_SCHEMA_GROUP_AGGRESSIVE, BV_SCHEMA_GROUP_SPEAR};
  for (uint32_t mask : masks)
  {
    uint32_t parsed = ~0u;
    std::string error;
    ASSERT_TRUE(parseBVSchemaGroups(formatBVSchemaGroups(mask), parsed, error))
        << error;
    EXPECT_EQ(mask, parsed);
  }
}

TEST(BVSchemaGroups, rejected_lists_are_atomic)
{
  const char* invalid[] = {"",          "base,", " ,base", "nonsense",
                           "all,base", "base,none", "none,all"};
  for (const char* text : invalid)
  {
    uint32_t mask = BV_SCHEMA_GROUP_DEFAULT;
    std::string error;
    EXPECT_FALSE(parseBVSchemaGroups(text, mask, error)) << text;
    EXPECT_EQ(BV_SCHEMA_GROUP_DEFAULT, mask) << text;
    EXPECT_FALSE(error.empty()) << text;
  }
}

TEST(BVSchemaGroups, c_api_bits_and_profiles_match_cpp)
{
  const uint32_t cBits[] = {
      STP_BV_SCHEMA_GROUP_BASE,
      STP_BV_SCHEMA_GROUP_UDIV15,
      STP_BV_SCHEMA_GROUP_UDIV_EXTRA,
      STP_BV_SCHEMA_GROUP_UREM,
      STP_BV_SCHEMA_GROUP_MUL8,
      STP_BV_SCHEMA_GROUP_MUL_REF3,
      STP_BV_SCHEMA_GROUP_MUL_EXTRA,
      STP_BV_SCHEMA_GROUP_ADD,
      STP_BV_SCHEMA_GROUP_QUOTIENT_THRESHOLDS,
      STP_BV_SCHEMA_GROUP_LOW_PREFIX,
      STP_BV_SCHEMA_GROUP_QUOTIENT_ONE_REM,
      STP_BV_SCHEMA_GROUP_DIVREM_PAIR,
      STP_BV_SCHEMA_GROUP_QUOTIENT_ONE_QUOT,
      STP_BV_SCHEMA_GROUP_DIVISOR_MAGNITUDE,
      STP_BV_SCHEMA_GROUP_DIVREM_FULL,
      STP_BV_SCHEMA_GROUP_UDIV_OBSERVED};

  ASSERT_EQ(BV_SCHEMA_GROUP_COUNT, sizeof(cBits) / sizeof(cBits[0]));
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
    EXPECT_EQ(bvSchemaGroupBit(static_cast<BVSchemaGroup>(i)), cBits[i]);

  EXPECT_EQ(BV_SCHEMA_GROUP_QUALIFIED,
            static_cast<uint32_t>(STP_BV_SCHEMA_GROUP_QUALIFIED));
  EXPECT_EQ(BV_SCHEMA_GROUP_AGGRESSIVE,
            static_cast<uint32_t>(STP_BV_SCHEMA_GROUP_AGGRESSIVE));
  EXPECT_EQ(BV_SCHEMA_GROUP_SPEAR,
            static_cast<uint32_t>(STP_BV_SCHEMA_GROUP_SPEAR));
  EXPECT_EQ(BV_SCHEMA_GROUP_ALL,
            static_cast<uint32_t>(STP_BV_SCHEMA_GROUP_ALL));
}

// Sweep every four-bit candidate under each family in isolation. Any chooser
// result must be charged to the only enabled family; reaching a fact owned by
// a different family would invalidate both ablation results and counters.
TEST(BVSchemaGroups, disabled_families_are_never_chosen)
{
  const unsigned width = 4;
  const unsigned values = 1u << width;
  std::vector<bool> sawChoice(BV_SCHEMA_GROUP_COUNT, false);

  for (unsigned g = 0; g <= BV_SCHEMA_GROUP_COUNT; ++g)
  {
    const bool empty = g == BV_SCHEMA_GROUP_COUNT;
    const uint32_t mask =
        empty ? 0u : bvSchemaGroupBit(static_cast<BVSchemaGroup>(g));

    for (unsigned x = 0; x < values; ++x)
      for (unsigned s = 0; s < values; ++s)
        for (unsigned t = 0; t < values; ++t)
        {
          const std::vector<bool> xb = bitsOf(x, width);
          const std::vector<bool> sb = bitsOf(s, width);
          const std::vector<bool> tb = bitsOf(t, width);

          const MulSchemaChoice mul = chooseMulSchema(xb, sb, tb, 0, mask);
          if (mul.schema != MulSchema::None)
          {
            ASSERT_FALSE(empty);
            EXPECT_EQ(static_cast<BVSchemaGroup>(g), mul.group);
            sawChoice[g] = true;
          }

          const AddSchemaChoice add = chooseAddSchema(xb, sb, tb, 0, mask);
          if (add.found)
          {
            ASSERT_FALSE(empty);
            EXPECT_EQ(static_cast<BVSchemaGroup>(g), add.group);
            sawChoice[g] = true;
          }

          for (Kind kind : {stp::BVDIV, stp::BVMOD})
          {
            const DivSchemaChoice div =
                chooseDivSchema(kind, xb, sb, tb, 0, mask);
            if (div.schema != DivSchema::None)
            {
              ASSERT_FALSE(empty);
              EXPECT_EQ(static_cast<BVSchemaGroup>(g), div.group);
              sawChoice[g] = true;
            }
          }
        }
  }

  // Paired relations are scheduled across records and tested by
  // BVDivRemSchema_Test. Every single-record family must be reachable here.
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
  {
    const BVSchemaGroup group = static_cast<BVSchemaGroup>(i);
    if (group == BVSchemaGroup::DIVREM_PAIR ||
        group == BVSchemaGroup::DIVREM_FULL)
      continue;
    EXPECT_TRUE(sawChoice[i]) << bvSchemaGroupName(group);
  }
}

TEST(BVSchemaGroups, spear_profile_excludes_both_paired_relations)
{
  EXPECT_EQ(16u, BV_TERM_ABSTRACTION_SPEAR_ROUNDS);
  EXPECT_FALSE(
      bvSchemaGroupEnabled(BV_SCHEMA_GROUP_SPEAR, BVSchemaGroup::DIVREM_PAIR));
  EXPECT_FALSE(
      bvSchemaGroupEnabled(BV_SCHEMA_GROUP_SPEAR, BVSchemaGroup::DIVREM_FULL));
  EXPECT_TRUE(bvSchemaGroupEnabled(BV_SCHEMA_GROUP_SPEAR,
                                   BVSchemaGroup::QUOTIENT_ONE_REM));
  EXPECT_TRUE(bvSchemaGroupEnabled(BV_SCHEMA_GROUP_SPEAR,
                                   BVSchemaGroup::QUOTIENT_ONE_QUOT));
}
