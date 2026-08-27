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

// stp_counter_t is part of the C ABI: callers compile these integers into
// their binaries and may load a newer libstp without recompiling. Keep the
// published prefix fixed and append new counters after it.
#include "stp/c_interface.h"
#include <gtest/gtest.h>

static_assert(STP_COUNTER_UF_APPLICATIONS_LOWERED == 15,
              "the published UF application counter ordinal changed");
static_assert(STP_COUNTER_UF_CONSTRAINTS_INSTALLED == 16,
              "the published UF constraint counter ordinal changed");
static_assert(STP_COUNTER_BV_SCHEMA_LEMMAS == 17,
              "new counters must follow the published counter prefix");
static_assert(STP_COUNTER_BV_SCHEMA_GROUP_BASE == 18,
              "schema-group counters must follow the aggregate");
static_assert(STP_COUNTER_BV_SCHEMA_GROUP_DIVREM_PAIR == 29,
              "schema-group counter block must remain contiguous");
static_assert(STP_COUNTER_BV_SCHEMA_GROUP_DIVREM_FULL == 32,
              "new schema-group counters must be appended");
static_assert(STP_COUNTER_BV_SCHEMA_GROUP_UDIV_OBSERVED == 33,
              "published schema-group counter ordinal changed");
static_assert(STP_COUNTER_BV_EXACT_ESCALATIONS == 34,
              "new counters must be appended");
static_assert(STP_COUNTER_BV_EXACT_ESCALATIONS_DIVMOD == 36,
              "new counter block must remain contiguous");
static_assert(STP_COUNTER_BV_EXACT_CLAUSES == 37,
              "exact-cost counters must be appended");
static_assert(STP_COUNTER_BV_EXACT_VARIABLES == 38,
              "exact-cost counter block must remain contiguous");
static_assert(STP_COUNTER_BV_EXACT_MICROSECONDS == 39,
              "exact-cost counter block must remain contiguous");

TEST(c_counter_enum_abi, PublishedCounterOrdinalsRemainStable)
{
  EXPECT_EQ(15, static_cast<int>(STP_COUNTER_UF_APPLICATIONS_LOWERED));
  EXPECT_EQ(16, static_cast<int>(STP_COUNTER_UF_CONSTRAINTS_INSTALLED));
  EXPECT_EQ(17, static_cast<int>(STP_COUNTER_BV_SCHEMA_LEMMAS));
  EXPECT_EQ(18, static_cast<int>(STP_COUNTER_BV_SCHEMA_GROUP_BASE));
  EXPECT_EQ(29, static_cast<int>(STP_COUNTER_BV_SCHEMA_GROUP_DIVREM_PAIR));
  EXPECT_EQ(32, static_cast<int>(STP_COUNTER_BV_SCHEMA_GROUP_DIVREM_FULL));
  EXPECT_EQ(33, static_cast<int>(STP_COUNTER_BV_SCHEMA_GROUP_UDIV_OBSERVED));
  EXPECT_EQ(34, static_cast<int>(STP_COUNTER_BV_EXACT_ESCALATIONS));
  EXPECT_EQ(36, static_cast<int>(STP_COUNTER_BV_EXACT_ESCALATIONS_DIVMOD));
  EXPECT_EQ(37, static_cast<int>(STP_COUNTER_BV_EXACT_CLAUSES));
  EXPECT_EQ(38, static_cast<int>(STP_COUNTER_BV_EXACT_VARIABLES));
  EXPECT_EQ(39, static_cast<int>(STP_COUNTER_BV_EXACT_MICROSECONDS));
}
