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

// The per-family block that follows it. Only where it starts is pinned:
// what a caller compiles in is the ordinal of the family it reads, and the
// whole block moves together if this one does. Where it ends is not pinned
// on purpose -- a family appended to BVSchemaGroup extends the block, and
// that is the one change to it that breaks nobody.
//
// An insertion *into* the block is the change that would, and it is caught
// without naming every member: vc_getCounter indexes the coverage array by
// `counter - STP_COUNTER_BV_SCHEMA_BASE`, and asserts there that the span
// from BASE to the last family is exactly BV_SCHEMA_GROUP_COUNT wide. A
// family inserted rather than appended fails that assertion.
static_assert(STP_COUNTER_BV_SCHEMA_BASE == 18,
              "the per-family schema counters must start where they always "
              "have");

// ... and ifaceflag_t, which is the same ABI and the same rule, pinned the
// same way.
//
// It was not pinned before, and a flag was inserted into the middle of it --
// twice, past a review that added the assertions above and reasoned about
// append-versus-insert while doing so. What the counter enum had and this
// one did not was a test. So this one names ordinals rather than asserting
// an ordering between two of them: an ordering is satisfied by an insertion
// anywhere below it, which is exactly what happened.
//
// A published flag whose number moves silently redirects a caller compiled
// against an older header to a different flag. There is no diagnostic for
// it and no way for the caller to notice.
static_assert(BV_TERM_ABSTRACTION_MULT == 21,
              "the published BV term abstraction flag ordinal changed");
static_assert(BV_TERM_ABSTRACTION_VALUE_DIVISOR == 24,
              "an interface flag was inserted, not appended");
static_assert(CNF_GENERATION_EFFORT == 26,
              "an interface flag was inserted, not appended");
static_assert(INCREMENTAL_PIECE_REWRITING == 28,
              "an interface flag was inserted, not appended");
static_assert(CNF_AUTO_THRESHOLD == 29,
              "an interface flag was inserted, not appended");

// The two this branch appends. Their own ordinals are pinned as well, so
// that a later flag has to go after them rather than between them.
static_assert(BV_TERM_ABSTRACTION_SCHEMA_GROUPS == 30,
              "new interface flags must be appended, not inserted");
static_assert(BV_TERM_ABSTRACTION_DIVMOD == 31,
              "new interface flags must be appended, not inserted");

TEST(c_counter_enum_abi, PublishedCounterOrdinalsRemainStable)
{
  EXPECT_EQ(15, static_cast<int>(STP_COUNTER_UF_APPLICATIONS_LOWERED));
  EXPECT_EQ(16, static_cast<int>(STP_COUNTER_UF_CONSTRAINTS_INSTALLED));
  EXPECT_EQ(17, static_cast<int>(STP_COUNTER_BV_SCHEMA_LEMMAS));
  EXPECT_EQ(18, static_cast<int>(STP_COUNTER_BV_SCHEMA_BASE));
}

static_assert(STP_COUNTER_BV_EXACT_ESCALATIONS == 33,
              "the escalation counters must follow the per-family block");

TEST(c_counter_enum_abi, PublishedInterfaceFlagOrdinalsRemainStable)
{
  EXPECT_EQ(21, static_cast<int>(BV_TERM_ABSTRACTION_MULT));
  EXPECT_EQ(24, static_cast<int>(BV_TERM_ABSTRACTION_VALUE_DIVISOR));
  EXPECT_EQ(26, static_cast<int>(CNF_GENERATION_EFFORT));
  EXPECT_EQ(28, static_cast<int>(INCREMENTAL_PIECE_REWRITING));
  EXPECT_EQ(29, static_cast<int>(CNF_AUTO_THRESHOLD));
  EXPECT_EQ(30, static_cast<int>(BV_TERM_ABSTRACTION_SCHEMA_GROUPS));
  EXPECT_EQ(31, static_cast<int>(BV_TERM_ABSTRACTION_DIVMOD));
}
