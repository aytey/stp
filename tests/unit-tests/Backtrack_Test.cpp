/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "stp/Incremental/Backtrack.h"
#include <gtest/gtest.h>
#include <string>

using namespace stp::backtrack;

TEST(Backtrack, vector_truncates_to_the_pushed_size)
{
  BacktrackManager mgr;
  vector<int> v(&mgr);

  v.push_back(1);
  mgr.push();
  v.push_back(2);
  v.push_back(3);
  mgr.push();
  v.push_back(4);

  ASSERT_EQ(4u, v.size());
  mgr.pop();
  ASSERT_EQ(3u, v.size());
  EXPECT_EQ(3, v[2]);
  mgr.pop();
  ASSERT_EQ(1u, v.size());
  EXPECT_EQ(1, v[0]);
}

TEST(Backtrack, map_erases_only_what_the_level_added)
{
  BacktrackManager mgr;
  unordered_map<std::string, int> m(&mgr);

  ASSERT_TRUE(m.insert("base", 0));
  mgr.push();
  ASSERT_TRUE(m.insert("one", 1));
  // Insert-only: rebinding a live key is refused and changes nothing.
  ASSERT_FALSE(m.insert("base", 99));
  mgr.push();
  ASSERT_TRUE(m.insert("two", 2));

  ASSERT_EQ(3u, m.size());
  mgr.pop();
  EXPECT_FALSE(m.contains("two"));
  EXPECT_TRUE(m.contains("one"));
  mgr.pop();
  EXPECT_FALSE(m.contains("one"));
  ASSERT_NE(nullptr, m.find("base"));
  EXPECT_EQ(0, *m.find("base"));

  // A popped key may be inserted again, at the new level.
  ASSERT_TRUE(m.insert("one", 10));
  EXPECT_EQ(10, *m.find("one"));
}

TEST(Backtrack, set_round_trips_through_pop)
{
  BacktrackManager mgr;
  unordered_set<int> s(&mgr);

  ASSERT_TRUE(s.insert(1));
  mgr.push();
  ASSERT_TRUE(s.insert(2));
  ASSERT_FALSE(s.insert(1));
  mgr.pop();
  EXPECT_FALSE(s.contains(2));
  EXPECT_TRUE(s.contains(1));
  ASSERT_TRUE(s.insert(2));
  EXPECT_TRUE(s.contains(2));
}

TEST(Backtrack, late_registration_replays_the_current_level)
{
  BacktrackManager mgr;
  mgr.push();
  mgr.push();

  // Constructed two levels in: joins at the current level, so the pops
  // below stay balanced.
  vector<int> v(&mgr);
  v.push_back(1);

  mgr.pop();
  EXPECT_EQ(0u, v.size());
  mgr.pop();
  EXPECT_EQ(0u, v.size());
  EXPECT_EQ(0u, mgr.num_levels());
}

TEST(Backtrack, empty_levels_cost_nothing_and_balance)
{
  BacktrackManager mgr;
  unordered_map<int, int> m(&mgr);
  ASSERT_TRUE(m.insert(1, 1));

  for (int i = 0; i < 100; i++)
    mgr.push();
  for (int i = 0; i < 100; i++)
    mgr.pop();

  EXPECT_EQ(1u, m.size());
  EXPECT_EQ(0u, mgr.num_levels());
}
