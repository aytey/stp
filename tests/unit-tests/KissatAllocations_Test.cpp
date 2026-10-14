/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: October, 2026
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

#include "KissatAllocations.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <limits>
#include <vector>

using Owner = stp::detail::KissatAllocations;

namespace
{
std::size_t liveBlocks(const Owner& owner)
{
  std::size_t count = 0;
  const Owner::Block* previous = nullptr;
  for (const Owner::Block* block = owner.blocks; block; block = block->next)
  {
    EXPECT_EQ(block->previous, previous);
    previous = block;
    ++count;
  }
  return count;
}
} // namespace

TEST(KissatAllocations, PayloadsAreAlignedAndUnlinkedInAnyOrder)
{
  Owner owner;
  std::vector<void*> pointers;
  for (std::size_t bytes = 0; bytes != 129; ++bytes)
  {
    void* ptr = Owner::allocate(&owner, bytes);
    ASSERT_NE(ptr, nullptr);
    EXPECT_EQ(reinterpret_cast<std::uintptr_t>(ptr) % alignof(std::max_align_t),
              0u);
    std::memset(ptr, 0x5a, bytes);
    pointers.push_back(ptr);
  }
  EXPECT_EQ(liveBlocks(owner), pointers.size());
  // Remove the head, tail and interior entries while their neighbours live.
  for (std::size_t i : {128u, 0u, 64u})
  {
    Owner::deallocate(&owner, pointers[i]);
    pointers[i] = nullptr;
  }
  EXPECT_EQ(liveBlocks(owner), 126u);
  for (void* ptr : pointers)
    Owner::deallocate(&owner, ptr);
  EXPECT_EQ(owner.blocks, nullptr);
  EXPECT_FALSE(owner.failed);
}

TEST(KissatAllocations, ResizePreservesPayloadAndOwnership)
{
  Owner owner;
  void* tail = Owner::allocate(&owner, 17);
  void* middle = Owner::resize(&owner, nullptr, 19);
  void* head = Owner::allocate(&owner, 23);
  for (void** pointer : {&head, &middle, &tail})
  {
    auto* ptr = static_cast<unsigned char*>(*pointer);
    std::memset(ptr, 0xa5, 16);
    for (std::size_t bytes : {1048576u, 16u, 4194304u, 0u})
    {
      ptr = static_cast<unsigned char*>(Owner::resize(&owner, ptr, bytes));
      EXPECT_EQ(liveBlocks(owner), 3u);
      EXPECT_EQ(reinterpret_cast<std::uintptr_t>(ptr) %
                    alignof(std::max_align_t),
                0u);
      for (std::size_t i = 0; i != std::min(bytes, std::size_t(16)); ++i)
        EXPECT_EQ(ptr[i], 0xa5);
    }
    *pointer = ptr;
  }
  // The owner also cleans up blocks a partial solver did not release.
  EXPECT_FALSE(owner.failed);
}

TEST(KissatAllocations, FailedResizeKeepsTheOriginalOwnedBlock)
{
  Owner owner;
  auto* ptr = static_cast<unsigned char*>(Owner::allocate(&owner, 32));
  std::memset(ptr, 0x6b, 32);
  EXPECT_THROW(
      Owner::resize(&owner, ptr, std::numeric_limits<std::size_t>::max()),
      std::bad_alloc);
  EXPECT_TRUE(owner.failed);
  EXPECT_EQ(liveBlocks(owner), 1u);
  for (std::size_t i = 0; i != 32; ++i)
    EXPECT_EQ(ptr[i], 0x6b);
  EXPECT_THROW(Owner::allocate(&owner, std::numeric_limits<std::size_t>::max()),
               std::bad_alloc);
  EXPECT_EQ(liveBlocks(owner), 1u);
}
