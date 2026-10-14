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

#ifndef STP_SAT_KISSATALLOCATIONS_H
#define STP_SAT_KISSATALLOCATIONS_H

#include <ankerl/unordered_dense.h>

#include <cstddef>
#include <cstdlib>
#include <limits>
#include <new>

namespace stp
{
namespace detail
{
// Track payloads without an individual ownership-node allocation or a prefix
// that changes the payload's allocation size. Failed C operations still leave
// their live blocks owned so the adapter can discard the unfinished solver.
struct KissatAllocations
{
  ankerl::unordered_dense::set<void*> blocks;
  bool failed = false;

  KissatAllocations() = default;
  KissatAllocations(const KissatAllocations&) = delete;
  KissatAllocations& operator=(const KissatAllocations&) = delete;

  ~KissatAllocations()
  {
    for (void* block : blocks)
      std::free(block);
  }

  static void checkSize(KissatAllocations& self, std::size_t bytes)
  {
    if (bytes == std::numeric_limits<std::size_t>::max())
    {
      self.failed = true;
      throw std::bad_alloc();
    }
  }

  static void* allocate(void* state, std::size_t bytes)
  {
    auto& self = *static_cast<KissatAllocations*>(state);
    checkSize(self, bytes);
    void* block = std::malloc(bytes);
    if (!block)
    {
      if (!bytes)
        return nullptr;
      self.failed = true;
      throw std::bad_alloc();
    }
    try
    {
      self.blocks.insert(block);
    }
    catch (...)
    {
      std::free(block);
      self.failed = true;
      throw;
    }
    return block;
  }

  static void* resize(void* state, void* ptr, std::size_t bytes)
  {
    if (!ptr)
      return allocate(state, bytes);
    auto& self = *static_cast<KissatAllocations*>(state);
    checkSize(self, bytes);
    if (!bytes)
    {
      deallocate(state, ptr);
      return nullptr;
    }
    try
    {
      // Keep a spare metadata slot before moving the payload. Reinsertion
      // after an unsuccessful realloc then needs no additional allocation.
      self.blocks.reserve(self.blocks.size() + 1);
    }
    catch (...)
    {
      self.failed = true;
      throw;
    }
    self.blocks.erase(ptr);
    void* next = std::realloc(ptr, bytes);
    if (!next)
    {
      self.failed = true;
      try
      {
        self.blocks.insert(ptr);
      }
      catch (...)
      {
        // Even an unexpected metadata failure must leave no unowned block.
        std::free(ptr);
        throw;
      }
      throw std::bad_alloc();
    }
    try
    {
      self.blocks.insert(next);
    }
    catch (...)
    {
      std::free(next);
      self.failed = true;
      throw;
    }
    return next;
  }

  static void deallocate(void* state, void* ptr)
  {
    if (!ptr)
      return;
    auto& self = *static_cast<KissatAllocations*>(state);
    self.blocks.erase(ptr);
    std::free(ptr);
  }
};

} // namespace detail
} // namespace stp

#endif
