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

#ifndef BACKTRACK_H_
#define BACKTRACK_H_

#include <cassert>
#include <cstddef>
#include <unordered_map>
#include <unordered_set>
#include <vector>

// Backtrackable containers for the incremental solver: push is O(1) -- a
// saved watermark -- and pop erases exactly what was added above the
// watermark, never rescanning lower levels. The pattern follows Bitwuzla's
// src/backtrack/: a manager fans push/pop out to every registered
// container, and each container keeps a control stack of saved sizes.
//
// The map and set are insert-only: a key, once inserted, may not be bound
// again while it is live, so pop can undo insertions by erasure alone. That
// is exactly the discipline the incremental solver's stores need -- e.g. the
// level a symbol was first seen at, or a variable's substitution under the
// first-seen rule -- and it keeps the semantics impossible to misuse: there
// is no "the value was overwritten and pop restores the older one" case.

namespace stp
{
namespace backtrack
{

class Backtrackable;

class BacktrackManager
{
public:
  BacktrackManager() {}
  ~BacktrackManager();

  BacktrackManager(const BacktrackManager&) = delete;
  BacktrackManager& operator=(const BacktrackManager&) = delete;

  void push();
  void pop();

  size_t num_levels() const { return d_levels; }

private:
  friend class Backtrackable;
  void registerBacktrackable(Backtrackable* b);
  void unregisterBacktrackable(Backtrackable* b);

  std::vector<Backtrackable*> d_registered;
  size_t d_levels = 0;
};

class Backtrackable
{
public:
  explicit Backtrackable(BacktrackManager* mgr) : d_mgr(mgr)
  {
    if (d_mgr)
    {
      d_mgr->registerBacktrackable(this);
      // A container constructed after some pushes joins at the current
      // level. It is empty right now, so the watermark for every level it
      // missed is zero -- written directly, because a virtual push() cannot
      // reach the derived class from this constructor.
      d_control.assign(d_mgr->num_levels(), 0);
    }
  }

  virtual ~Backtrackable()
  {
    if (d_mgr)
      d_mgr->unregisterBacktrackable(this);
  }

  // The manager holds raw pointers to registered objects.
  Backtrackable(const Backtrackable&) = delete;
  Backtrackable& operator=(const Backtrackable&) = delete;

  virtual void push() = 0;
  virtual void pop() = 0;

protected:
  std::vector<size_t> d_control;

private:
  BacktrackManager* d_mgr;
};

inline BacktrackManager::~BacktrackManager()
{
  // Containers must not outlive their manager; nothing left to do here, but
  // a container destructed later would touch a dangling manager pointer.
  assert(d_registered.empty());
}

inline void BacktrackManager::registerBacktrackable(Backtrackable* b)
{
  d_registered.push_back(b);
}

inline void BacktrackManager::unregisterBacktrackable(Backtrackable* b)
{
  for (size_t i = 0; i < d_registered.size(); i++)
  {
    if (d_registered[i] == b)
    {
      d_registered.erase(d_registered.begin() + i);
      return;
    }
  }
  assert(false && "unregistering a container that was never registered");
}

inline void BacktrackManager::push()
{
  for (Backtrackable* b : d_registered)
    b->push();
  ++d_levels;
}

inline void BacktrackManager::pop()
{
  assert(d_levels > 0);
  for (Backtrackable* b : d_registered)
    b->pop();
  --d_levels;
}

// An append-only vector; pop truncates to the saved size.
template <class T> class vector : public Backtrackable
{
public:
  explicit vector(BacktrackManager* mgr) : Backtrackable(mgr) {}

  void push_back(const T& t) { d_data.push_back(t); }

  void push() override { d_control.push_back(d_data.size()); }

  void pop() override
  {
    assert(!d_control.empty());
    d_data.resize(d_control.back());
    d_control.pop_back();
  }

  size_t size() const { return d_data.size(); }
  bool empty() const { return d_data.empty(); }
  const T& operator[](size_t i) const { return d_data[i]; }

  typename std::vector<T>::const_iterator begin() const
  {
    return d_data.begin();
  }
  typename std::vector<T>::const_iterator end() const { return d_data.end(); }

private:
  std::vector<T> d_data;
};

// An insert-only map: insert() refuses a key that is already bound, so pop
// can undo a level by erasing the keys inserted there.
template <class K, class V, class Hash = std::hash<K>,
          class Eq = std::equal_to<K>>
class unordered_map : public Backtrackable
{
public:
  explicit unordered_map(BacktrackManager* mgr) : Backtrackable(mgr) {}

  // TRUE if the key was inserted; FALSE if it was already bound (and the
  // map is unchanged).
  bool insert(const K& k, const V& v)
  {
    auto inserted = d_map.emplace(k, v);
    if (!inserted.second)
      return false;
    d_trail.push_back(k);
    return true;
  }

  const V* find(const K& k) const
  {
    auto it = d_map.find(k);
    return it == d_map.end() ? nullptr : &it->second;
  }

  bool contains(const K& k) const { return d_map.find(k) != d_map.end(); }
  size_t size() const { return d_map.size(); }

  void push() override { d_control.push_back(d_trail.size()); }

  void pop() override
  {
    assert(!d_control.empty());
    const size_t keep = d_control.back();
    d_control.pop_back();
    while (d_trail.size() > keep)
    {
      d_map.erase(d_trail.back());
      d_trail.pop_back();
    }
  }

private:
  std::unordered_map<K, V, Hash, Eq> d_map;
  std::vector<K> d_trail;
};

// An insert-only set with the same discipline as the map.
template <class T, class Hash = std::hash<T>, class Eq = std::equal_to<T>>
class unordered_set : public Backtrackable
{
public:
  explicit unordered_set(BacktrackManager* mgr) : Backtrackable(mgr) {}

  // TRUE if newly inserted.
  bool insert(const T& t)
  {
    if (!d_set.insert(t).second)
      return false;
    d_trail.push_back(t);
    return true;
  }

  bool contains(const T& t) const { return d_set.find(t) != d_set.end(); }
  size_t size() const { return d_set.size(); }

  void push() override { d_control.push_back(d_trail.size()); }

  void pop() override
  {
    assert(!d_control.empty());
    const size_t keep = d_control.back();
    d_control.pop_back();
    while (d_trail.size() > keep)
    {
      d_set.erase(d_trail.back());
      d_trail.pop_back();
    }
  }

private:
  std::unordered_set<T, Hash, Eq> d_set;
  std::vector<T> d_trail;
};

} // namespace backtrack
} // namespace stp

#endif
