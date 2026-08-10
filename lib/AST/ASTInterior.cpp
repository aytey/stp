/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
 *
 * BEGIN DATE: November, 2005
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

#include "stp/AST/ASTInterior.h"
#include "stp/STPManager/STPManager.h"
namespace stp
{
/******************************************************************
 * ASTInterior Member Functions                                   *
 ******************************************************************/

// Call this when deleting a node that has been stored in the
// the unique table
//
// Deleting an interior node releases its children, and a child that loses
// its last reference is deleted in turn. Left to nest, that is one set of
// destructor frames per level of the DAG, so releasing a deeply nested
// formula runs off the stack -- the depth is the input's, not ours. So only
// the outermost node deletes: anything that dies underneath it is queued on
// the manager and deleted by the loop below, which keeps the whole teardown
// at one frame.
void ASTInterior::CleanUp()
{
  nodeManager->_interior_unique_table.erase(this);

  if (nodeManager->_deleting_interiors)
  {
    nodeManager->_pending_deletion.push_back(this);
    return;
  }

  // Held separately: the first delete below is `this`, and nodeManager is
  // one of its members.
  STPMgr* const mgr = nodeManager;

  // Lowered by the guard rather than by the line after the loop. A destructor
  // that threw would otherwise leave the flag raised for the rest of the
  // process, and every node released after that would queue on a drain that
  // never runs again -- a leak of the whole DAG rather than a crash, which is
  // the harder of the two to notice.
  struct Draining
  {
    STPMgr* mgr;
    Draining(STPMgr* m) : mgr(m) { mgr->_deleting_interiors = true; }
    ~Draining() { mgr->_deleting_interiors = false; }
  } draining(mgr);

  ASTInterior* node = this;
  while (true)
  {
    delete node; // releases its children; any that die queue up above.

    if (mgr->_pending_deletion.empty())
      break;
    node = mgr->_pending_deletion.back();
    mgr->_pending_deletion.pop_back();
  }
}

// Returns kinds.  "lispprinter" handles printing of parenthesis
// and childnodes. (c_friendly is for printing hex. numbers that C
// compilers will accept)
void ASTInterior::nodeprint(ostream& os, bool /*c_friendly*/)
{
  os << _kind_names[_kind];
}

// ASTInteriorHasher::operator() and ASTInteriorEqual::operator() are defined
// inline in ASTInterior.h.

ASTInterior::~ASTInterior()
{
}

} // end of namespace
