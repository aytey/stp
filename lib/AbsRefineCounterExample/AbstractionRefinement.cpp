/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
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

#include "stp/AST/AST.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/AxiomMemo.h"
#include <map>
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/STPManager/STPManager.h"
#include <cassert>
#include <math.h>

namespace stp
{
using std::pair;
using std::map;

/******************************************************************
 * Abstraction Refinement related functions
 ******************************************************************/

void getSatVariables(const ASTNode& a, vector<unsigned>& v_a,
                     SATSolver& SatSolver, ToSATBase::ASTNodeToSATVar& satVar)
{
  ToSATBase::ASTNodeToSATVar::iterator it = satVar.find(a);
  if (it != satVar.end())
  {
    v_a = it->second;

    // ToCNFAIG::fill_node_to_var() writes ~0u for a bit of a symbol that
    // reached no SAT variable, and the same value arrives from a CNF
    // generator that left an object's variable number at -1. getEquals()
    // indexes this vector straight into mkLit(), where the sentinel wraps
    // into a variable far past the solver's range: MiniSat then indexes
    // its assignment array out of bounds, and Cadical is handed a literal
    // beyond max_var.
    //
    // There is no safe recovery. Allocating a fresh variable for the
    // missing bit -- what the branch below does for a symbol that was
    // never bit-blasted at all -- would carry no connection to the term
    // the axiom is about, so the congruence clause could fail to rule out
    // the candidate model it was built from. The array-equality encoder
    // rejects the same shape for the same reason; see
    // ExtensionalityContext::checkPreencodedBV().
    for (size_t i = 0, size = v_a.size(); i < size; ++i)
      if (v_a[i] == ~((unsigned)0))
        FatalError("An array axiom leaf has a bit with no SAT variable: ", a);
  }
  else if (!a.isConstant())
  {
    assert(a.GetKind() == SYMBOL);
    // It was ommitted from the initial problem, so assign it freshly.
    for (unsigned i = 0; i < a.GetValueWidth(); i++)
    {
      uint32_t v = SatSolver.newVar();
      // We probably don't want the variable eliminated.
      SatSolver.setFrozen(v);
      v_a.push_back(v);
    }
    satVar.insert(make_pair(a, v_a));
  }
}

// This function adds the clauses to constrain that "a" and "b" equal a fresh
// variable
// (which it returns).
// Because it's used to create array axionms (a=b)-> (c=d), it can be
// used to only add one of the two polarities.
uint32_t getEquals(SATSolver& SatSolver, const ASTNode& a, const ASTNode& b,
                   ToSATBase::ASTNodeToSATVar& satVar, Polarity polary)
{
  const unsigned width = a.GetValueWidth();
  assert(width == b.GetValueWidth());

  vector<unsigned> v_a;
  vector<unsigned> v_b;

  getSatVariables(a, v_a, SatSolver, satVar);
  getSatVariables(b, v_b, SatSolver, satVar);

  // The only time v_a or v_b will be empty is if "a" resp. "b" is a constant.

  if (v_a.size() == width && v_b.size() == width)
  {
    SATSolver::vec_literals all;
    const int result = SatSolver.newVar();

    for (unsigned i = 0; i < width; i++)
    {
      SATSolver::vec_literals s;

      if (polary != Polarity::RIGHT_ONLY)
      {
        int nv0 = SatSolver.newVar();
        s.push(SATSolver::mkLit(v_a[i], true));
        s.push(SATSolver::mkLit(v_b[i], true));
        s.push(SATSolver::mkLit(nv0, false));
        SatSolver.addClause(s);
        s.clear();

        s.push(SATSolver::mkLit(v_a[i], false));
        s.push(SATSolver::mkLit(v_b[i], false));
        s.push(SATSolver::mkLit(nv0, false));
        SatSolver.addClause(s);
        s.clear();

        all.push(SATSolver::mkLit(nv0, true));
      }

      if (polary != Polarity::LEFT_ONLY)
      {
        s.push(SATSolver::mkLit(v_a[i], true));
        s.push(SATSolver::mkLit(v_b[i], false));
        s.push(SATSolver::mkLit(result, true));
        SatSolver.addClause(s);
        s.clear();

        s.push(SATSolver::mkLit(v_a[i], false));
        s.push(SATSolver::mkLit(v_b[i], true));
        s.push(SATSolver::mkLit(result, true));
        SatSolver.addClause(s);
        s.clear();
      }
    }
    if (all.size() > 0)
    {
      all.push(SATSolver::mkLit(result, false));
      SatSolver.addClause(all);
    }
    return result;
  }
  else if ((v_a.size() == 0) ^ (v_b.size() == 0))
  {
    ASTNode constant = a.isConstant() ? a : b;
    vector<unsigned> vec = v_a.size() == 0 ? v_b : v_a;
    assert(constant.isConstant());
    assert(vec.size() == width);

    SATSolver::vec_literals all;
    const int result = SatSolver.newVar();
    all.push(SATSolver::mkLit(result, false));

    CBV v = constant.GetBVConst();
    for (unsigned i = 0; i < width; i++)
    {
      if (polary != Polarity::RIGHT_ONLY)
      {
        if (CONSTANTBV::BitVector_bit_test(v, i))
          all.push(SATSolver::mkLit(vec[i], true));
        else
          all.push(SATSolver::mkLit(vec[i], false));
      }

      if (polary != Polarity::LEFT_ONLY)
      {
        SATSolver::vec_literals p;
        p.push(SATSolver::mkLit(result, true));
        if (CONSTANTBV::BitVector_bit_test(v, i))
          p.push(SATSolver::mkLit(vec[i], false));
        else
          p.push(SATSolver::mkLit(vec[i], true));

        SatSolver.addClause(p);
      }
    }
    if (all.size() > 1)
      SatSolver.addClause(all);
    return result;
  }
  else if (a.isConstant() && b.isConstant())
  {
    // A congruence axiom between two constant indexes (reachable when
    // both spell one value under different constant nodes -- a float
    // constant interns apart from the plain constant with its bits):
    // the equality's truth is just their bits; pin a fresh variable to
    // it.
    const int result = SatSolver.newVar();
    SATSolver::vec_literals unit;
    unit.push(SATSolver::mkLit(result, !constantsSameBits(a, b)));
    SatSolver.addClause(unit);
    return result;
  }
  else
  {
    FatalError("Unexpected, both must be constants..");
  }
}

/******************************************************************
 * ARRAY READ ABSTRACTION REFINEMENT
 *
 * SATBased_ArrayReadRefinement()
 *
 * What it really does is, for each array, loop over each index i.
 * inside that loop, it finds all the true and false axioms with i
 * as first index.  When it's got them all, it adds the false axioms
 * to the formula and re-solves, and returns if the result is
 * correct.  Otherwise, it goes on to the next index.
 *
 * If it gets through all the indices without a correct result
 * (which I think is impossible), it then solves with all the true
 * axioms, too.
 *
 * This is not the most obvious way to do it, and I don't know how
 * it compares with other approaches (e.g., one false axiom at a
 * time or all the false axioms each time).
 *****************************************************************/

void applyAxiomToSAT(SATSolver& SatSolver, AxiomToBe& toBe,
                     ToSATBase::ASTNodeToSATVar& satVar)
{
  uint32_t a = getEquals(SatSolver, toBe.index0, toBe.index1, satVar,
                         Polarity::LEFT_ONLY);
  uint32_t b = getEquals(SatSolver, toBe.value0, toBe.value1, satVar,
                         Polarity::RIGHT_ONLY);
  SATSolver::vec_literals satSolverClause;
  satSolverClause.push(SATSolver::mkLit(a, true));
  satSolverClause.push(SATSolver::mkLit(b, false));
  SatSolver.addClause(satSolverClause);
}

// Axioms already emitted against one solver, so that re-deriving them costs
// nothing. This is not a micro-optimisation: getEquals mints a FRESH
// comparison circuit on every call -- a new variable per index bit plus the
// clauses tying it to the operands -- so a round that re-derives a pair the
// solver already constrains does not submit a duplicate clause, it submits an
// entirely new circuit encoding a constraint that is already there. Left
// alone, a refinement loop that keeps re-deriving the same pairs grows the
// solver without bound and no clause- or variable-based progress measure can
// tell that apart from real work, which is why the no-progress guard could
// never fire.
//
// The key is the ORDERED quadruple, held as nodes rather than as node numbers.
// The GC re-mints the numbers of unreferenced nodes -- the same hazard the
// deterministic-name factory documents -- so the map holds the nodes alive and
// its keys stay distinct. (index0,index1,value0,value1) and
// (index1,index0,value1,value0) denote the same axiom, but swapping ONE pair
// denotes a different one, so nothing is canonicalised here: a missed dedup
// costs a circuit, a wrong one costs a constraint.
//
// The value is what the four leaves mapped to when the axiom was emitted, and
// checking it is what makes this safe rather than merely plausible. The
// node->variable map is rebuilt per solve and omits symbols the driver has
// eliminated for THIS solve; when a leaf is missing, getSatVariables mints
// throwaway variables and the axiom lands on nothing. A later solve can have
// the same leaf back with real variables, and a memo that only remembered
// "emitted" would suppress the real axiom in favour of the vacuous one -- a
// dropped congruence, i.e. sat on an unsat query. So a hit is honoured only
// while every leaf still maps to exactly the variables it had; otherwise the
// axiom is emitted again.
namespace
{
struct QuadLess
{
  bool operator()(const std::vector<ASTNode>& a,
                  const std::vector<ASTNode>& b) const
  {
    for (size_t i = 0; i < 4; i++)
      if (a[i].GetNodeNum() != b[i].GetNodeNum())
        return a[i].GetNodeNum() < b[i].GetNodeNum();
    return false;
  }
};

struct EmittedAxioms : public SATSolver::RefinementMemo
{
  std::map<std::vector<ASTNode>, std::vector<std::vector<unsigned>>, QuadLess>
      emitted;
};

std::vector<ASTNode> axiomKey(const AxiomToBe& toBe)
{
  std::vector<ASTNode> k;
  k.push_back(toBe.index0);
  k.push_back(toBe.index1);
  k.push_back(toBe.value0);
  k.push_back(toBe.value1);
  return k;
}

// The leaves' CURRENT variables, looked up without minting anything: a
// constant, or a symbol the map does not carry, simply yields an empty vector.
std::vector<std::vector<unsigned>>
currentVars(const std::vector<ASTNode>& key,
            ToSATBase::ASTNodeToSATVar& satVar)
{
  std::vector<std::vector<unsigned>> v(4);
  for (size_t i = 0; i < 4; i++)
  {
    ToSATBase::ASTNodeToSATVar::const_iterator it = satVar.find(key[i]);
    if (it != satVar.end())
      v[i] = it->second;
  }
  return v;
}
} // namespace

// Returns how many axioms were actually emitted. The callers re-solve only on
// a non-zero count: a round that emits nothing has changed nothing, and
// solving again would burn a search before the caller's no-progress guard
// could notice.
size_t applyAxiomsToSolver(ToSATBase::ASTNodeToSATVar& satVar,
                           std::vector<AxiomToBe>& toBe, SATSolver& SatSolver)
{
  if (SatSolver.refinementMemo.get() == NULL)
    SatSolver.refinementMemo.reset(new EmittedAxioms);
  EmittedAxioms& memo =
      *static_cast<EmittedAxioms*>(SatSolver.refinementMemo.get());

  size_t emitted = 0;
  for (size_t i = 0; i < toBe.size(); i++)
  {
    const std::vector<ASTNode> key = axiomKey(toBe[i]);
    const std::vector<std::vector<unsigned>> now = currentVars(key, satVar);
    std::map<std::vector<ASTNode>, std::vector<std::vector<unsigned>>,
             QuadLess>::iterator hit = memo.emitted.find(key);
    if (hit != memo.emitted.end() && hit->second == now)
      continue;
    applyAxiomToSAT(SatSolver, toBe[i], satVar);
    emitted++;
    // Re-read: applyAxiomToSAT may have minted variables for a leaf that had
    // none, and it is the post-emission mapping the next round must match.
    memo.emitted[key] = currentVars(key, satVar);
  }
  toBe.clear();
  return emitted;
}

bool sortBySize(const pair<ASTNode, ArrayTransformer::arrTypeMap>& a,
                const pair<ASTNode, ArrayTransformer::arrTypeMap>& b)
{
  return a.second.size() < b.second.size();
}

bool sortByIndexConstants(const pair<ASTNode, ArrayTransformer::ArrayRead>& a,
                          const pair<ASTNode, ArrayTransformer::ArrayRead>& b)
{
  int aCount = ((a.second.index_symbol.isConstant()) ? 2 : 0) +
               (a.second.symbol.isConstant() ? 1 : 0);
  int bCount = ((b.second.index_symbol.isConstant()) ? 2 : 0) +
               (b.second.symbol.isConstant() ? 1 : 0);
  return aCount > bCount;
}

bool sortbyConstants(const AxiomToBe& a, const AxiomToBe& b)
{
  return a.numberOfConstants() > b.numberOfConstants();
}

SOLVER_RETURN_TYPE
AbsRefine_CounterExample::SATBased_ArrayReadRefinement(
    SATSolver& SatSolver, const ASTNode& original_input, ToSATBase* tosat)
{
  vector<AxiomToBe> RemainingAxiomsVec;
  vector<AxiomToBe> FalseAxiomsVec;
  // NB. Because we stop this timer before entering the SAT solver, the count
  // it produces isn't the number of times Array Read Refinement was entered.
  bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);
  /// Check the arrays with the least indexes first.

  vector<pair<ASTNode, ArrayTransformer::arrTypeMap>> arrayToIndex;
  arrayToIndex.insert(arrayToIndex.begin(),
                      ArrayTransform->arrayToIndexToRead.begin(),
                      ArrayTransform->arrayToIndexToRead.end());
  sort(arrayToIndex.begin(), arrayToIndex.end(), sortBySize);

  ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  const bool extActive = ext != NULL && ext->activeInSolve();
  if (extActive)
    FatalError("array-equality: legacy array-read refinement was invoked "
               "during a solve owned by the extensionality checker");

  // In these loops we try to construct Leibnitz axioms and add it to
  // the solve(). We add only those axioms that are false in the
  // current counterexample. we keep adding the axioms until there
  // are no more axioms to add
  //
  // for each array, fetch its list of indices seen so far
  for (vector<pair<ASTNode, ArrayTransformer::arrTypeMap>>::const_iterator
           iset = arrayToIndex.begin(),
           iset_end = arrayToIndex.end();
       iset != iset_end; iset++)
  {
    const map<ASTNode, ArrayTransformer::ArrayRead>& mapper = iset->second;

    vector<ASTNode> listOfIndices;
    listOfIndices.reserve(mapper.size());

    // Make a vector of the read symbols.
    ASTVec read_node_symbols;
    read_node_symbols.reserve(listOfIndices.size());

    vector<Kind> jKind;
    jKind.reserve(mapper.size());

    vector<ASTNode> concreteIndexes;
    concreteIndexes.reserve(mapper.size());

    vector<ASTNode> concreteValues;
    concreteValues.reserve(mapper.size());

    ASTVec index_symbols;

    vector<pair<ASTNode, ArrayTransformer::ArrayRead>> indexToRead;
    indexToRead.insert(indexToRead.begin(), mapper.begin(), mapper.end());
    sort(indexToRead.begin(), indexToRead.end(), sortByIndexConstants);

    for (vector<pair<ASTNode, ArrayTransformer::ArrayRead>>::const_iterator it =
             indexToRead.begin();
         it != indexToRead.end(); it++)
    {
      const ASTNode& the_index = it->first;
      listOfIndices.push_back(the_index);

      ASTNode arrsym = it->second.symbol;
      read_node_symbols.push_back(arrsym);

      index_symbols.push_back(it->second.index_symbol);

      assert(read_node_symbols[0].GetValueWidth() == arrsym.GetValueWidth());
      assert(listOfIndices[0].GetValueWidth() == the_index.GetValueWidth());

      jKind.push_back(the_index.GetKind());

      concreteIndexes.push_back(TermToConstTermUsingModel(the_index));
      concreteValues.push_back(TermToConstTermUsingModel(arrsym));
    }

    assert(listOfIndices.size() == mapper.size());

    // loop over the list of indices for the array and create LA,
    // and add to inputAlreadyInSAT
    for (size_t i = 0; i < listOfIndices.size(); i++)
    {
      const ASTNode& index_i = listOfIndices[i];
      const Kind iKind = index_i.GetKind();

      // Create all distinct pairs of indexes.
      for (size_t j = i + 1; j < listOfIndices.size(); j++)
      {
        const ASTNode& index_j = listOfIndices[j];

        // If the indexes are constants of different values, the cells are
        // distinct and no congruence is needed. Compare bits, not nodes:
        // a float constant interns apart from the plain constant with its
        // bits, and skipping such a pair drops a needed axiom for good.
        if (BVCONST == iKind && jKind[j] == BVCONST &&
            constantsDenoteDifferentValues(index_i, index_j))
          continue;

        if (ASTFalse == simp->CreateSimplifiedEQ(index_i, index_j))
          continue; // shortcut.

        AxiomToBe o(index_symbols[i], index_symbols[j], read_node_symbols[i],
                    read_node_symbols[j]);

        if (concreteIndexes[i] == concreteIndexes[j] &&
            concreteValues[i] != concreteValues[j])
        {
          FalseAxiomsVec.push_back(o);
          // ToSATBase::ASTNodeToSATVar	& satVar =
          // tosat->SATVar_to_SymbolIndexMap();
          // applyAxiomsToSolver(satVar, FalseAxiomsVec, SatSolver);
        }
        else
          RemainingAxiomsVec.push_back(o);
      }
      if (FalseAxiomsVec.size() > 0)
      {
        ToSATBase::ASTNodeToSATVar& satVar = tosat->SATVar_to_SymbolIndexMap();
        const size_t wanted = FalseAxiomsVec.size();
        const size_t sent =
            applyAxiomsToSolver(satVar, FalseAxiomsVec, SatSolver);
        if (bm->UserFlags.stats_flag && sent < wanted)
          std::cerr << "Array refinement: " << (wanted - sent) << " of "
                    << wanted << " violated axioms already emitted"
                    << std::endl;

        if (sent > 0)
        {
          SOLVER_RETURN_TYPE res2;
          bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
          res2 = CallSAT_ResultCheck(SatSolver, ASTTrue, original_input,
                                     original_input, tosat,
                                     true);

          if (SOLVER_UNDECIDED != res2)
            return res2;
          bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);
        }
      }
    }
  }
#if 1
  if (RemainingAxiomsVec.size() > 0)
  {
    if (bm->UserFlags.stats_flag)
    {
      std::cout << "Adding all the remaining " << RemainingAxiomsVec.size()
                << " read axioms " << std::endl;
    }
    ToSATBase::ASTNodeToSATVar& satVar = tosat->SATVar_to_SymbolIndexMap();
    const size_t wanted = RemainingAxiomsVec.size();
    const size_t sent = applyAxiomsToSolver(satVar, RemainingAxiomsVec,
                                            SatSolver);
    if (bm->UserFlags.stats_flag && sent < wanted)
      std::cerr << "Array refinement: " << (wanted - sent) << " of " << wanted
                << " remaining axioms already emitted" << std::endl;

    bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
    if (sent > 0)
      return CallSAT_ResultCheck(SatSolver, ASTTrue, original_input,
                                 original_input, tosat, true);
    // Nothing new: the state is exactly what the last solve already rejected,
    // so re-solving would return the same answer. Say so, and let the caller's
    // no-progress guard convert the livelock into a diagnosis.
    return SOLVER_UNDECIDED;
  }
// For difficult problems, I suspec this is a better way to do it.
// However because it can cause an extra three SAT solver calls, it slows down
// easy problems.
#else
  if (RemainingAxiomsVec.size() > 0)
  {
    // Add the axioms in order of how many constants there are in each.

    ToSATBase::ASTNodeToSATVar& satVar = tosat->SATVar_to_SymbolIndexMap();
    sort(RemainingAxiomsVec.begin(), RemainingAxiomsVec.end(), sortbyConstants);
    int current_position = 0;
    for (int n_const = 4; n_const >= 0; n_const--)
    {
      bool added = false;
      while (current_position < RemainingAxiomsVec.size() &&
             RemainingAxiomsVec[current_position].numberOfConstants() ==
                 n_const)
      {
        AxiomToBe& toBe = RemainingAxiomsVec[current_position];
        applyAxiomToSAT(SatSolver, toBe, satVar);
        current_position++;
        added = true;
      }
      if (!added)
        continue;
      bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
      SOLVER_RETURN_TYPE res2;
      res2 =
          CallSAT_ResultCheck(SatSolver, ASTTrue, original_input,
                              original_input, tosat, true);
      if (SOLVER_UNDECIDED != res2)
        return res2;

      bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);
    }
    assert(current_position == RemainingAxiomsVec.size());
    RemainingAxiomsVec.clear();
    assert(SOLVER_UNDECIDED == CallSAT_ResultCheck(SatSolver, ASTTrue,
                                                   original_input,
                                                   original_input, tosat,
                                                   true));
  }
#endif

  bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
  return SOLVER_UNDECIDED;
}

// This is another way of performing Ackermannisation.
void AbsRefine_CounterExample::applyAllCongruenceConstraints(
    SATSolver& SatSolver, ToSATBase* tosat)
{
  // if (bm->UserFlags.stats_flag)
  std::cerr << "~CNF~" << std::endl;

  vector<pair<ASTNode, ArrayTransformer::arrTypeMap>> arrayToIndex;
  arrayToIndex.insert(arrayToIndex.begin(),
                      ArrayTransform->arrayToIndexToRead.begin(),
                      ArrayTransform->arrayToIndexToRead.end());

  ToSATBase::ASTNodeToSATVar& satVar = tosat->SATVar_to_SymbolIndexMap();

  // for each array, fetch its list of indices seen so far
  for (vector<pair<ASTNode, ArrayTransformer::arrTypeMap>>::const_iterator
           iset = arrayToIndex.begin(),
           iset_end = arrayToIndex.end();
       iset != iset_end; iset++)
  {
    // const ASTNode& ArrName = iset->first;
    const map<ASTNode, ArrayTransformer::ArrayRead>& mapper = iset->second;

    vector<ASTNode> listOfIndices;
    listOfIndices.reserve(mapper.size());

    // Make a vector of the read symbols.
    ASTVec read_node_symbols;
    read_node_symbols.reserve(listOfIndices.size());

    vector<Kind> jKind;
    jKind.reserve(mapper.size());

    ASTVec index_symbols;
    index_symbols.reserve(mapper.size());

    for (map<ASTNode, ArrayTransformer::ArrayRead>::const_iterator it =
             mapper.begin();
         it != mapper.end(); it++)
    {
      const ASTNode& the_index = it->first;
      listOfIndices.push_back(the_index);

      ASTNode arrsym = it->second.symbol;
      read_node_symbols.push_back(arrsym);

      index_symbols.push_back(it->second.index_symbol);

      assert(read_node_symbols[0].GetValueWidth() == arrsym.GetValueWidth());
      assert(listOfIndices[0].GetValueWidth() == the_index.GetValueWidth());

      jKind.push_back(the_index.GetKind());
    }

    assert(listOfIndices.size() == mapper.size());

    // loop over the list of indices for the array and create LA,
    // and add to inputAlreadyInSAT
    for (size_t i = 0; i < listOfIndices.size(); i++)
    {
      const ASTNode& index_i = listOfIndices[i];
      const Kind iKind = index_i.GetKind();

      // Create all distinct pairs of indexes.
      for (size_t j = i + 1; j < listOfIndices.size(); j++)
      {
        const ASTNode& index_j = listOfIndices[j];

        // If the indexes are constants of different values, the cells are
        // distinct and no congruence is needed. Compare bits, not nodes:
        // a float constant interns apart from the plain constant with its
        // bits, and skipping such a pair drops a needed axiom for good.
        if (BVCONST == iKind && jKind[j] == BVCONST &&
            constantsDenoteDifferentValues(index_i, index_j))
          continue;

        if (ASTFalse == simp->CreateSimplifiedEQ(index_i, index_j))
          continue; // shortcut.

        if (index_i == index_j)
          std::cerr << "EQUAL";

        AxiomToBe o(index_symbols[i], index_symbols[j], read_node_symbols[i],
                    read_node_symbols[j]);

        applyAxiomToSAT(SatSolver, o, satVar);
      }
    }
  }
}

} // end of namespace stp
