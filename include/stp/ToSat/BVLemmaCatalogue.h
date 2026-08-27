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

#ifndef BVLEMMACATALOGUE_H
#define BVLEMMACATALOGUE_H

// The arithmetic facts BV term abstraction refines with, as data.
//
// A fact has five faces: an enumerator, a predicate over values, a circuit
// over SAT variables, a name, and the option family that owns it -- plus a
// position in the order the refiner offers them. Four of those, and the
// order, used to be four `switch`es and an array spread over three
// translation units, with nothing but a test keeping them in step, and with
// the ranked array the one place a compiler could not notice an omission.
// They are one table each here.
//
// What is deliberately *not* here is the predicate and the circuit. The
// predicate stays one switch per operation below, because a switch over a
// scoped enum with no default is a compile error when a fact is added and a
// table of function pointers is not. The circuit stays with the bit-blaster,
// because it is written in BBNodeVec.

#include "stp/STPManager/UserDefinedFlags.h"
#include "stp/Util/Attributes.h"

#include <vector>

namespace stp
{

// The facts about division that STP had no way to state before this: each
// is an inequality or an implication over the dividend, the divisor and the
// quotient, rather than a value for the quotient.
//
// They are not STP's. They come from:
//
//   Aina Niemetz, Mathias Preiner, Yoni Zohar.
//   Scalable Bit-Blasting with Abstractions.
//   CAV 2024, LNCS 14681, pp. 178-200. doi:10.1007/978-3-031-65627-9_9
//
// and are reimplemented here against STP's own bit-blaster rather than
// copied from anywhere.
//
// The four with no premise are not facts anyone would derive by thinking
// about division -- `x >=u -((-s) & (-t))` is the output of the syntax-guided
// synthesis that paper describes -- which is the argument for taking a
// published set rather than inventing one.
//
// The table in the refiner keeps the measured entries in firing order and the
// unranked tail after them. Completeness is useful for controlled ablations,
// not evidence that every fact should eventually be enabled by default.
enum class DivLemma
{
  // x = 0 and s != 0 -> t = 0
  DividendZero,
  // s = x and s != 0 -> t = 1
  DivisorEqualsDividend,
  // s = ~0 and x != ~0 -> t = 0
  DivisorAllOnes,
  // t <=u -(s | 1)
  QuotientBelowNegatedDivisor,
  // x >=u -((-s) & (-t))
  DividendAboveNegatedAnd,
  // s >=u (x >> t)
  DivisorAboveShiftedDividend,
  // (s - 1) >=u (x >> t)
  DivisorLessOneAboveShiftedDividend,
  // x >=u ((t << 1) >> (t << s))
  DividendAboveShiftedDoubleQuotient,

  // t != -(s & ~x)
  QuotientNotNegatedAnd,
  // (x & -t) >=u (s & t)
  MaskedDividendAboveDivisorAndQuotient,
  // x >=u ((s >> (s << t)) << 1)
  DividendAboveDoubledShiftedDivisor,
  // t >=u ((x >> s) << 1)
  QuotientAboveDoubledShiftedDividend,
  // x >=u ((x | t) & (s << 1))
  DividendAboveOrAndDoubledDivisor,
  // x >=u ((x | s) & (t << 1))
  DividendAboveOrAndDoubledQuotient,
  // (x >> t) != (s | t)
  ShiftedDividendNotOr,
  // x >=u (t xor (t >> (s >> 1)))
  DividendAboveQuotientXorShifted,
  // x >=u (s xor (s >> (t >> 1)))
  DividendAboveDivisorXorShifted,
  // x != t + t + (x | s)
  DividendNotTwiceQuotientPlusOr,

  // s <=u x <u 2s -> t = 1. This STP-specific exact-band fact shares its
  // premise with RemainderIsDifference and is ranked with the fixed UDIV
  // registry rather than maintained as a one-off schema.
  QuotientIsOne,

  // The tail that did not fire on the qualification corpus. The enumerators
  // keep the catalogue's own numbering, which is the only handle these have;
  // divLemmaName() gives each a description of its formula.
  UdivRef10,
  UdivRef11,
  UdivRef20,
  UdivRef21,
  UdivRef23,
  UdivRef24,
  UdivRef25,
  UdivRef28,
  UdivRef29,
  UdivRef30,
  UdivRef31,
  UdivRef32,
  UdivRef34,
  UdivRef36,
  UdivRef38
};

// The remainder facts, in the order the refiner offers them.
enum class RemLemma
{
  DividendZero,
  DivisorEqualsDividend,
  DividendBelowDivisor,
  // s <=u x <u 2s -> t = x - s. The remainder half of QuotientIsOne, ranked
  // with the three above because it likewise determines the result throughout
  // its premise rather than only bounding it.
  RemainderIsDifference,
  DividendWithinDivisorOrRemainder,
  DividendAboveRemainderOrAnd,
  RemainderOutsideOperandsNotOne,
  RemainderNotOrOfComplements,
  RemainderInOperandsAboveLowBit,
  DividendNotOrOfNegations,
  DifferenceAboveRemainder,
  XorAboveRemainder
};

// The unconditional multiplication facts not already represented by STP's
// power-of-two, low-bit, trailing-zero and odd-inverse schemas. Each has two
// readings because multiplication is commutative but most synthesised
// expressions are not syntactically so.
enum class MulLemma
{
  // s = s << (x & (1 >> t)). Its only nontrivial reading is that an odd x and
  // a zero product force s to zero. The value predicate keeps this spelling
  // and the bit-blaster encodes the compact equivalent implication.
  FactorUnchangedByMaskedShift,
  MulRef1,
  FactorAndProductNotOr,
  MulRefN3,
  MulRefN5,
  MulRefN6,
  MulRef14,
  MulRef15,
  MulRefN9,
  MulRef18,
  MulRefN11,
  MulRefN12,
  MulRefN13,
  MulRef13,
  MulRef12
};

enum class AddLemma
{
  AddZero,
  AddSame,
  AddInv,
  AddOverflow,
  AddNoOverflow,
  AddOr,
  AddRef6,
  AddRef7,
  AddRef8,
  AddRef9,
  AddRef10,
  AddRef11,
  AddRef12
};

// One row of a catalogue: everything about a fact except how to evaluate it
// and how to build it.
//
// `minWidth` and `excludedWidth` are the fact's domain. Several of these
// were synthesised rather than derived, and a synthesised fact is not
// automatically a theorem at every width -- `t >=u (1 & ((x & s) >> 1))`
// holds everywhere except at two bits, where both operands can carry bit one
// and the product still truncates to zero. A caller must not evaluate or
// install one outside its domain, and the tests check that each restriction
// is necessary rather than defensive. Zero excludes nothing.
template <typename Lemma> struct BVLemmaEntry
{
  Lemma lemma;
  const char* name;
  BVSchemaGroup group;
  unsigned minWidth;
  unsigned excludedWidth;

  bool applicable(unsigned width) const
  {
    return width >= minWidth && width != excludedWidth;
  }
};

// The size of each catalogue. A constant rather than only a runtime count
// because the refiner packs one installed-lemma bit per entry into a 64-bit
// field alongside other state, and whether the registry still fits is a
// question a compiler should answer. BVLemmaCatalogue.cpp asserts each
// against its table.
constexpr unsigned BV_DIV_LEMMA_COUNT = 34;
constexpr unsigned BV_REM_LEMMA_COUNT = 12;
constexpr unsigned BV_MUL_LEMMA_COUNT = 15;
constexpr unsigned BV_ADD_LEMMA_COUNT = 13;

// The catalogues, in the order the refiner offers them. Measured entries
// come first, ranked by how often they fired on the qualification corpus;
// the unranked tail keeps its catalogue order, because there is no
// measurement to rank it by and an arbitrary reordering would only look like
// one.
DLL_PUBLIC const BVLemmaEntry<DivLemma>* divLemmaTable(unsigned& count);
DLL_PUBLIC const BVLemmaEntry<RemLemma>* remLemmaTable(unsigned& count);
DLL_PUBLIC const BVLemmaEntry<MulLemma>* mulLemmaTable(unsigned& count);
DLL_PUBLIC const BVLemmaEntry<AddLemma>* addLemmaTable(unsigned& count);

// The i'th row of a catalogue. The refiner carries a rank rather than an
// enumerator, because the rank is what its installed-lemma mask is indexed
// by, so this is the lookup it actually does.
DLL_PUBLIC const BVLemmaEntry<DivLemma>& divLemmaAt(unsigned index);
DLL_PUBLIC const BVLemmaEntry<RemLemma>& remLemmaAt(unsigned index);
DLL_PUBLIC const BVLemmaEntry<MulLemma>& mulLemmaAt(unsigned index);
DLL_PUBLIC const BVLemmaEntry<AddLemma>& addLemmaAt(unsigned index);

// The row for one fact, by name rather than by rank. Linear over a table of
// at most a few dozen; the refiner indexes by rank and never comes here.
DLL_PUBLIC const BVLemmaEntry<DivLemma>& divLemmaEntry(DivLemma lemma);
DLL_PUBLIC const BVLemmaEntry<RemLemma>& remLemmaEntry(RemLemma lemma);
DLL_PUBLIC const BVLemmaEntry<MulLemma>& mulLemmaEntry(MulLemma lemma);
DLL_PUBLIC const BVLemmaEntry<AddLemma>& addLemmaEntry(AddLemma lemma);

inline const char* divLemmaName(DivLemma l) { return divLemmaEntry(l).name; }
inline const char* remLemmaName(RemLemma l) { return remLemmaEntry(l).name; }
inline const char* mulLemmaName(MulLemma l) { return mulLemmaEntry(l).name; }
inline const char* addLemmaName(AddLemma l) { return addLemmaEntry(l).name; }

inline bool divLemmaApplicable(DivLemma l, unsigned w)
{
  return divLemmaEntry(l).applicable(w);
}
inline bool remLemmaApplicable(RemLemma l, unsigned w)
{
  return remLemmaEntry(l).applicable(w);
}
inline bool mulLemmaApplicable(MulLemma l, unsigned w)
{
  return mulLemmaEntry(l).applicable(w);
}
inline bool addLemmaApplicable(AddLemma l, unsigned w)
{
  return addLemmaEntry(l).applicable(w);
}

// Whether one of them holds of these three values. The refiner asks before
// installing -- a lemma the candidate already satisfies rules nothing out --
// and the tests ask to check the circuits say the same thing.
//
// Bit vectors, least significant bit first, all of the same width.
DLL_PUBLIC bool divLemmaHolds(DivLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);
DLL_PUBLIC bool remLemmaHolds(RemLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);
DLL_PUBLIC bool mulLemmaHolds(MulLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);
DLL_PUBLIC bool addLemmaHolds(AddLemma lemma, const std::vector<bool>& xBits,
                              const std::vector<bool>& sBits,
                              const std::vector<bool>& tBits);

} // namespace stp

#endif
