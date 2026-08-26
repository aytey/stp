# Bit-vector abstraction work: final handoff

Date: 2026-08-26

Branch: `cegar-next-codex-v3`

Based on: `989065aa` (`cegar-next-codex-v2`)

Hybrid based on: `b3b87580` (`cegar-variable-shift-udiv15`)

Additional source reviewed: `1351a312` (`pr-lemmas`)

V2 comparison source: `17465e3d` (`cegar-next-claude`)

V3 comparison source: `ed66f875` (`cegar-next-claude-v2`)

Worktree used for this stack:
`/home/avj/clones/stp/cegar-next-codex-v3`

## Executive summary

The implementation side of this line of work is now broad enough to call
complete:

- STP represents every enabled Bitwuzla UDIV, UREM, MUL, and ADD abstraction
  lemma from the local Bitwuzla source used for the comparison.
- The one UREM lemma Bitwuzla defines but leaves out of its active registry is
  also transcribed and tested, but deliberately remains disabled in STP.
- STP's older divisor-value, bound, power-of-two, trailing-zero, odd-product,
  and exact/value-pair fallbacks remain in place.
- Seven STP-specific schema groups have been added after completing the imported
  registries: quotient magnitude thresholds, exact low prefixes for addition
  and multiplication, a quotient-one remainder band, and paired DIV/REM
  low-prefix recomposition, plus the hybrid's quotient-one quotient band,
  capped divisor-magnitude bound, and full-width paired recomposition.
- Candidate predicates, emitted circuits or clauses, applicability
  restrictions, totalised zero-divisor behaviour, and complete end-to-end
  regressions are tested.

The coverage-first qualification sweep is now complete. It found a small
productive subset and a much larger neutral or harmful tail. Commit
`9d763349` therefore keeps every sound implementation available but puts the
families behind one named group mask:

- an explicitly enabled BV term abstraction inherits only `base,urem,mul-ref3`;
- `all` reproduces the complete stack represented before the mask;
- `none` reaches the ordinary operation-specific fallback without offering a
  schema;
- the master `--bv-term-abstraction-schemas=0` still overrides every group;
- BV term abstraction itself remains off by default.

The hybrid retains that qualified profile unchanged. Its three additional
families have compelling targeted regressions but no broad isolated corpus
qualification, so they are available for controlled experiments and remain
off in the inherited profile.

The older `/home/avj/clones/stp/NEXT_CEGAR_LEMMAS.md` described what was
missing before this stack. It is now stale and this file supersedes it.

## V3 hybrid convergence

V3 keeps V2's corpus-qualified defaults and record-aware paired DIV/REM
scheduler, then incorporates the parts of `cegar-next-claude-v2` that make
the larger catalogue easier to select, audit, and maintain:

- `udiv-observed` is a new group containing the ten ranked imported UDIV
  facts beyond `base` and `udiv15`. It was appended as bit 15, preserving all
  existing mask bits and counter ordinals. The old `udiv-extra` bit remains a
  compatibility umbrella: it still enables the observed facts and the
  unobserved registry tail exactly as it did in V2.
- The observed UDIV registry, the full UREM registry, and `MulRef3` now use
  semantic enum identifiers as well as semantic diagnostics. Comments retain
  their source-registry IDs for reconciliation with Bitwuzla, and aliases
  preserve the first catalogue's C++ spellings and underlying values.
- Named `qualified` and `aggressive` profiles apply the schema mask and round
  ceiling as one atomic operation. They are available through both the CLI
  and C API. An invalid profile changes neither field, and the CLI refuses to
  combine a profile with either lower-level option.
- The imported DIV, REM, MUL, and ADD registries share one table-driven test
  harness. It checks registry completeness, theorem soundness, width
  applicability, useful counterexamples, and predicate/circuit equivalence.
  The MUL8 regression additionally compares the published shifted predicate
  with an independently written compact implication before checking the CNF.
- ABI tests pin every pre-existing interface-flag, schema-bit, and counter
  ordinal explicitly. New public values are appended.

The profiles are:

| Profile | Groups | Rounds |
| --- | --- | ---: |
| `qualified` | `base,urem,mul-ref3` | 32 |
| `aggressive` | `base,udiv15,udiv-observed,urem,mul8,mul-ref3,quotient-one-rem,quotient-one-quot,divisor-magnitude,divrem-full` | 16 |

Neither profile enables BV term abstraction itself. A complete invocation is:

```sh
build/stp --bv-term-abstraction=1 \
  --bv-term-abstraction-profile=qualified input.smt2
```

The complete unobserved UDIV and MUL tails, ADD registry, open-ended quotient
thresholds, and low-prefix experiments remain individually selectable but
are not included in either named profile.

### V3 profile qualification

The two profiles were compared on all 287 natural DIV/REM consumers from the
existing qualification corpus: 219 SPEAR inputs plus 68 broader consumers.
Each input/profile pair used CaDiCaL, non-incremental mode, and a two-second
internal budget. Order was alternated per input and repetition, and the
complete run was repeated three times.

| Repeat | Qualified solved | Aggressive solved | Common median, Q/A | Common total, Q/A |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 258 | 257 | 0.040 / 0.030 s | 17.36 / 17.71 s |
| 2 | 258 | 257 | 0.030 / 0.030 s | 17.27 / 17.71 s |
| 3 | 258 | 257 | 0.040 / 0.030 s | 17.30 / 17.61 s |

There were no answer disagreements. Aggressive gained no solves, lost the
same solve in every repetition, and took 1.8--2.5% more time over the common
solves. The split explains why it is still a useful named experiment: both
profiles solved all 219 SPEAR inputs, while aggressive reduced their common
total by 3.6--6.3% in each repeat. On the other 68 consumers it solved 38
against qualified's 39 and increased the 38 common-solve total from
5.21--5.31 seconds to 6.15--6.33 seconds.

On the lost `sin2.c.2.smt2` case, qualified solved in 1.18--1.21 seconds at a
five-second budget; aggressive returned unknown after five seconds in all
three repeats and solved in about 5.8 seconds when given ten. Its trace
installed two 109-bit full recomposition facts early in the run.

The measured decision is therefore to retain `qualified` as the default mask
and round ceiling, while exposing `aggressive` as one reproducible opt-in
experiment. Raw profile data, while the temporary directory survives, is in
`/tmp/stp-cegar-v3-profile.zzNPXg`.

Fresh `RelWithDebInfo` builds pass the complete test suites with both supported
refinement backends: 170/170 with CaDiCaL and 169/169 with simplifying
MiniSat.

## V2 hybrid delta

The comparison with `cegar-next-claude` produced four changes without
altering the complete catalogue, the public flag ordinals, or the qualified
default group mask:

- Paired division/remainder refinement now reads both candidate values and
  emits both low-prefix and full recomposition clauses through each
  abstraction record's owned result-variable accessor. This preserves the
  durable incremental record when the AST-keyed map names a newer encoding
  of the same hash-consed term. A unit regression deliberately makes those
  two sources disagree and checks both the read and write sides.
- The capped divisor-magnitude bound now precedes the open-ended quotient
  thresholds. On the 256-bit binade regression, the `all` profile changed
  from a 30-second timeout at roughly 577 MB to 0.02 seconds at roughly
  23 MB. A chooser-level regression holds both facts violated and requires
  the capped family to win.
- Observed imported UDIV and UREM facts, plus qualified `MulRef3`, use
  semantic diagnostic names while retaining their source-registry enum IDs
  for mechanical reconciliation. Nine focused query regressions exercise
  individual imported relationships by name and group.
- A fresh CaDiCaL build passes all 172 CTest entries, including both complete
  query-file configurations. A separate simplifying-MiniSat build passes the
  five focused lemma/refiner binaries and the complete query-file suite.

The proposed 16-round limit was compared with 32 using the identical
`base,urem,mul-ref3` mask on all 287 natural division/remainder consumers from
the qualification corpus, at a two-second internal budget. Both solved 256
files with no answer disagreement; their common-solve medians were both
0.060 seconds, with totals of 25.04 seconds at 16 and 25.21 seconds at 32.
Five changed or materially timed cases were then repeated three times at a
five-second budget. Sixteen rounds gained no solve and produced two stable
small slowdowns, so V2 retains the 32-round default. Raw comparison data,
while the temporary directory survives, is under
`/tmp/stp-codex-v2-rounds.cwLXsl`.

## Scope and defaults

The base already contains the general BV term-abstraction machinery and the
initial division work merged in PR #989:

- `--bv-term-abstraction=1` abstracts sufficiently wide `BVPLUS`,
  `BVMULT`, `BVDIV`, `BVMOD`, ITE, and signed/unsigned inequalities.
- `--bv-abstraction-width=N` sets the shared width floor; its default is 64.
- `--bv-term-abstraction-mult=0` excludes multiplication.
- `--bv-term-abstraction-divmod=0` independently excludes division and
  remainder. Both scope flags default on, preserving the earlier behaviour.
- The ITE, addition, and comparison families have their own scope flags.
- `--bv-term-abstraction-schemas=1` enables algebraic schemas. The schema
  flag defaults to true, but term abstraction itself defaults to false.
- `--bv-term-abstraction-schema-groups=base,urem,mul-ref3` selects the
  schema families offered when the master schema flag is on. The value is a
  comma-separated list; `all` and `none` are stand-alone aliases. Whitespace
  and duplicate names are accepted, while malformed lists are rejected
  without partially changing the mask.
- `--bv-term-abstraction-rounds=32` separately caps schema rounds and
  value-pair blocking rounds for a heavy arithmetic record. Schema rounds do
  not consume the blocking allowance; after the blocking allowance is spent,
  the ordinary exact operation is installed.
- `--bv-term-abstraction-inc-bitblast=1` is a separate, default-off,
  multiplication-only partial-exact experiment.

Signed division and remainder are translated to unsigned operations before
bit-blasting, so they do not require separate abstraction registries.

The named groups and their disposition are:

| Group | Contents | In inherited profile? |
| --- | --- | --- |
| `base` | Schemas already present on merged master | yes |
| `udiv15` | `DividendAboveShiftedDoubleQuotient` | no |
| `udiv-observed` | Ranked imported UDIV facts beyond `base` and `udiv15` | no |
| `udiv-extra` | Compatibility umbrella for `udiv-observed` and the unobserved UDIV tail | no |
| `urem` | Enabled UREM registry | yes |
| `mul8` | Zero product with an odd operand | no |
| `mul-ref3` | `FactorAndProductNotOr` (`MulRef3`) alone | yes |
| `mul-extra` | Remaining general MUL registry | no |
| `add` | Complete ADD registry | no |
| `quotient-thresholds` | UDIV power-of-two magnitude thresholds | no |
| `low-prefix` | Exact low-three-bit ADD and MUL facts | no |
| `quotient-one-rem` | Remainder in the quotient-one band | no |
| `divrem-pair` | Paired DIV/REM low-prefix recomposition | no |
| `quotient-one-quot` | Quotient equals one in the one-subtraction band | no |
| `divisor-magnitude` | Capped divisor-magnitude quotient bound | no |
| `divrem-full` | Paired DIV/REM full modular recomposition | no |

The paired scheduler gives the low-prefix relation first refusal only when
the current model violates it. If those bits already agree, emitting the
prefix would make no progress, so an enabled `divrem-full` relation may fire
directly. Either relation consumes one schema round from both records and
prevents their individual schemas from also firing in that pass. The
divisor-magnitude family is limited to two instances per BVDIV record, the
cap that removed its observed exponent-walking regression.

The C API values for all pre-existing interface flags and counters remain
stable. `BV_TERM_ABSTRACTION_DIVMOD` and the three new group counters were
appended; they were not inserted into the published enum prefixes.

This partition is deliberately coarser than individual lemmas. It supports
qualified defaults and controlled experiments without making every
low-frequency algebraic fact a permanent command-line option. The C API
exposes the same bits through `BV_TERM_ABSTRACTION_SCHEMA_GROUPS`; unknown or
negative mask bits are rejected.

Every refinement clause is permanent and must therefore be a theorem about
the operation. A candidate decides only *which* theorem is useful to add; it
does not appear as a premise unless the installed theorem explicitly guards
on that value. Once no useful schema remains, STP either blocks the current
operand pair or installs the ordinary exact encoding, according to the
operation and remaining allowance.

Useful diagnostics are:

```sh
build/stp -t --bv-term-abstraction=1 input.smt2
build/stp -s --bv-term-abstraction=1 input.smt2
```

`-t` reports candidates, abstractions, refinement rounds, blocking lemmas,
aggregate schema lemmas, and the exact partition of schema firings over the
sixteen groups. `-s` prints each selected schema by name and the SAT/backend
telemetry. The C counter API likewise exposes one counter for every group;
the group counts always sum to the aggregate schema count.

## Source layout

The principal implementation files are:

- `include/stp/ToSat/BVAbstractionRefiner.h`
- `lib/ToSat/BVAbstractionRefiner.cpp`
- `include/stp/ToSat/BVExactEncoder.h`
- `lib/ToSat/BVExactEncoder.cpp`
- `include/stp/ToSat/BitBlaster.h`
- `lib/ToSat/BitBlaster.cpp`
- `include/stp/STPManager/UserDefinedFlags.h`
- `lib/STPManager/UserDefinedFlags.cpp`

`BVAbstractionRefiner` reads a candidate, chooses a violated fact, tracks
which unconditional facts are installed, and emits the refinement.
`BVExactEncoder` builds a theorem with the normal `BitBlaster`, sends it
through the normal AIG/CNF path, and splices the resulting clauses onto the
live operand/result SAT variables. This keeps exact fallback and complex
synthesised lemmas aligned with STP's ordinary encoding.

`UserDefinedFlags` defines the stable group ordinals, default mask, parser,
and formatter used by the CLI and C API. The chooser records the group on
every selected fact, and a single counter helper increments both the
aggregate and exactly one group counter.

The imported lemma source used for reconciliation was:

```text
/home/avj/clones/bitwuzla
e92a4c517bc4aa9c65551947f7bffe9a57236151
src/solver/abstract/abstraction_lemmas.cpp
src/solver/abstract/abstraction_module.cpp
```

The relevant paper is:

> Aina Niemetz, Mathias Preiner, Yoni Zohar. *Scalable Bit-Blasting
> with Abstractions.* CAV 2024, LNCS 14681, pp. 178-200.
> doi:10.1007/978-3-031-65627-9_9.

Both projects use the MIT licence. STP's circuits were implemented against
STP's bit-blaster rather than copied from Bitwuzla's node API.

## Final lemma inventory

### Unsigned division

STP has 33 unconditional `DivLemma` entries. The observed entries are
ordered by their measured firing count; the unobserved tail retains Bitwuzla
registry order:

```text
DivisorAboveShiftedDividend
QuotientBelowNegatedDivisor
DividendAboveNegatedAnd
DividendZero
DivisorEqualsDividend
DivisorLessOneAboveShiftedDividend
DividendAboveShiftedDoubleQuotient       (UDIV15)
QuotientNotNegatedAnd                    (UDIV ref9)
DivisorAllOnes
DividendAboveDoubledShiftedDivisor       (UDIV ref14)
DividendNotTwiceQuotientPlusOr           (UDIV ref33)
QuotientAboveDoubledShiftedDividend      (UDIV ref16)
DividendAboveOrAndDoubledDivisor         (UDIV ref17)
MaskedDividendAboveDivisorAndQuotient    (UDIV ref12)
DividendAboveQuotientXorShifted          (UDIV ref26)
ShiftedDividendNotOr                     (UDIV ref19)
DividendAboveOrAndDoubledQuotient        (UDIV ref18)
DividendAboveDivisorXorShifted           (UDIV ref27)
UdivRef10, UdivRef11, UdivRef20, UdivRef21, UdivRef23,
UdivRef24, UdivRef25, UdivRef28, UdivRef29, UdivRef30,
UdivRef31, UdivRef32, UdivRef34, UdivRef36, UdivRef38
```

The remaining enabled Bitwuzla facts are represented by STP's pre-existing
schemas:

- zero divisor: `s = 0 -> q = ~0`;
- power-of-two divisor: `s = 2^k -> q = x >> k`;
- nonzero-divisor quotient bound: `q <=u x`;
- the divisor-one case is subsumed by the power-of-two schema.

The branch also adds an STP-specific threshold family:

```text
for 0 < k < W:
q >=u 2^k  <->  s <=u (x >> k)
```

Only the two boundaries around the candidate quotient's highest set bit need
to be checked. The finite ranked lemma registry is tried before this
open-ended family. The first full regression run found that the opposite
order could consume all 32 schema rounds on a 256-bit term and starve UDIV15,
forcing an exact divider. The corrected order preserves the UDIV15
regression.

### Unsigned remainder

The transcribed `RemLemma` registry contains 12 entries and enables 11:

```text
DividendZero, DivisorEqualsDividend, DividendBelowDivisor,
RemainderBelowDivisorDisabled (UREM ref6; tested but deliberately disabled),
DividendWithinDivisorOrRemainder, DividendAboveRemainderOrAnd,
RemainderOutsideOperandsNotOne, RemainderNotOrOfComplements,
RemainderInOperandsAboveLowBit, DividendNotOrOfNegations,
DifferenceAboveRemainder, XorAboveRemainder
```

`UremRef6` is omitted from Bitwuzla's active registry. It is redundant in
STP: when `s != 0`, the existing `r <u s` fact gives the same upper bound,
and when `s = 0` its all-ones bound is vacuous.

The existing schemas cover:

- `s = 0 -> r = x`;
- `s = 2^k -> r = x & (2^k - 1)`;
- `r <=u x`;
- `s != 0 -> r <u s`.

The branch adds the quotient-one band:

```text
s <=u x  and  (x - s) <u s  ->  r = x - s
```

This spelling avoids overflow from `x < 2*s`. Its premise is false when
`s = 0`, so it does not conflict with totalised zero-divisor semantics.

### Multiplication

There are 14 general `MulLemma` entries, each offered in both operand
readings where applicable:

```text
FactorAndProductNotOr (MUL ref3), MulRefN3,
MulRef1, MulRefN5, MulRefN6, MulRef14, MulRef15, MulRefN9,
MulRef18, MulRefN11, MulRefN12, MulRefN13, MulRef13, MulRef12
```

They complete Bitwuzla's active registry after accounting for STP's existing
schemas:

- power-of-two and negative-power-of-two operands;
- odd-product parity;
- operand-derived trailing zeros;
- the MUL8 zero-product/odd-operand fact, encoded directly as
  `odd(x) and s != 0 -> t != 0`.

The branch additionally installs the exact low `min(3, W)` product bits
after the algebraic registry has no violated fact left. Higher result bits
remain unconstrained.

### Addition

All 13 Bitwuzla ADD facts are present:

```text
AddZero, AddSame, AddInv, AddOverflow, AddNoOverflow, AddOr,
AddRef6, AddRef7, AddRef8, AddRef9, AddRef10, AddRef11, AddRef12
```

Asymmetric forms are offered in both operand readings. STP records the
special lowering in which one operand is syntactically negated and uses the
effective two's-complement operand in both lemmas and exact fallback.

After the registry has no useful fact, STP installs the exact low
`min(3, W)` sum bits. Addition's eventual full exact fallback reuses the
same prefix encoder at width `W`, avoiding two implementations with
different polarity behaviour.

### Paired division/remainder

When syntactically identical operands occur in both
`q = bvudiv(x, s)` and `r = bvurem(x, s)`, the refiner can assert either:

```text
low3(x) = low3(q*s + r)
x = q*s + r                         (modulo 2^W)
```

The pairing is by AST identity and width, not by candidate value. The first
form is the inexpensive `divrem-pair` group; the second is the stronger
`divrem-full` group. Both relationships also hold for `s = 0`, because
SMT-LIB gives `q = ~0`, `r = x`, and therefore `q*0+r = x`.

The shared fact is charged to both records' schema allowances. A violating
pair receives this relationship before either member spends an individual
schema or value-pair lemma in that round. Candidate reads and emitted clauses
use each durable abstraction record's owned result variables, so pairing
remains correct when an AST-keyed map points at a newer encoding epoch.

## Why the implementation is sound

The imported algebraic facts have two independent representations:

1. A width-independent predicate over least-significant-bit-first
   `std::vector<bool>` values, used only to decide whether the current
   candidate violates the fact.
2. A BitBlaster or direct-CNF encoding over live SAT variables, asserted
   permanently.

Tests compare those representations. Selection never makes a false fact
true: if a chooser or its ordering were wrong, it could waste time, but the
installed circuit still has to be a theorem.

The important semantic boundaries are explicit:

- `bvudiv x 0 = ~0`;
- `bvurem x 0 = x`;
- addition and multiplication are modulo `2^W`;
- low result bits of addition and multiplication depend only on equally low
  operand bits;
- quotient low bits do **not** have that property and are not prefix-encoded;
- width-restricted synthesised facts are never evaluated or installed
  outside their applicable widths;
- `+0/-0`, NaN, infinity, rounding, and FP underflow do not appear at this
  layer: the abstraction sees only the exact BV operations produced by FP
  lowering and preserves those BV operations' semantics.

Exact escalation uses the same arithmetic BitBlaster and AIG/CNF conversion
as an ordinary non-abstracted solve. It is therefore a scheduling change, not
an alternate arithmetic definition.

Incremental solver rebuilds clear `BVAbstractionRefiner`, re-harvest every
record, and reinstall refinements against the fresh SAT variable epoch.
Installed-schema state, including paired DIV/REM state, cannot survive after
the clauses and variables it described have been discarded.

## Test coverage

The main focused tests are:

- `tests/unit-tests/BVAbstractionLemma_Test.cpp`
- `tests/unit-tests/BVAddLemma_Test.cpp`
- `tests/unit-tests/BVDivSchema_Test.cpp`
- `tests/unit-tests/BVMultSchema_Test.cpp`
- `tests/unit-tests/BVLowPrefixSchema_Test.cpp`
- `tests/unit-tests/BVDivRemSchema_Test.cpp`

For every imported registry:

- the expected registry size is pinned;
- the true operation result satisfies every applicable lemma at every width
  from 1 through 6;
- every lemma excludes at least one arbitrary operand/result triple;
- at width 4, the emitted circuit permits exactly the triples accepted by
  the independent predicate (4,096 triples per lemma);
- smaller applicable widths receive the same predicate/circuit comparison;
- exceptional width restrictions are asserted explicitly.

Focused coverage for the four newest rules includes:

- every four-bit UDIV threshold, including divisor zero;
- exhaustive ADD and MUL low-prefix CNF checks, negated ADD operands, and a
  deliberately unconstrained high result bit;
- exhaustive quotient-one remainder predicates and clauses, including
  divisor zero;
- true DIV/REM results at widths 1 through 6;
- all 65,536 arbitrary four-bit `(x,s,q,r)` tuples for recomposition;
- a live refiner test showing identical DIV/MOD records are paired and the
  violating candidate is rejected.

The final local qualification command was:

```sh
cmake --build build -j24
ctest --test-dir build --output-on-failure -j24
```

Result at `9d763349`:

```text
100% tests passed, 0 tests failed out of 172
```

That includes both query-file configurations. Each discovered 827 tests,
with 6 unsupported, under normal CaDiCaL 3.0.1 and again with
`--cadical-factor=off`.

This local build did not exercise the repository's complete CI matrix.
MiniSat, simplifying MiniSat, CryptoMiniSat, Riss, CaDiCaL 2.1, and Windows
builds remain a PR/CI qualification item.

## Commit sequence

These are the 15 code/test commits after `upstream/master`, oldest first:

1. `e6f4619d Add the UDIV15 abstraction fact`
   - Adds the highest-firing omitted UDIV fact and safe variable left/right
     shifts.
2. `9988a606 Refine zero products with an odd multiplier`
   - Adds the compact MUL8 implication in both commutative readings.
3. `2738781a Prepare BV refinement for the complete lemma set`
   - Widens installed-schema masks to 64 bits and factors the common
     ternary-lemma AIG/CNF splice.
4. `a1255e51 Add the remaining observed UDIV abstraction facts`
   - Adds every remaining UDIV fact observed in the ranking corpus.
5. `d9bb8da9 Complete the UDIV abstraction lemma registry`
   - Adds the enabled, unobserved UDIV tail.
6. `b8e80295 Add the UREM abstraction lemma registry`
   - Adds the complete UREM registry, with upstream-disabled UremRef6 kept
     explicit and disabled.
7. `c07ff56c Complete the multiplication abstraction lemma registry`
   - Adds the remaining general multiplication facts and both operand
     readings.
8. `446d319c Add the complete addition abstraction lemma registry`
   - Adds every ADD fact and handles the recorded negated-operand lowering.
9. `b3b4dc12 Qualify the complete BV lemma registries`
   - Extends applicable-width, registry-completeness, circuit-equivalence,
     public-flag, and counter checks.
10. `5932911a Keep the BV fallback regression registry-independent`
    - Makes the exact-fallback regression independent of which schema is
      ranked first.
11. `21c76364 Refine unsigned division by quotient thresholds`
    - Adds power-of-two quotient magnitude thresholds and puts them after the
      finite ranked registry to prevent schema-budget starvation.
12. `6dfa0337 Refine arithmetic with exact low prefixes`
    - Adds exact low-three-bit ADD/MUL refinements and shares the ADD encoder
      with full exact fallback.
13. `a032a19c Refine remainder in the quotient-one band`
    - Adds the overflow-safe conditional `r = x-s` region.
14. `381cc401 Relate paired division and remainder abstractions`
    - Adds low-prefix recomposition across matching DIV/REM records.
15. `9d763349 Group BV abstraction schemas by qualification`
    - Adds the named CLI/C-API mask, selects the corpus-qualified inherited
      profile, attributes coverage counters, and tests every gate and alias.

The handoff/documentation commit follows those 15 and intentionally contains
no source change.

## Measurements with positive local effects

### UDIV15

On the 256-bit regression that negates UDIV15:

- before: 25.56-25.88 s and 607-611 MB over three paired runs;
- after: 4.54-4.73 s and 113-116 MB.

A 1,029-file Certora coverage sweep found 55 consumers. One 30 s pass moved
from 9 to 10 solves. Five boundary trials consistently gained files 1044 and
1243 and lost 0433; at 120 s the change exchanged 1243 for 0433. The honest
aggregate verdict is neutral, despite the decisive target regression.

Raw logs, while they survive:

```text
/tmp/stp-udiv15.slOIr4
```

### MUL8

On the 256-bit target regression:

- before: 0.90-1.13 s and 211-214 MB over five runs;
- after: 0.01-0.02 s and 25-26 MB.

The 1,029-file Certora coverage pass installed the fact 144 times in 84 files.
Paired 30 s runs over those consumers solved the same four files and timed out
on the same 80, with no answer disagreement. Again, the target win is real
and the industrial aggregate is neutral.

Raw logs, while they survive:

```text
/tmp/stp-mul8.hy3HGI
```

## Neutral or negative evidence

### The initial division fact set

The division schemas already merged in PR #989 fire frequently but did not
improve the 1,029-file Certora family beyond noise. Across the 73 hardest
files, the first five facts fired 784 times; firing was not the missing
ingredient. Three purpose-built division regressions did improve from a
60-second timeout to 0.01-0.74 s because the installed fact was the crux of
their refutation.

Repeated solve counts on this family showed a spread of 13 files for an
unchanged binary. A one-pass net difference smaller than that is not
evidence.

### Immediate exact escalation

Experimental commit `c8935a5e` on branch
`bv-abstraction-immediate-exact` disables value-pair lemmas and installs the
ordinary exact BVMULT/BVDIV/BVMOD encoding as soon as no schema applies. It
was sound, modestly helped MiniSat on the FP64 glycerol probe, and hurt
CaDiCaL. It remains an experimental knob, not a candidate default.

### Exact-encode every remaining heavy record

Experimental commit `320bb12b` exact-encodes all remaining heavy arithmetic
records in deterministic insertion order after the first inconsistency. On
FP64 glycerol it reduced four SAT stages to two but grew the final CNF from
1.29 million to 3.45 million clauses and slowed CaDiCaL 2.1 from a 6.56 s to
an 11.12 s median. Broad early escalation is rejected.

### Schema barrier

Experimental commit `cc16c57f` implements the faithful global barrier:

1. scan all inconsistent records;
2. when any schema applies, emit schemas only and defer exact fallback;
3. on a schema-free pass, exact-encode only currently inconsistent
   no-schema records together;
4. never exact-encode candidate-consistent records.

On FP64 glycerol it preserved the final 313,266-variable,
1,289,475-clause CNF and reduced six SAT stages to five, but seven live runs
moved only from a 7.22 s control median to 7.16 s. FP16/FP32/FP64
`fba_none_tol1` medians moved from 3.86/5.84/35.93 s to
3.75/5.83/35.93 s. These are neutral results.

The dynamic clause recorder/replayer in experimental commit `598096f8`
showed that fresh-final replay could improve from 8.01 s to 5.92 s while the
retained staged solve did not. The final CNF alone is therefore not the whole
effect; learned state, inprocessing history, and when clauses enter remain
important. The barrier did not reproduce Bitwuzla's advantage.

Raw logs, while they survive:

```text
/tmp/stp-schema-barrier.qPVrWY
/tmp/stp-schema-sweep.2QVdmK
/tmp/stp-bv-immediate.Ww3y1k
/tmp/stp-replay-dimacs.5w0WVp
```

These four experimental commits are not in the present branch.

### Allowance scaling and partial exact encoding

Width-scaled value-pair allowances did not produce a repeatable difference on
the measured FP corpus; the default remains the flat ceiling. Incremental
partial multiplication bit-blasting remains default-off and does not have
enough evidence to recommend it. Neither should be mixed into the final
lemma qualification sweep.

## Completed corpus qualification

The final sweep searched
`/mnt/baranem/smt2_problems/non-incremental` rather than selecting only the
purpose-built regressions:

- 3,557 QF_BV/QF_ABV files whose source contains `bvudiv` or `bvurem`;
- 3,385 completed coverage runs from that set;
- 287 files with an abstracted division/remainder consumer;
- 1,580 files that installed at least one schema;
- a separate 20,846-file `bvmul` source set, with 20,745 completed coverage
  runs and 184 actual wide-multiplication consumers.

No answer disagreement was observed in any corpus, boundary, ablation, or
repeat. The important result is not that all of the facts are correct—the
exhaustive tests already establish that—but that only two new families earned
a place alongside the established `base` profile.

### UREM registry

The first screen over 20 natural UREM consumers moved from 13 to 17 solves at
a two-second budget, without a loss or disagreement. Four wide ecrw cases
then reproduced the gain three times each:

| Instance suffix | Full UREM wall time | Full UREM peak RSS |
| --- | ---: | ---: |
| `bw512_3` | 0.33 / 0.33 / 0.33 s | 55-59 MB |
| `bw512_4` | 0.28 / 0.28 / 0.28 s | 60-62 MB |
| `bw512_16` | 1.26 / 1.32 / 1.20 s | 85-87 MB |
| `bw512_19` | 1.27 / 1.27 / 1.24 s | 84-87 MB |

The predecessor without the UREM registry reached the external limit on most
runs at 8.90-9.02 seconds and roughly 2.19 GB. These are decisive construction
and search improvements, not timing noise.

A temporary per-lemma ablation established which relationship matters:

- removing `UremRef4` still solved all four cases in every repeat; the chooser
  selected `UremRef8` after `UremRef5` instead;
- removing `UremRef5` left the two small cases solved, but `bw512_16` and
  `bw512_19` both exhausted the limit twice at 9.40-9.56 seconds and roughly
  2.22 GB.

`UremRef5` is therefore essential to the two hard cases; `UremRef4` is not.
The whole enabled UREM registry remains one group because its broader screen
was positive and loss-free, and because per-lemma public flags would expose
implementation ordering rather than a useful user-facing policy.

### MulRef3

On `rw_rule_candidate_vmcai_2022_bw512_7.smt2`, three interleaved repeats
gave:

| Groups | Wall time | Peak RSS |
| --- | ---: | ---: |
| `base` | 3.66 / 3.68 / 3.61 s | 765-768 MB |
| `base,mul-ref3` | 0.12 / 0.12 / 0.12 s | 63-67 MB |
| `all` | 0.12 / 0.13 / 0.12 s | 64-67 MB |

The qualified profile fires six `base` facts and one `mul-ref3` fact on this
target; no opt-in group fires. This isolates the gain and shows that the rest
of the complete stack is unnecessary for it.

### Groups retained only for explicit experiments

The complete stack regressed the broadest 1,580-consumer comparison at a
two-second budget: solves fell from 1,374 to 1,336, the median rose from
0.64 to 0.73 seconds, common-solve time rose from 830.19 to 893.36 seconds,
and there were 40 gains against 78 losses. All five ecrw gains were real, but
77 SPEAR losses made this unsuitable as an inherited profile.

The group-level evidence explains the default mask:

- `add`: 1,368 to 1,337 solves over 1,550 consumers; median 0.64 to 0.69
  seconds and common-solve total 821.14 to 865.94 seconds. Repeating the 95
  changed files at five seconds still left ADD stably harmful, with no single
  lemma accounting for the reversal.
- `mul8`: 25 to 22 solves over 53 consumers. The three lost files eventually
  solved at five seconds, but slowed from 0.53-0.55 to 1.74-1.79 seconds.
- multiplication low prefixes: 77 to 75 solves over 125 consumers; median
  0.62 to 0.765 seconds and common total 48.82 to 54.94 seconds.
- all ADD/MUL prefixes together: a nearly neutral 1,133 to 1,135 solves over
  1,346 consumers, but median and common total still worsened from 0.74 to
  0.77 seconds and 807.67 to 830.83 seconds.
- quotient thresholds: the same 72 of 78 solves, with common total moving
  from 6.72 to 6.95 seconds.
- quotient-one remainder: repeatable but balanced at three gains and two
  losses, with slightly worse common-solve time.
- paired DIV/REM recomposition: neutral on its three natural consumers.
- UDIV15 and the remaining observed/unobserved UDIV facts: neutral on the
  broad corpus. UDIV15 retains its strong synthetic regression, but it did
  not earn inherited-profile status.
- the remaining MUL registry has no isolated broad improvement sufficient to
  overcome the losses seen when the complete tail is active.

A temporary selective build at `c07ff56c`, with MUL8 removed and before ADD
and the later STP-specific facts, provided a useful consistency check rather
than a final profile: div/rem consumers moved from 1,378 to 1,385 solves and
wide-multiplication consumers remained at 119 solves while their common total
fell from 45.58 to 35.97 seconds. Repeating the changed sets at five seconds
confirmed the gains. The named mask is preferable because it isolates the
two relationships that later target ablations actually justified.

Raw logs, while the temporary directory survives, are under:

```text
/tmp/stp-bv-corpus.2fP256
```

## Recommended disposition and remaining work

Keep the complete sound implementation behind the named groups. Do not
silently discard tested research code, but do not make the whole registry
tail the inherited behaviour either. The qualified policy is:

```text
term abstraction off by default
schemas on when abstraction is requested
schema groups = base,urem,mul-ref3
```

`--bv-term-abstraction-schema-groups=all` is the reproducibility and future
research setting. Individual opt-in groups make later workload-specific
qualification possible without rebuilding or carrying private patches.

The remaining work is integration rather than lemma discovery:

- run the repository CI matrix, particularly the non-CaDiCaL and Windows
  configurations not present in this build;
- decide whether review is clearest as this checkpoint or as an ordered PR
  series, without changing the qualified default;
- if requested during review, repeat the UREM screen on another independent
  remainder-heavy corpus.

Further low-frequency lemmas, schema batching, affine-equality preprocessing,
and broad exact-escalation changes are not justified by the collected
evidence. New work should return to preprocessing or refinement/SAT
architecture unless a new workload exposes a concrete missing relationship.
