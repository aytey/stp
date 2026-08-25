# Bit-vector abstraction work: final handoff

Date: 2026-08-25

Branch: `cegar-variable-shift-udiv15`

Code stack documented through: `381cc401`

Base: `87be10ce` (`upstream/master`, merge of PR #990)

Worktree used for this stack:
`/home/avj/clones/stp/cegar-next-lemmas`

## Executive summary

The implementation side of this line of work is now broad enough to call
complete:

- STP represents every enabled Bitwuzla UDIV, UREM, MUL, and ADD abstraction
  lemma from the local Bitwuzla source used for the comparison.
- The one UREM lemma Bitwuzla defines but leaves out of its active registry is
  also transcribed and tested, but deliberately remains disabled in STP.
- STP's older divisor-value, bound, power-of-two, trailing-zero, odd-product,
  and exact/value-pair fallbacks remain in place.
- Four STP-specific facts have been added after completing the imported
  registries: quotient magnitude thresholds, exact low prefixes for addition
  and multiplication, a quotient-one remainder band, and paired DIV/REM
  low-prefix recomposition.
- Candidate predicates, emitted circuits or clauses, applicability
  restrictions, totalised zero-divisor behaviour, and complete end-to-end
  regressions are tested.

This does **not** mean the complete stack should be merged as one feature.
Correctness qualification is substantially ahead of performance
qualification. UDIV15 and MUL8 have focused measurements. The low-frequency
registry tail and the four newest STP-specific rules do not yet have the
consumer-guided ablation needed to decide whether they help real workloads.

The correct next action is a final coverage-first, per-commit performance
sweep. Do not add another lemma family before doing it. If that sweep is
neutral, consider the abstraction-lemma research complete and return to
preprocessing or solver/refinement architecture.

The older `/home/avj/clones/stp/NEXT_CEGAR_LEMMAS.md` described what was
missing before this stack. It is now stale and this file supersedes it.

## Scope and defaults

The base already contains the general BV term-abstraction machinery and the
initial division work merged in PR #989:

- `--bv-term-abstraction=1` abstracts sufficiently wide `BVPLUS`,
  `BVMULT`, `BVDIV`, `BVMOD`, ITE, and signed/unsigned inequalities.
- `--bv-abstraction-width=N` sets the shared width floor; its default is 64.
- `--bv-term-abstraction-mult=0` excludes the expensive multiplication,
  division, and remainder family.
- The ITE, addition, and comparison families have their own scope flags.
- `--bv-term-abstraction-schemas=1` enables algebraic schemas. The schema
  flag defaults to true, but term abstraction itself defaults to false.
- `--bv-term-abstraction-rounds=32` separately caps schema rounds and
  value-pair blocking rounds for a heavy arithmetic record. Schema rounds do
  not consume the blocking allowance; after the blocking allowance is spent,
  the ordinary exact operation is installed.
- `--bv-term-abstraction-inc-bitblast=1` is a separate, default-off,
  multiplication-only partial-exact experiment.

Signed division and remainder are translated to unsigned operations before
bit-blasting, so they do not require separate abstraction registries.

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
and aggregate schema lemmas. `-s` prints each selected schema by name and
the SAT/backend telemetry.

## Source layout

The principal implementation files are:

- `include/stp/ToSat/BVAbstractionRefiner.h`
- `lib/ToSat/BVAbstractionRefiner.cpp`
- `include/stp/ToSat/BVExactEncoder.h`
- `lib/ToSat/BVExactEncoder.cpp`
- `include/stp/ToSat/BitBlaster.h`
- `lib/ToSat/BitBlaster.cpp`

`BVAbstractionRefiner` reads a candidate, chooses a violated fact, tracks
which unconditional facts are installed, and emits the refinement.
`BVExactEncoder` builds a theorem with the normal `BitBlaster`, sends it
through the normal AIG/CNF path, and splices the resulting clauses onto the
live operand/result SAT variables. This keeps exact fallback and complex
synthesised lemmas aligned with STP's ordinary encoding.

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
UdivRef9
DivisorAllOnes
UdivRef14
UdivRef33
UdivRef16
UdivRef17
UdivRef12
UdivRef26
UdivRef19
UdivRef18
UdivRef27
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
UremRef2, UremRef4, UremRef5,
UremRef6 (transcribed and tested, deliberately disabled),
UremRef7, UremRef8, UremRef9, UremRef10, UremRef11,
UremRef12, UremRef13, UremRef14
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
MulRef3, MulRefN3,
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
`q = bvudiv(x, s)` and `r = bvurem(x, s)`, the refiner can assert:

```text
low3(x) = low3(q*s + r)
```

The pairing is by AST identity and width, not by candidate value. Only the
low prefix is built. This relationship also holds for `s = 0`, because
SMT-LIB gives `q = ~0`, `r = x`, and therefore `q*0+r = x`.

The shared fact is charged to both records' schema allowances. A violating
pair receives this relationship before either member spends an individual
schema or value-pair lemma in that round.

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

- `tests/unit-tests/BVDivLemma_Test.cpp`
- `tests/unit-tests/BVRemLemma_Test.cpp`
- `tests/unit-tests/BVMulLemma_Test.cpp`
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

Result at `381cc401`:

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

These are the 14 code/test commits after `upstream/master`, oldest first:

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

The handoff/documentation commit follows those 14 and intentionally contains
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

## What is not yet measured

No defensible performance conclusion exists yet for:

- the complete low-frequency UDIV registry tail;
- the UREM registry on a broad remainder-heavy corpus;
- the complete MUL registry tail;
- the ADD registry;
- quotient power-of-two thresholds;
- exact low ADD/MUL prefixes;
- the quotient-one remainder band;
- paired DIV/REM low-prefix recomposition.

The tests establish that these are sound implementations of useful
relationships. They do not establish that spending a refinement round and
adding their clauses improves SAT search.

## Outstanding qualification sweep

Use coverage to make the timing experiment small rather than running every
commit over every file.

### 1. Build the relevant boundaries

At minimum compare:

```text
87be10ce  merged master baseline
e6f4619d  + UDIV15
9988a606  + MUL8
5932911a  + complete imported registries and qualification
21c76364  + quotient thresholds
6dfa0337  + low ADD/MUL prefixes
a032a19c  + quotient-one remainder
381cc401  + paired DIV/REM recomposition
```

The comparisons after `5932911a` are intentionally adjacent: each isolates
one new rule. Compare `9988a606` to `5932911a` to judge the imported
low-frequency registry tail as a group; split that group further only if its
coverage or performance warrants it.

### 2. Run coverage-only passes

Use `-s` and `-t` to identify consumers and collect:

- candidates and abstracted terms by operation kind;
- named schema firings;
- refinement rounds;
- blocking and schema lemma counts;
- exact-fallback events;
- SAT calls and fixed-conflict telemetry;
- AIG/CNF size, construction time, wall time, and peak memory.

Suggested workloads:

- the 1,029 Certora QF_UFBV files for UDIV and multiplication continuity;
- a broad QF_BV remainder/division corpus, including the Cryptol
  `gcd_divides` family, for UREM and paired DIV/REM;
- LatendresseFP and SyntheticFBA for ADD/MUL prefixes after FP lowering;
- the established glycerol probes for continuity with the scheduling work.

Use explicit abstraction widths appropriate to the lowering under test.
The default floor of 64 will not exercise every binary32-derived arithmetic
term; earlier FP experiments used widths around 24 and 33 for that reason.

### 3. Time only consumers

For each rule, compare its commit to its immediate predecessor over files
where that rule actually fired. Interleave versions and use repeated runs.
Report gains and losses separately, not only a net solve count.

Use both:

- matched wall budgets for end-to-end solver value;
- fixed-conflict checkpoints for construction/refinement/search diagnosis.

CaDiCaL conflict counts are comparable only within the same backend and
configuration. Do not compare MiniSat and CaDiCaL conflict totals directly.

### 4. Keep criteria

Keep a rule only if:

- there are no answer disagreements;
- it fires on more than a purpose-built regression, or its target win is
  compelling enough to justify a deliberately narrow PR;
- gains survive repeats and are not merely exchanged for similar losses;
- it does not starve higher-value schemas or push terms prematurely to exact
  encoding;
- memory and final CNF growth remain acceptable.

A rule with zero or negligible natural coverage should be abandoned rather
than retained because it is mathematically attractive. A rule with a decisive
target regression and neutral aggregate behaviour can be proposed as a small,
independent PR with that limited claim; UDIV15 and MUL8 currently fit that
description.

### 5. Final hardening

After selecting the surviving commits:

- rebase/split them into reviewable PR branches;
- run the full repository CI matrix, especially MiniSat,
  simplifying MiniSat, CryptoMiniSat, Riss, CaDiCaL 2.1/3.0, and Windows;
- preserve concise aggregate measurements in commit or PR text rather than
  relying on `/tmp`;
- leave `--bv-term-abstraction` default-off unless a much broader
  qualification justifies changing it.

## Recommended disposition

Do not merge all 14 commits merely because the complete stack is sound.

The present evidence supports preparing UDIV15 and MUL8 as small,
independently reviewable changes. The registry-completion commits are valuable
as a controlled research implementation and make omissions explicit, but
need the sweep above before they become product changes. The four newest
rules should be judged independently at their commit boundaries.

If none of the unmeasured work survives that sweep, archive this branch and
its handoff rather than continuing to invent algebraic facts. Previous results
show that STP's larger remaining gap is not a missing list of lemmas.
