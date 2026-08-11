# Incremental solving in STP: architecture review, defect ledger, and roadmap

**Document status:** authoritative maintainer record for the `incremental-solving`
branch. Rewritten 2026-08-11 to carry the second architectural review and its two
reproduced soundness defects. The pre-existing material (reference-solver study,
state-lifetime audit, scoped-state design, closeout campaign evidence) is
retained below in Parts VI--X; nothing from the 2026-08-07/08 review has been
deleted, only re-ordered and annotated where it is now superseded.

`docs/incremental-solving.rst` remains the user-facing description of the
feature. This file is maintainer-facing: what is broken, what is proven correct,
what must not be re-chased, and what to do next.

---

## How to use this document

| If you are... | Go to |
|---|---|
| Picking up the branch cold | [Status board](#status-board), then [Part I](#part-i--open-defects) |
| About to fix a bug | [Part I](#part-i--open-defects) -- each defect has mechanism, witness, fix options, and a verification recipe |
| About to "investigate" something | [Part II](#part-ii--verified-correct-do-not-re-chase) first. Fourteen plausible-sounding concerns are already disproved there, several with measurements. |
| Deciding whether to merge | [Status board](#status-board) and [Part V](#part-v--work-queue) |
| Wondering why the design is like this | [Part III](#part-iii--architecture-assessment), then [Part VI](#part-vi--reference-solver-investigations) |
| Chasing performance | [Part IV](#part-iv--cost-model-and-measurements) |
| Looking for a specific finding | [Appendix B](#appendix-b--full-finding-ledger) -- all 44, with verification verdicts |
| Deciding what to do next | [Part V](#part-v--work-queue) -- tiered and re-ordered after the fixes; Tier 0 is the merge gate |

---

## Status board

**All fourteen tracked defects are now FIXED or closed.** **Three** of them
were silent wrong answers: D1 and D2 (`e1229764`, `926bf48f`), found by this
review, and **D14** (`87a77ac2`), found later and by accident. All three were
reachable with **no non-default flags on the path**, on logics STP is built
for; every witness is landed as a regression and the campaign harness now
validates the candidate's models by default (see
[Part V](#part-v--work-queue)).

**Read D14 before trusting this board.** It was not found by looking for
soundness defects. It came out of adversarially challenging **F43**, a *tidiness*
row about duplicated preprocessing code: the challenge agreed the refactor that
row asks for would be churn, then asked the question the refactor would have
hidden --- whether each of the four preprocessing prefixes still enforces what
its siblings enforce. One did not, and the gap was a wrong answer. The sweep
that produced this document had classified that area as cost-and-clarity. So
"no known soundness defect remains" is the honest status and has already been
wrong once; it is a statement about what has been looked for, not about what is
there. The relief-rebuild path is where all three of the last defects lived and
where the test suite is thinnest --- 11 of 82 files reach a rebuild at all, and
every one of them has to force `--incremental-reencode-limit` to get there.

Two tracked rows were fixed only at their headline, and their sub-items are
tracked separately: **D7b** (feed cap) is now fixed, and **D8b** (refinement
mass) is closed as declined-with-measurement.

**Every defect below is branch-introduced.** None reproduces on master --- see
[Validation against master](#validation-against-master) for the evidence, which
is per-defect.

### Defects

Status column: FIXED items keep their full write-up below, because the
mechanism is the part worth remembering.

| ID | Class | Status / severity | Default flags? | In master? | Evidence | Summary |
|---|---|---|---|---|---|---|
| [D1](#d1--soundness-private-elimination-privacy-is-decided-over-the-raw-stack) | soundness | **FIXED** `e1229764` | yes | no (branch-only code) | fixed + regression | `levelPrivate` decides eliminability over the *raw* stack; levels are encoded from the *ctx-substituted* stack |
| [D2](#d2--soundness-unit-promotion-pins-a-prepared-form-it-never-revalidates) | soundness | **FIXED** `926bf48f` | yes | no (branch-only code) | fixed + regression | Promotion pins a level's *prepared* conjuncts but only revalidates its *raw* conjunction |
| [D3](#d3--architecture-whole-base-re-simplification-is-welded-to-rebuildencodings) | architecture | **FIXED** `e093b0d2` | yes | no (branch-only code) | reproduced: 18.3 ms → 2.1 ms | A semantic whole-base pass fired on all four rebuild reasons, the two pure SAT-config latches included |
| [D4](#d4--cost-the-privacy-predicate-makes-a-no-op-check-quadratic-in-stack-depth) | cost | **FIXED / closed** | yes | no (branch-only code) | ~4x; remainder measured flat | Steady-state per-check work is O(depth²); this is what engagement-at-32 hides |
| [D5](#d5--architecture-the-exact-stack-block-cache-is-fronted-by-a-non-deterministic-pass) | architecture | **FIXED** `45504ef9` | `--array-equality` | no (branch-only *dependency* on master naming) | agent-measured | `RemoveUnconstrained` mints counter-named vars in front of the block cache: 4,177 → 56,299 vars over 15 *identical* repeats |
| [D6](#d6--measurement---incremental-profile-changes-the-relief-schedule-it-measures) | measurement | **FIXED** `635b3b04` | n/a | no (branch-only code) | agent-demonstrated | The profiler substitutes a different live-mass estimator, so it changes when rebuilds fire |
| [D7](#d7--policy-cbpeverfixed-does-not-measure-what-its-retirement-tier-needs) | policy | **FIXED** `8ab75f81`; D7b **FIXED** `e438bbba` | yes | no (branch-only code) | agent-reproduced; D7b reproduced + 2 regressions | A level's own assumed truth counts as "a fixing", so the 8-divergence tier is unreachable for array-free sessions. **D7b:** the feed cap was charged the sum of level DAG sizes, not what the engine retains, and a refusal was latched for the session though its charge is refunded on pop |
| [D8](#d8--cost-every-array-encode-installs-and-copies-back-the-whole-session-registry) | cost | **FIXED** `8ffd109f`; D8b **closed** `95014cd7` | array logics | **loop is master's**, blowup is not | agent-verified; D8b measured | Anchors re-conjoined for every read ever seen; registry deep-copied twice per encode. **D8b:** theory-lemma mass is keyed on the whole-stack conjunction, so any stack change drops all of it; measured at one spurious relief rebuild and 646 of 6800 lemmas re-derived, no time difference --- declined, see Tier 2.2 |
| [D9](#d9--contract-construct_counterexample_flag-was-made-sticky) | contract | **FIXED** `060cc34f` | yes | **no --- branch deleted master's reset** | agent-reproduced | One array round or `:produce-models` permanently disables the documented unchanged-stack cache shortcut |
| [D10](#d10--layering-a-node-construction-rewrite-is-gated-on-a-mutable-session-mode-flag) | layering | **FIXED** `0767b22a` | after any `push` | **no --- master folds unconditionally** | yes, incl. vs master | `SimplifyingNodeFactory` reads `UserFlags.incremental_solving`; contradicts the branch's own stated invariant |
| [D11](#d11--dead-backtrackh-canhandle-batchtablesseeded) | dead code | **FIXED** | n/a | no (branch-only code) | yes | A tested 273-line scoped-container library with zero production users; a `return true` seam; a write-only flag |
| [D12](#d12--cost-the-tosatbase-adapter-rebuilds-an-oall-session-symbols-map-per-call) | form | **closed** | array logics | no (branch-only code) | measured: no effect | Per-call cost is real but the call count is not; caching it and removing the copy both measured neutral. Contract fixed, optimisation declined. |
| [D13](#d13--conservatism-d1s-fix-refuses-eliminations-the-context-re-join-would-have-covered) | conservatism | **FIXED** | yes | n/a (introduced by `e1229764`) | eliminations restored; 1.5x faster | D1's fix refuses eliminations the `ctx` re-join would have covered; clean fix is a single elimination/inline transaction |
| [D14](#d14--soundness-the-relief-rebuild-keeps-a-definition-whose-dependency-it-just-dropped) | **soundness** | **FIXED** `87a77ac2` | yes (needs a relief rebuild) | no (branch-only code) | fixed + regression; 4 engines agree | The relief rebuild keeps a definition for an untouchable variable while `RemoveUnconstrained` drops the last constraint on a variable that definition mentions. The rebuilt base is strictly weaker than the raw base it replaces: `sat` on an `unsat` query |

### Verified correct (do not re-chase) — see [Part II](#part-ii--verified-correct-do-not-re-chase)

Retraction mechanism; activation-literal keying and pinning; unsat-core
conservatism; the frontend verdict cache including core-level recording; CaDiCaL
factor translation on all four literal paths; `IncrementalCBP`'s undo trail
(complete, all state enumerated); CBP prefix discipline by evaluation order;
array congruence-lemma permanence; deterministic-name uniqueness; the
`submittedClauses()` chokepoint; the cheap live-mass estimator's lower-bound
property; `SessionProfile::add()` completeness.

### Deferred from the previous review

Phase 0 item 7, the three-run timing campaign, remains the only open item of the
old roadmap. It was moot while D1/D2 stood; with both fixed it is runnable
again, and should be run with `--no-check-models` (model validation is not free
and would distort timings) against a correctness campaign that keeps it on.

---

## Validation against master

Every defect in this document was checked against master to establish that it is
a **branch regression** rather than a pre-existing STP bug. Result: **all
fourteen are branch-introduced; none reproduces on master.** D14 was added after
this section was first written; it is branch-only by construction, because
`resimplifyBaseAtRebuild` exists only on this branch, and its witness answers
`unsat` on master's batch pipeline as well as on Bitwuzla, cvc5 and Z3.

### Comparison baseline

| | |
|---|---|
| master revision | `d47f6b579424e852d5c1f566726649af63e4262c` --- **exactly `git merge-base HEAD master`**, so no master-side delta is in play |
| master build | rebuilt 2026-08-11 from that revision (the pre-existing binary was 41 commits / 121 files stale and was discarded) |
| binary provenance | `stp --version` reports SHA `d47f6b57…`; targets `stp` (library) **and** `stp-bin` (executable) both relinked |
| build configuration | `Release`, `ENABLE_ASSERTIONS=ON`, `USE_CADICAL=ON`, `USE_LIBBF=ON`, shared libs |
| compile defines | **byte-identical to the branch build**, including `-DNDEBUG` --- so the `#ifndef NDEBUG construct = true` paths are inactive on *both* sides and the comparison is like-for-like |

> ⚠ `make stp` builds the **library**; the executable target is `stp-bin`. A
> `make stp` alone leaves a stale `build/stp`, and `libstp.so` is linked
> dynamically, so a saved binary is never a valid A/B arm on its own.

### 1. The three soundness defects: four independent engines say `unsat`, the branch says `sat`

The witnesses were cross-checked against three external SMT solvers as well as
STP master, so the expected answer does not rest on STP's own reasoning or on my
hand-derivation of the formulas.

| Engine | Version |
|---|---|
| Bitwuzla | `0.9.1-dev-fix-216-funsolver-uaf@d733897b` |
| cvc5 | `1.3.5.dev+main@ed5e08073b` (run with `--incremental`) |
| Z3 | `5.0.0`, build `4af3410d104ad291437275ad1553d2b82b152727` |
| STP master | `d47f6b57` (see baseline above) |

Full `sat`/`unsat` answer **sequences** were compared, not just the final answer.

| Witness | Defect | checks | Bitwuzla | cvc5 | Z3 | STP master | STP branch |
|---|---|---|---|---|---|---|---|
| `w6.smt2` | D1 | 1 | unsat | unsat | unsat | unsat | **sat** ✗ |
| `w7.smt2` | D1 | 35 | 34×sat, unsat | *idem* | *idem* | *idem* | 34×sat, **sat** ✗ |
| `repro3.smt2` | D2 | 15 | 14×sat, unsat | *idem* | *idem* | *idem* | 14×sat, **sat** ✗ |
| `promote7.smt2` | D2 | 13 | 12×sat, unsat | *idem* | *idem* | *idem* | 12×sat, **sat** ✗ |

**All four engines agree on all 64 answers.** The branch matches on 60 of 64 and
diverges on exactly one check per file --- always the **last** one, always `sat`
where the consensus is `unsat`.

That divergence pattern is itself confirmatory: the branch's answers are correct
right up until the level that triggers the defect arrives, which is precisely
what both mechanisms predict --- for D1, the deeper level whose `ctx`-substituted
encoding names the eliminated variable; for D2, the level that makes a promoted
level's private variable shared.

Both defects are additionally isolable *within* the branch by a single flag:
`--no-incremental-promote-units` fixes D2, and `--incremental-auto-engage-at 0`
fixes both by routing to the batch path.

### 2. Structural argument: most defects cannot exist on master

`lib/Incremental/` and `include/stp/Incremental/` **do not exist on master**
(`git ls-tree` returns nothing), and the master binary rejects every new flag:

```
$ master/build/stp --incremental
Error: The following argument was not expected: --incremental
$ master/build/stp --incremental-promote-units      # same
$ master/build/stp --incremental-profile            # same
$ master/build/stp --incremental-auto-engage-at     # same
```

D1, D2, D3, D4, D6, D7, D11 and D12 are entirely inside that absent code, so they
cannot reproduce on master by construction.

### 3. The branch modifies 30 pre-existing master files --- three carry a defect

The branch touches these files that already existed on master (excluding tests,
scripts and docs):

```
include/stp/AST/ASTInternal.h                include/stp/Sat/{SATSolver,Cadical,CryptoMinisat5,
include/stp/AbsRefineCounterExample/           MinisatCore,Riss,SimplifyingMinisat}.h
  ArrayTransformer.h                         include/stp/Simplifier/RemoveUnconstrained.h
include/stp/STPManager/{STP,STPManager,       include/stp/{c_interface,cpp_interface}.h
  UserDefinedFlags}.h                        lib/AbsRefineCounterExample/ArrayTransformer.cpp
lib/Extensionality/ExtensionalityContext.cpp lib/Interface/{c,cpp}_interface.cpp
lib/NodeFactory/SimplifyingNodeFactory.cpp   lib/Parser/smt2.y
lib/STPManager/STP.cpp                       lib/Sat/{Cadical,CryptoMinisat5,MinisatCore,
lib/Simplifier/RemoveUnconstrained.cpp         RissCore,SimplifyingMinisat}.cpp
lib/CMakeLists.txt                           tools/stp/main.cpp
                                             tools/test_fprewrites/test_fprewrites.cpp
```

Only three of those carry a tracked defect, and each was checked directly:

**D10 --- `lib/NodeFactory/SimplifyingNodeFactory.cpp`. Reproduced as a
divergence from master.** Master folds `(= x x)` on floats to `ASTTrue`
unconditionally; the branch makes it conditional on
`UserFlags.incremental_solving`, which `push()` sets. Probe:

```smt2
(set-logic QF_FP) (declare-fun x () Float32)
[(push 1)]  (assert (= x x))  (check-sat)
```

| | without `(push 1)` | with `(push 1)` |
|---|---|---|
| master | node size **1** (folded) | node size **1** (folded) |
| branch | node size **1** (folded) | node size **2** (**not** folded) |

Node sizes are from `-s` and are identical at every pipeline stage
(`input asserts`, `After Constant Bit Propagation`, `After Propagating
Equalities`, `After Removing Unconstrained`, `After Domain Analysis`,
`After Pure Literals`, `After Split Extracts`, …). The incremental **driver never
engages here** --- QF_FP engages at solve 3 and this is solve 1 --- so this is the
branch's *batch* pipeline behaving differently from master purely because a
`push` occurred. That is the layering violation, demonstrated.

**D9 --- `lib/STPManager/STP.cpp`. Source-verified branch-introduced.** Master's
`TopLevelSTPAux` ends the derivation with

```cpp
  else
    bm->UserFlags.construct_counterexample_flag = false;   // present on master
```

which the branch deletes, making the flag monotone for the session. Verified by
`git diff master...HEAD -- lib/STPManager/STP.cpp`. The consequence on master's
own code path is extra counterexample-construction work, which is a cost rather
than an answer change; **I could not construct a CLI-visible observable for it**,
so D9 is recorded as source-verified, not reproduced. (The agent's reproduction
observed the branch-side consequence --- the frontend cache shortcut --- which is
branch-only code.)

**D8 --- `lib/AbsRefineCounterExample/ArrayTransformer.cpp`. The loop is master's;
the blowup is not.** The whole-table anchor loop that emits
`EQ(the_index, index_symbol)` for every row with a computed index is *pre-existing
master code*. It cannot misbehave on master because master clears the table on
every solve --- `ArrayTransformer.h:133-134` (`arrayToIndexToRead.clear();
ack_pair.clear();`) and `STP.cpp:734`. The branch's contribution is *persisting
the session registry and re-installing it into that table on every encode*, which
is what turns a per-query loop into an all-reads-ever loop.

**D5** is the mirror image: `RemoveUnconstrained`'s counter-based
`CreateFreshVariable` naming is master's and is harmless there; the branch
introduces a **cache that depends on that pass being deterministic**.

The remaining modified files are additive or mechanical: `ASTInternal.h` (uid
accessors), the `Sat/*` facade split (`addClauseInternal` + capability virtuals,
all with declining defaults), `RemoveUnconstrained`'s extra defaulted parameter,
`smt2.y` (`check-sat-assuming`/`get-unsat-assumptions` now implemented instead of
`unsupported`), and the two interface files.

### 4. Corpus differential: no other divergence

Master `d47f6b57` versus the branch **at default settings** (no flags), over the
72 files of `tests/query-files/incremental-tests/` plus the repository's scratch
regressions (`moo.smt2`, `fp_soundness_bug.smt2`, `reduced-Problem101.smt2`),
comparing full `sat`/`unsat`/`unknown` answer sequences:

```
identical answer streams : 71
DISAGREEMENTS            :  1   -> unsat-assumptions.smt2
no answers from either   :  0
```

The single flagged file is **not a defect**: master prints `unsupported` eight
times because `check-sat-assuming` and `get-unsat-assumptions` do not exist on
master at all. The branch implements them, and under the configuration its own
RUN line specifies (`--incremental`) it produces exactly the precise cores the
test expects.

One behaviour worth knowing, surfaced by running that file *without*
`--incremental`: `get-unsat-assumptions` then reports the **full** assumption set
rather than the minimal core, because the driver was not engaged and
`lastUnsatHasAssumptionGranularity()` is false. A superset of a core is a correct
core, and this fallback is documented at
`docs/incremental-solving.rst`, but it means **core precision silently depends on
whether the driver engaged** --- worth stating explicitly in the user-facing docs.

### 5. What this validation does and does not establish

- **Does:** every tracked defect is a branch regression; the expected `unsat`
  answers are confirmed by three external solvers as well as STP master, so they
  do not depend on STP's own reasoning; the branch's batch path matches master on
  71/72 corpus files; the only shared-code behavioural divergence found is D10.
- **Does not:** prove the branch has no *further* defects. This differential
  covers 72 small files chosen to exercise the driver, not the 22,999-file
  corpus, and it compares answers only. The campaign re-run demanded by
  [Part V](#part-v--work-queue) item 3 --- with `--check-sanity` on the
  incremental arm --- is still the required gate.

### Reproducing this validation

```sh
# --- independent confirmation of the expected answers ---
BZ=/home/avj/clones/bitwuzla/main/build/src/main/bitwuzla
CVC=/home/avj/clones/cvc5/main/build/bin/cvc5
Z3=/home/avj/clones/z3/master/build/z3
for w in w6 w7 repro3 promote7; do
  for s in "$BZ" "$CVC --incremental" "$Z3"; do
    printf '%-12s %s ' "$w" "$(basename ${s%% *})"
    $s $w.smt2 | grep -xE 'sat|unsat' | tail -1        # every one: unsat
  done
done

# --- STP master at the merge base ---
# master must be at the merge base, and BOTH targets must be built
cd /home/avj/clones/stp/master
git rev-parse HEAD                                   # d47f6b57… == git merge-base HEAD master
cd build && make -j20 stp stp-bin                    # 'stp' alone builds only the library
LD_LIBRARY_PATH=lib ./stp --version | sed -n 2p      # must print d47f6b57…

M="LD_LIBRARY_PATH=/home/avj/clones/stp/master/build/lib /home/avj/clones/stp/master/build/stp"
for w in w6 w7 repro3 promote7; do
  printf '%-14s master=%s\n' "$w" "$(eval $M --SMTLIB2 $w.smt2 2>&1 | tail -1)"   # all: unsat
done
```

---

## Provenance and method

### What was reviewed

| | |
|---|---|
| Branch | `incremental-solving`, tip `278552ce` ("Merge upstream/master into incremental-solving") |
| Base | `master`; diff base `master...HEAD` = 103 commits, 133 files, +18,185 lines |
| Builds used | `build/` (Release + assertions, CaDiCaL 3.0.1, FP, LibBF) and `bd-dbg/` (RelWithDebInfo + assertions). Both were current with the tip at review time. |
| Date | 2026-08-11 |

The previous review (2026-08-07/08) covered solver code through `ee8685bb`. The
~16 commits after it were **not** covered by that review and are where most of
this review's new material lives:

```
3d030827 Incremental: discard definitions from rejected trials
3933a396 C API: materialize lazy models before fd printing
826aaab1 Incremental: preserve trails when FP arrives late
20ea1b66 Incremental: delay reflexive FP equality folding      <-- D10
45a36a07 Incremental: narrow late FP trail retention
f3e9c1e0 Incremental: scope late FP trail retirement to array sessions
90186061 Incremental: require a stable base before inprocessing retirement
1b6e994c Incremental: batch overlapping CBP symbol walks
8ed8c0d4 Incremental: defer oversized first-solve CBP bootstrap
e5b1442? Incremental: preprocess changing exact-stack blocks
45b846fa Incremental: preprocess explicitly forced first array blocks
5ae90c7a Incremental: eliminate pure literals on forced first bases
56f14241 Incremental: collapse forced first BV stacks
f48c84fc Incremental: solve scoped BV blocks directly
cf4b29dc Incremental: make auto-engagement threshold configurable
06dbdccf Incremental: delay BV auto-engagement to solve 32     <-- see Part IV
```

### Method

Nine independent review lenses were run over the branch (retraction model;
preprocessing under retraction; CBP; arrays and refinement; extensionality and
FP; relief valve and accounting; frontend and engagement; SAT layer; complexity
and overreach). Each produced ranked findings with file:line evidence; **every
finding was then handed to an independent adversarial verifier instructed to
refute it**, which read the cited code itself rather than trusting the quoted
evidence. 44 findings; 12 CONFIRMED, 26 PARTLY (real but narrower or differently
scoped than claimed), 6 REFUTED.

The two soundness defects were then reproduced by hand against both builds
before being recorded here.

### Evidence classes used in this document

Every claim below carries one of these. Do not upgrade a claim's class without
redoing the work.

- **Reproduced** --- a witness file was run against a built binary and the wrong
  behaviour observed. Commands are in [Appendix C](#appendix-c--reproduction-command-reference).
- **Measured** --- a number was obtained from `--incremental-profile`, `perf`, or
  `-s` on a stated input. Timing numbers are indicative unless the note says
  interleaved quiet-box A/B (see the branch protocol: sequential timings swing
  30--50 %).
- **Code-verified** --- established by reading the code path end to end, with the
  reasoning recorded so it can be re-checked.
- **Agent-reported** --- produced by a review agent and survived adversarial
  verification, but not independently re-run for this document. Treated as a
  strong lead, not as settled fact.

---

# PART I — OPEN DEFECTS

## D1 — SOUNDNESS: private-elimination privacy is decided over the raw stack

**Class:** silent wrong answer (`sat` where `unsat`). One-directional: this
defect can never produce a wrong `unsat`.
**Reachable at:** default flags, pure `QF_BV`, automatic engagement.
**Evidence:** reproduced at tip `278552ce` on `build/` and `bd-dbg/`.
**Sites:** `lib/Incremental/IncrementalSolver.cpp:1687-1708` (`levelPrivate`),
`:1862-1872` (elimination decision), `:5306-5322` (ctx substitution),
`:5400-5424` (the "repair" join), `:2688-2745` (`recogniseDefinition`).

### Mechanism

Two different pieces of code read the same conjunct as a definition of two
*different* variables:

- `recogniseDefinition` (`:2688`) requires a `SYMBOL` on one side. Given
  `(= (bvnot v) y)` it reads **`y := ~v`** and `harvestPushed` puts that in `ctx`
  --- so a live `ctx` body now mentions `v`.
- `PropagateEqualities`, running inside `preparePiece`, reads the same conjunct
  as **`v := ~y`** (its `BVNOT` rule, `PropagateEqualities.cpp:582-586`, ungated).

`levelPrivate` is then asked whether `v` may be eliminated. It consults
`baseSymbols`, `symbolsOf(stack[j])` for the **raw** level conjunctions,
`bbMgr.symbolToBBNode`, the CBP-protected set, and a per-level conjunct count
that is *vacuous* at whole-level granularity (one raw conjunct ⇒ every count is
1). It does **not** consult `ctx`. `v` is declared private and its defining
equation is deleted from the formula.

Deeper levels are not encoded from their raw conjunctions --- they are encoded
from `SubstitutionMap::replace(level, ctx, …)` (`:5310`). So `v` reaches the
bit-blaster inside a deeper level's formula, **completely unconstrained**.

The one mechanism that is supposed to repair this --- re-joining the eliminated
definition into `ctx` at `:5400-5424` so `replace` expands `v` away --- declines
**silently** in three cases: already present; the occurs-check at `:5412` (which
is exactly what fires here, since expanding `~y` under `ctx[y] = ~v` yields `v`);
and the `defInlineCap` size test at `:5415`. When it declines, **nothing
retracts the elimination**. `screenNewContent` never sees substituted content, so
no later check catches it either.

The source comment at `:5392-5399` states the precondition correctly and then
draws the wrong conclusion:

> "The elimination itself stays (it is sound for the piece and its replay); only
> the context entry is withheld."

True for the piece. False for every deeper level substituted under a `ctx` entry
that still names the variable.

### Witness

`w6.smt2` (see [Appendix A](#appendix-a--witness-files)). `y = ~v` and
`y*y = y` force `y ∈ {0,1}`; the deeper level asserts `y > 1`. The `bvmul`
constraints exist only to keep constant-bit propagation from independently
refuting the query.

```
--incremental-auto-engage-at 0   (batch)     -> unsat   [correct]
--incremental                                -> sat     [WRONG]
--incremental-auto-engage-at 1               -> sat     [WRONG]
--incremental --check-sanity                 -> STP Error: the model does not satisfy an asserted formula
```

`w7.smt2` is `w6.smt2` preceded by 34 trivial push/check/pop rounds so the
session crosses the QF_BV engagement ordinal (35 `check-sat`s in total):

```
(no flags at all)                            -> sat     [WRONG]
--incremental-auto-engage-at 0   (batch)     -> unsat   [correct]
```

Both reproduce identically on `bd-dbg/`.

### Why 23,000 files of differential fuzzing did not catch it

The campaign compared **answer streams only**. This defect needs: a definition
`PropagateEqualities` harvests that `recogniseDefinition` refuses (BVNOT-headed
equations, XOR, some speculative BVPLUS/BVUMINUS shapes) --- otherwise
`harvestPushed`'s `ctx` entry repairs the hole; the occurs-check or size decline
to fire; CBP not to refute the query independently; and PE's candidate ordering
to prefer the compound side (which depends on child sort order). `--check-sanity`
catches it instantly, and was not part of the campaign.

### Fix

Make the eliminability predicate range over **everything that can reach the
encoder**, not over the raw stack. Concretely: maintain a symbol-set union over
live `ctx` bodies as entries are inserted, and add it to `protectedSymbols`
before `levelPrivate` is consulted. One extra clause in `levelPrivate`.

That also subsumes the join's repair role, so the declines at `:5412-5417`
become pure optimisation declines rather than silent soundness holes. With the
extra clause the `ctx` join at `:5400-5424` is provably inert for its stated
purpose and can be deleted.

**Cheap independent guard, worth landing regardless:** assert at the encode
boundary (`rootLit`, `:2963`) that no conjunct being encoded mentions a variable
in `activeEliminatedVars`. That single assert would have caught this class at
test time.

### Verification recipe

1. `w6.smt2` under `--incremental` must answer `unsat`.
2. `w7.smt2` with no flags must answer `unsat`.
3. Both under `--check-sanity` must not error.
4. `tests/query-files/incremental-tests/level-elimination.smt2` must still report
   `2 eliminated` --- the fix must not disable elimination wholesale.
5. Re-run the differential campaign **with `--check-sanity` on the incremental
   arm** (see [Part V](#part-v--work-queue)).

---

## D2 — SOUNDNESS: unit promotion pins a prepared form it never revalidates

**Class:** silent wrong answer (`sat` where `unsat`). One-directional.
**Reachable at:** default flags (`incremental_promote_units` defaults to true).
**Evidence:** reproduced at tip `278552ce` on `build/` and `bd-dbg/`.
**Sites:** `lib/Incremental/IncrementalSolver.cpp:5501-5526` (promotion),
`:5484-5488` (the skip), `:2046-2084` (`updateStackStability`), `:1602-1623`
(screening), `:1728-1755` (cache-hit revalidation), `:1634-1657` (the repair the
base level has and promotion does not).

### Mechanism

Promotion asserts a level's **prepared** conjuncts as permanent units:

```cpp
// :5477-5482 -- levelRoots comes from `conjuncts`, the PREPARED form
for (const ASTNode& c : conjuncts) { levelRoots.push_back(rootLit(c)); … }
…
// :5487-5488 -- and a promoted level is skipped ever after
if (level <= impl->promotedDepth) continue;
…
// :5508-5518 -- the prepared roots become permanent units
for (const int r : levelRoots) { … addClause(unit); }
impl->promotedDepth = level;
```

The only thing that can undo promotion is `updateStackStability`, which compares
the level's **raw** conjunction node against `lastStackSeen` (`:2049-2057`).

A promoted level's prepared form can legitimately change while its raw node is
byte-identical. `preparePiece` deletes a level-private defining equation
(`:1862-1872`); later content mentioning that variable makes it non-private, so
`screenNewContent → dropPreparedLevel` (`:1614-1623`) invalidates the entry and
the cache-hit revalidation (`:1738-1754`) refuses it. The level is re-prepared
**with the equation restored** --- and that re-prepared form is encoded via
`rootLit` and then dropped on the floor by the `continue` at `:5487`. No unit is
added, no assumption is pushed, no rebuild is triggered. The older, weaker units
--- the ones with the definition eliminated --- stay permanently asserted, and
the variable is unconstrained in the SAT formula while a live deeper level
constrains it.

The base level has exactly the repair this path is missing:
`screenNewContent` restores a base elimination's originals as permanent units,
tracked in `restoredBaseRoots` (`:1634-1657`). The hazard was recognised for
level 0 and not inherited by promotion, which turns a *pushed* level into
base-like permanence.

### Witness

`repro3.smt2` (see [Appendix A](#appendix-a--witness-files)). `QF_BVFP`; the FP
conjunct retires trail reuse on solve 1, which is promotion's precondition; the
stable level carries `(= (bvnot p) (bvmul t (bvmul t t)))`, a BVNOT-headed
equation `recogniseDefinition` refuses and PE harvests; the `bvmul` nest keeps
CBP from re-deriving the lost fact.

```
(no flags at all)                            -> sat     [WRONG]
--no-incremental-promote-units               -> unsat   [correct]
--incremental-auto-engage-at 0   (batch)     -> unsat   [correct]
--check-sanity                               -> STP Error: the model does not satisfy an asserted formula
```

`promote7.smt2` is a second, independently constructed witness in pure `QF_BVFP`
that reproduces under `--incremental --disable-cbitp`; it isolates the *masking*
relationship described next.

### The architectural point, not just the bug

In four of my five construction attempts the wrong answer did **not** appear ---
because some *other* mechanism re-derived the lost constraint:

- the pushed-definition `ctx`, rebuilt from raw conjuncts every solve, substituted
  the eliminated variable away in the deeper level;
- the simplifying node factory normalised `(= (bvadd p #x01) #x05)` into
  `(= p #x04)` at construction, making it raw-recognisable after all;
- constant-bit propagation, which holds **all** raw levels including the promoted
  one, re-derived the fixing and folded the deeper level to `FALSE`;
- on array levels, the refinement loop's model check evaluates the candidate
  against the **raw** active conjunction and rejects it.

Promotion's soundness is therefore not established by promotion's own logic. It
is established, incidentally and partially, by four redundant re-derivations.
That is the finding, and it is worse than the bug: **any change that makes one of
those mechanisms less eager --- retiring CBP, tightening the node factory,
skipping a `ctx` harvest --- can silently expose a wrong answer somewhere else.**

### Fix (pick one; (a) is smallest)

- **(a)** Store the promoted conjunct set per promoted level; before the
  `continue` at `:5487`, compare the freshly prepared `conjuncts` against it and
  demote + `rebuildEncodings` on any difference.
- **(b)** Refuse promotion for any level whose prepared piece carries
  eliminations --- the only known source of prepared-form drift under a stable
  raw conjunction.
- **(c)** Hook `dropPreparedLevel` so that dropping a piece belonging to a level
  ≤ `promotedDepth` forces `rebuildEncodings`, mirroring what
  `updateStackStability` already does for a raw change.

### Verification recipe

1. `repro3.smt2` with no flags must answer `unsat`.
2. `promote7.smt2` under `--incremental --disable-cbitp` must answer `unsat`.
3. Both under `--check-sanity` must not error.
4. `tests/query-files/incremental-tests/unit-promotion.smt2` must still report
   `promoted level 1 (1 conjuncts) to units after 8 stable solves` --- the fix
   must not disable promotion outright.
5. Add a regression covering *re-preparation of a promoted level*; the existing
   test covers only firing, binding, and demotion-on-retraction.

---

## D3 — ARCHITECTURE: whole-base re-simplification is welded to `rebuildEncodings`

**Severity:** high. **Class:** architecture (cost + coupling; no soundness
consequence found). **Evidence:** agent-reported, adversarially verified,
measured by the agent at 9.4 s.
**Sites:** `IncrementalSolver.cpp:3415` (the call), `:3514-3651`
(`resimplifyBaseAtRebuild`), `:3340-3352` (`RebuildReason`), `:4738`, `:4806`.

`rebuildEncodings()` unconditionally calls `resimplifyBaseAtRebuild()`, and it is
called for **all four** `RebuildReason` values --- including `Inprobing` (`:4738`)
and `Trail` (`:4806`), which are pure SAT-backend *configuration latches* with no
semantic content whatsoever.

The pass runs `PropagateEqualities` + `applySubstitutionMap` +
`ConstantBitPropagation::topLevelBothWays` + `SimplifyFormula_TopLevel` +
`RemoveUnconstrained` over the **entire base conjunction** with no size test, no
trial/reject gate, no memo, and no off-switch --- and re-derives the
model-visible `baseEliminatedDefs` from scratch on every fire. Every neighbouring
use of these same passes in the same file *is* budgeted (`:1796-1817` trial cost
bound, `:5107` adopter gate, `bigFormulaCap` at `:838`/`:5210`,
`incremental_cbp_bootstrap_limit`).

Measured (agent): a 23,294-conjunct array-free base with 12 tiny FP rounds costs
**9.4 s** inside a single trail-retirement rebuild --- a rebuild whose entire
purpose was to set one CaDiCaL option.

**Fix:** make the base pass a first-class, budgeted, content-keyed step rather
than a side effect of epoch replacement. Key it on the base conjunction so a
second rebuild over an unchanged base is a no-op; give it the same
trial/halving gate every other use of these passes has; invoke it only from the
`Relief` path (and the first forced solve). `Inprobing`/`Trail`/`Promotion`
rebuilds need a fresh backend, not a fresh formula.

**Related (D3b, `PARTLY/low`):** `baseEliminatedDefs` is cleared only on
`resimplifyBaseAtRebuild`'s full path (`:3545`), not in `rebuildEncodings` beside
`restoredBaseRoots.clear()` (`:3413`). On the two early-return paths (arrays in
the base; an `ExtensionalityContext` that was ever created --- the test is
`!= NULL`, not `active()`), a stale map survives into the new epoch and
`screenNewContent` can re-assert the same witness originals a second time,
double-counting `baseLiveMass` and `permanentUnitMass`. Bookkeeping only, but the
one-line fix is: clear `baseEliminatedDefs` in `rebuildEncodings` next to
`restoredBaseRoots`, and route the `pendingRebuiltBase` flush through
`restoredBaseRoots` too.

---

## D4 — COST: the privacy predicate makes a no-op check quadratic in stack depth

**Status: substantially FIXED** by the occurrence index (work-queue item 4)
and the elimination/inline transaction that followed it (D13's fix). Measured
on a deepening stack whose every level contributes a private elimination,
session total at depth 400: **3.13 s pre-fix → 1.14 s with the index → 0.77 s
after the transaction**, roughly 4x overall, with the growth rate falling from
about 10x per doubling (cubic) to about 4x (quadratic). What remains is the
per-check context rebuild, linear in the live stack and unaddressed.

⚠ *An earlier revision of this document recorded 0.48 s for the index step.
That was a single run taken under different load and it flattered the state
before the transaction; the 1.14 s figure above is the median of three runs
taken back to back against 0.77 s on a quiet machine. None of these are
interleaved quiet-box A/B, so treat them as indicative — the ordering is
solid, the exact values are not.*

**Severity:** was high --- this is the cost the engagement-at-32 policy is
compensating for. **Evidence:** measured by me; stronger figures
agent-reported.
**Sites:** `IncrementalSolver.cpp:1700-1706` (`levelPrivate`'s scan),
`:1738-1747` (revalidation on cache **hit**), `:5219-5222` (`conjunctCountOf`),
`:5150-5177` (context rebuild), `:1551-1574` (`symbolsOfCache`).

On a check where **nothing changed**, the driver still:

- rebuilds the pushed-definition context from scratch (fresh per-call `ctx`,
  `:5140`) by re-running `splitConjuncts` + `harvestPushed` over every level;
- rebuilds `conjunctCountOf` per level at Θ(total stack symbols) --- and at
  whole-level granularity (any level under `bigFormulaCap`) every count is 1, so
  its only consumer (`cnt->second > 1`) can never fire. Pure waste in the common
  branch;
- re-proves `levelPrivate` for **every eliminated variable of every cached
  piece** (`:1738-1747`), and `levelPrivate` scans **every live level**
  (`:1700-1706`) --- with the same `symbolsOf(stack[j])` call written twice.

Total: Θ(depth × eliminations-per-level × depth) per check, on the *cache-hit*
path.

**My measurements** (`--incremental-profile`, `build/`, agent-generated
deepening-stack files `w1_{100,200,400}.smt2`):

| depth | checks | total | semantic reconstruction | per-check semantic |
|---|---|---|---|---|
| 100 | 100 | 3.36 s | 0.94 s | 9.4 ms |
| 200 | 200 | 6.44 s | 2.65 s | 13.2 ms |
| 400 | 400 | 20.75 s | 8.17 s | 20.4 ms |

Per-check semantic cost grows with depth, so the session total is superlinear.
On a *toy* 3-level, 9-node stack (`tests/query-files/incremental-tests/incremental-profile.smt2`,
6 checks) the split is `semantic-us=1758` (46 %) against `sat-us=210` (5.5 %) ---
i.e. even at the smallest scale, reconstruction dominates solving.

**Agent-reported, not re-run by me:** on a 400-level session whose levels each
adopt one private elimination, `prepare-us` is 79 % of the session (2.35 s of
2.99 s) against 5.7 ms of SAT time, with `perf` attributing 60.5 % of process
time to `Impl::symbolsOf` and 20.3 % to `Impl::preparePiece`; per-hit cost grows
linearly with depth (8.3 µs at 100 levels, 29.5 µs at 400). With zero
eliminations `prepare-us` is flat below 100 µs at all depths.

**Fix.** Three bounded changes, none of which needs the assertion journal:

1. Maintain a **symbol → set-of-live-levels** index (or per-symbol level bitset)
   as levels are screened, so `levelPrivate` is O(1). This is the same
   longest-common-prefix comparison the CBP fed-prefix and promotion already
   perform. *This is also the index D1's fix wants and the record D2's fix wants
   --- one structure closes all three.*
2. Skip building `conjunctCountOf` entirely when `rawConjuncts.size() == 1`.
3. Memoise the harvested-definition set per level-conjunction node, so
   `harvestPushed` is paid once per distinct level rather than once per check per
   level. Remember the previous check's base conjunction node and skip the
   base split when unchanged (the same pointer-equality trick
   `updateStackStability` already uses).

Then **re-measure the engagement ordinal.** A cost-model-driven threshold is the
principled version of the 32.

**Caveat for whoever fixes this:** the rescan is a deliberate soundness repair
(`ee8685bb`) for a stale privacy proof after pop/re-push. A fix must *preserve*
that guarantee, not drop the check.

**Related (low):** `symbolsOfCache` (`:658-659`) is unbounded and never cleared,
not even at `rebuildEncodings`. Memory only --- symbol sets are a pure function
of the node, so entries can never be stale --- measured by the agent at ~12 % of
peak heap in the shape that maximises it.

---

## D5 — ARCHITECTURE: the exact-stack block cache is fronted by a non-deterministic pass

**Severity:** medium. **Evidence:** agent-measured, adversarially verified.
**Sites:** `IncrementalSolver.cpp:3709` (`RemoveUnconstrained` in the block
pass), `:4179` (the cached accept/reject bool), `:4262` (the `rootLitOf` block
lookup), `RemoveUnconstrained.cpp:133`, `STPManager.h:571`
(`CreateFreshVariable`).

`docs/incremental-solving.rst:341-344` promises that "repeating or re-pushing a
stack recreates the same transformed root and reuses its encoding and lemmas".
The block cache (`rootLitOf` hit at `:4262`) is the *only* reuse above the
bit-blast memo on this path --- and `preprocessExactStackBlock` is **not** a
deterministic function of its input node, because `RemoveUnconstrained` names its
stand-in variables from `STPMgr::_symbol_count`, a mutable counter.

Whenever a stand-in survives into the output --- which needs the replaced parent
term to have ≥2 uses, a common symbolic-execution shape --- an identical
re-pushed `--array-equality` stack lowers to a *fresh node*, misses `rootLitOf`,
and gets a complete fresh AIG cone, CNF variables, and clause copy.

Measured (agent): +24 SAT variables per identical repeat on a small stack;
**4,177 → 56,299 variables over 15 identical repeats** on a 40-read stack; flat
with unconstrained elimination disabled.

Separately, only the accept/reject *bool* is cached (`:4179-4184`), so the whole
CBP + equality-propagation + unconstrained + pure-literal pass re-runs on every
check even when it hits.

**Fix:** memoise the pass by input node, storing `(output, eliminated
definitions)` together --- that restores determinism *and* makes a repeated stack
O(1) above the transform. Alternatively (or additionally) give
`RemoveUnconstrained`'s stand-ins deterministic names via the branch's own
`CreateDeterministicVariable`.

---

## D6 — MEASUREMENT: `--incremental-profile` changes the relief schedule it measures

**Severity:** medium. **Evidence:** code-verified by me; demonstrated at the
shipped default configuration by an agent.
**Sites:** `IncrementalSolver.cpp:2536-2569` (`stageLiveConeMass`), `:2556` (the
`!profile.enabled` guard), `:4693-4706` (the relief decision), `:5565-5566`.

`stageLiveConeMass` feeds **two different quantities** into
`recordLiveClauseMass → maxLiveClauseMass` depending on `profile.enabled`: an
exact de-duplicated AIG-cone walk when profiling, the per-key `clauseMassOf`
lower bound otherwise. The compensating lazy repair
(`expandPendingLiveConeMass`) is *disabled* under profiling by the
`!profile.enabled` guard at `:2556`, so `hasPendingLiveCone` is never set and the
lazy path is never exercised.

Since exact ≥ cheap, and the non-profiled path repairs only the last solve's
snapshot, **the profiled peak is always ≥ the unprofiled peak** --- so
`--incremental-profile` can suppress or delay relief rebuilds, never advance
them.

This matters twice over. The measurement apparatus perturbs the thing it
measures, in the direction that hides rebuild events; and 17 of the branch's 87
lit RUN lines assert counters produced under the profiled regime, so those
expectations describe a configuration production never runs.

*(Two small relief-valve cases I tried did not diverge between the two regimes;
the divergence is established from the code paths, not from a demonstrated
answer difference on those files. The agent demonstrated it on a synthetic
variant-push corpus at default `incremental_reencode_limit`.)*

**Fix:** compute **one** live value for the decision on both paths --- the exact
walk when a snapshot exists, the lower bound otherwise --- and let profiling only
add *reporting*. If the exact walk is affordable every solve, it is the right
production estimator and the cheap-estimate-plus-lazy-repair pair
(`clauseMassOf` staging, `PendingLiveCone`, `expandPendingLiveConeMass`) can be
deleted outright: roughly 80 lines and 4 fields. If it is not affordable, the
profiler must report the estimate the driver actually used and expose the exact
walk as a separate column.

---

## D7 — POLICY: `cbpEverFixed` does not measure what its retirement tier needs

**Severity:** medium. **Evidence:** agent-reproduced on two structurally
identical 120-query sessions.
**Sites:** `IncrementalCBP.cpp:458-468`, `IncrementalSolver.cpp:1360-1377`,
`:955-973` (the two-tier comment), `:4943-4956` (the leash).

The retirement policy has two tiers: a session whose engine has **never derived
a fixing** retires after 8 barren divergences; one with fixings but no adoption
gets 64. But `feedLevel` records the level's own **assumed truth** as a fixing,
and the harvest's interior-node loop sets `cbpEverFixed = true` off it --- so in
any session whose first fed level is array-free, the flag is true after the first
feed, before the engine has derived anything at all.

The 8-divergence tier is therefore **unreachable** for exactly the sessions it
was designed for. Reproduced: two structurally identical 120-query pop-per-query
sessions, one array-free and one with a `select` in every level, retire at 64 and
8 divergences respectively --- the opposite of the intent.

**Fix:** set `cbpEverFixed` only from fixings that are not the fed level's own
assumed truth --- i.e. only in the SYMBOL loop (`:1358`) and, in the interior
loop, only for nodes not in `callCbpFedConjuncts`. Better: drive the leash off
evidence that a fixing *crossed a level boundary* (survived `cbpFinishLevel` and
later matched in a deeper level's `cbpAdopt` walk), which is the property the
pass exists for, and let one leash serve both tiers.

**Related (D7b, `PARTLY/low`) --- the feed cap double-counts.** `cbpFeedCap` is
charged as the *sum* of per-level DAG sizes (`callCbpFed += dagSizeUpToMemo(...)`,
`:1249-1266`) while the engine retains their *union* (`extendParentMap` dedupes
via `depsVisited`). A live stack of ~25 levels over a single 8k-node define-fun
spine therefore trips the 200k cap even though retained content is ~8k nodes
(agent-reproduced), and because `cbpSessionRetired` sits deliberately outside the
undo trail, the pass stays off after the stack shrinks. Fix: charge the union
(the engine can report `depsVisited.size()`), and let a rollback below the
tripping level re-arm the pass --- the rollback already restores `callCbpFed`
correctly.

---

## D8 — COST: every array encode installs and copies back the whole session registry

**Severity:** medium. **Evidence:** agent-verified empirically (anchors == rows
on all 400 encodes of a 400-query session).
**Sites:** `IncrementalSolver.cpp:2884`, `:2891`, `:2897-2933`,
`ArrayTransformer.cpp:79-136`.

`encodePrepared` installs the entire persistent registry into `batchAT` **by
value** and copies it back (`:2884-2892`). `TransformFormula_TopLevel`'s
post-loop (`ArrayTransformer.cpp:84-133`) uses a call-local `replaced` map with
no check on an already-set `index_symbol`, so it re-conjoins an index-binding
equation for **every registry row with a computed index** onto **every array
conjunct it transforms** --- including rows from other levels and popped levels,
since `myReads` is never pruned.

The comment at `:2897-2908` asserts the opposite invariant and is false; the
repair loop at `:2909-2933` is today a strict, redundant subset (identical node
factory, operands, and skip condition).

**Fix:** give the driver a registry it owns and hand it to the transformer by
pointer/reference instead of by value; make anchor emission **per transform run**
rather than per table --- emit `EQ(index, index_symbol)` only for rows in
`touchedReads`, which the driver already collects. That deletes both the
whole-table loop in `ArrayTransformer` and the compensating loop at `:2909-2933`,
restores per-conjunct locality of the encoding, and makes `clauseMassOf` mean
what the relief valve assumes it means.

**Related (D8b, low):** congruence lemmas are permanent and unconditional, but
`refinementMassOf` charges them to a content-addressed **whole-stack** owner key
(`AND(assertionsSMT2)`). On a growing stack a later check's live mass omits the
axioms earlier checks emitted while `retainedClauseMass()` still counts them,
biasing the relief ratio toward firing. The natural owner is the registry row
pair (or the active read-row set) --- a lemma is live while both its rows are in
the active seeded table.

---

## D9 — CONTRACT: `construct_counterexample_flag` was made sticky

**Severity:** low (no wrong answers). **Evidence:** agent-reproduced on a Release
build and isolated by rebuilding with the master behaviour.
**Sites:** `STP.cpp:448-457` (the deleted `else … = false`),
`IncrementalSolver.cpp:4337` (set unconditionally on array-equality rounds, never
restored --- unlike `savedAck` at `:4126`/`:4388`), `:4016-4022`, `:5641-5647`,
`cpp_interface.cpp:706-708`.

Removing `else construct_counterexample_flag = false` from `TopLevelSTPAux` and
having both incremental drivers OR the flag into their own derivation makes the
flag **monotone for the life of the session**. Because the frontend reads that
same flag as its "a model was demanded" predicate, one array round whose array
ops survive Ackermannisation --- or one `(set-option :produce-models true)` ---
**permanently disables the verdict cache's unchanged-stack shortcut** documented
at `docs/incremental-solving.rst:38-42`, and permanently re-enables per-solve
counterexample construction in the *batch* pipeline too.

**Fix:** give the driver a private `needsCandidateModel` derived per check from
`needRefinement`/extensionality, instead of latching the shared user flag;
restore `construct_counterexample_flag` to being recomputed per check from its
genuine inputs (`check_counterexample_flag`, `print_counterexample_flag`,
`produce_models`, and the C API's `'c'` request held in its own field). The
frontend's cache predicate should read the *request*, not the derived flag.

---

## D10 — LAYERING: a node-construction rewrite is gated on a mutable session mode flag

**Severity:** low (performance/predictability, no soundness consequence found).
**Evidence:** code-verified by me; measured by an agent.
**Sites:** `SimplifyingNodeFactory.cpp:946-951`, `cpp_interface.cpp:610`
(`push()` sets the flag), `c_interface.cpp:892`, `UserDefinedFlags.h:92`.

```cpp
if (kind == stp::FP_SMT_EQ)
  result = bm.UserFlags.incremental_solving
             ? hashing.CreateNode(kind, children)   // keep x = x
             : bm.ASTTrue;                          // fold it
```

A semantics-preserving reflexive rewrite in the **generic** simplifying node
factory is gated on a driver-lifecycle flag that `push()` sets mid-session and
never clears. Three consequences:

1. The branch's own design doc still asserts the opposite invariant ---
   `docs/incremental-solving.rst:114-115`, *"Node-construction rewrites (the
   simplifying node factory) … are context-free and always on"* --- and was
   edited two days after this change without carving out the exception.
2. The gate's reach is wider than "incremental mode": `push()` sets the flag even
   when the driver never engages, so a QF_BV session that stays on the batch
   pipeline until solve 32 still gets a different word-level DAG. Agent-measured:
   adding a bare `(push 1)` to a one-check QF_FP file changes a formula that
   otherwise folds away entirely.
3. It weakens the branch's own primary oracle. Batch-vs-incremental differential
   testing now compares two engines that were handed **different node graphs**.

The stated justification is a >3× CaDiCaL swing on the Newton family --- i.e. a
search-luck effect, deliberately embedded in a shared rewrite rule.

**Fix:** keep the rewrite unconditional. If encoding order genuinely matters,
express it where order is chosen --- the bit-blaster/CNF conversion, or a
driver-owned lowering step --- not in a node-construction rule keyed on a mutable
global.

**Related (D10b, low, reproduced by agent):** because `push()` sets
`UserFlags.incremental_solving` permanently and `reset()` re-runs `init()`, which
re-derives `incremental_from_start` from that flag, **any SMT-LIB session that
issues `(push)` and later `(reset)` runs its entire post-reset session through the
driver as though `--incremental` had been passed**, with
`firstForcedIncrementalSolve` set on its first solve --- contradicting
`IncrementalSolver.h:88-96`. No wrong answers; the cost is losing the batch
pipeline's whole-formula simplification on the first post-reset query. Fix: keep
`UserFlags.incremental_solving` as the immutable user *request* and hold "this
session became incremental" in `Cpp_interface`, as the C API already does with
`STP::incrementalFromStart`.

---

## D11 — DEAD: `Backtrack.h`, `canHandle`, `batchTablesSeeded`

**Severity:** low. **Evidence:** verified by me (grep across the whole tree) and
by agents.

> **Disposition (done).** `Backtrack.h` and its test are deleted --- 383 lines,
> no behaviour change, recoverable from history. The occurrence index added in
> `00ea5c1e` is per-call rather than per-level, so it was not the consumer this
> header was waiting for; if the assertion-journal work reintroduces it, it
> should arrive with its first real consumer rather than ahead of one.
> `batchTablesSeeded` is gone with its stale comment. `canHandle` is kept as
> the documented seam, with its false "verdicts are cached" claim corrected,
> and the three `Cpp_interface` model readers now ask `hasIncrementalSolver()`
> so a batch session no longer builds a driver and a SAT backend as a side
> effect of asking whether one exists. `CbpCallerCheckpoint::offBefore` and
> `conflictBefore` are **kept**: `feedLevel` latches both, so an undo of that
> feed owes their restoration, and a trail that covers only the state whose
> restoration is currently load-bearing is a trap for the next caller. The
> comment now says so.

- **`include/stp/Incremental/Backtrack.h`** --- 273 lines: `BacktrackManager`,
  `Backtrackable`, and backtrackable `vector`/`unordered_map`/`unordered_set`,
  modelled on Bitwuzla's `src/backtrack/`. Complete, correct, unit-tested
  (`tests/unit-tests/Backtrack_Test.cpp`, 5 tests) --- and **used by no
  translation unit outside that test**. No file names `stp::backtrack`; it is not
  an installed public header. Its comment describes stores the driver never grew
  (there is no "first-seen" rule or symbol-level record anywhere in
  `lib/Incremental`).

  This is the branch's clearest statement about itself: the design was started
  one way (scoped containers) and finished another (snapshot reconstruction), and
  both philosophies shipped.

  **Two acceptable dispositions, not one.** (a) Delete it, its test, and the
  CMake entry --- 383 lines, zero behaviour change --- and accept the two local
  trails as the design. (b) Land the first real consumer with it: the natural one
  is exactly the symbol→levels index D4 asks for and the promoted-conjunct record
  D2 asks for, both insert-only per level, which is the discipline this header
  already implements.

- **`IncrementalSolver::canHandle`** (`:4502-4510`) is unconditionally
  `return true`. The `.cpp` comment describes it honestly as a future seam, but
  the header comment at `IncrementalSolver.h:75` --- *"Verdicts are cached per
  assertion node"* --- is stale (left from `eb793409`, when it really did call
  `impl->supported()` per level). Because it never returns false, the batch
  fallback at `c_interface.cpp:834-836` is dead too. Additionally,
  `Cpp_interface::getValue` (`:994-995`), `getUnsatAssumptions` (`:1068`) and
  `getModel` (`:1111-1112`) call `GlobalSTP->getIncrementalSolver()`, which
  **constructs on null** --- so their `!= NULL` guards can never be false, and a
  plain batch session that prints a model allocates a whole driver (including a
  CaDiCaL instance) as a side effect of asking whether one exists. Change those
  three to `hasIncrementalSolver()`, matching the C API.

- **`batchTablesSeeded`** (`:3094`) is write-only: initialised at `:2127`,
  assigned at `:2900`, `:3212`, `:3392`, `:4250`, **read nowhere**. Its 12-line
  comment still documents a key-fingerprint skip-if-unchanged policy that
  `seedActiveReads` explicitly declines to implement (`:3168-3174`). Git history
  pins it: `8ce5ecc5` added the flag with its one read; `1e1d5969` replaced that
  fast path and removed the read but not the flag or its comment.

- **`CbpCallerCheckpoint::offBefore` / `conflictBefore`** (`:1044-1046`) are a
  dead store/restore pair --- `cbpRollbackCallerTo` has one call site and both
  fields are unconditionally reassigned a few lines later with no intervening
  read. Correct if a rollback ever ran mid-call; today unobservable.

---

## D12 — COST: the `ToSATBase` adapter rebuilds an O(all session symbols) map per call

**Severity:** low. **Evidence:** agent-measured at ~1.8 ms per call for a
3000-symbol/96k-bit memo.
**Sites:** `IncrementalSolver.cpp:3993-3998`, `:3894-3930` (`buildSymbolMap`),
`CounterExample.cpp:2121`, `AbstractionRefinement.cpp:433`,
`ExtensionalityContext.cpp:1670`.

`IncrementalToSAT::SATVar_to_SymbolIndexMap()` clears and re-runs
`buildSymbolMap` on **every call**, walking the entire never-pruned
`bbMgr.symbolToBBNode` (all symbols ever blasted, popped ones included) and
allocating a `vector<unsigned>` per symbol before it can discover the symbol
contributes nothing. The batch adapter returns a stored map by reference.

It is called twice per ordinary refinement round and **once per pending lemma**
on the array-equality path, so the cost is Θ((rounds + lemmas) × all-session
symbol-bits).

**Status: CLOSED, optimisation declined.** Two candidate fixes were built and
measured against interleaved baselines:

- caching the built map behind a dirty flag invalidated at `setVarOfAig`,
  `recordActiveElimination` and the per-solve reset --- **neutral** (3.66-3.75 s
  against 3.74-3.84 s on a 300-query refinement session, identical refinement
  rounds and answers);
- passing it by `const&` instead of by value --- **neutral** on the same session
  (3.80-3.88 s) and on a 2,500-symbol session built specifically to make the
  symbol set dominate (20.0 s against 19.9 s).

The per-call cost is real, but the call count is not: `SATVar_to_SymbolIndexMap`
is reached twice per refinement round, and in every session I could construct
the SAT search and `totalizeSymbol` dominate it (CaDiCaL propagation 21%,
`totalizeSymbol` 16%, the map nowhere in the profile). Caching it would add an
invalidation surface across three sites --- the shape that produced D1 --- for
no measured return, so it was not shipped.

What *was* shipped is the contract, not the optimisation: `ConstructCounterExample`
only ever iterates the map, so it now takes `const&` and the call site no longer
copies it. That is correct by inspection and costs nothing; it is not claimed as
a speedup.

⚠ **Measurement note.** An earlier reading made the cache look 1.45x *slower*.
It was compared against a baseline taken minutes earlier on a quieter machine.
Interleaving the two builds showed them identical. Do not compare timings on
this branch across anything but back-to-back runs.

---

## D13 — CONSERVATISM: D1's fix refuses eliminations the context re-join would have covered

**Severity:** low, and **measured**. Introduced deliberately by `e1229764`; not
a defect, a known over-approximation with a known clean fix.
**Sites:** `IncrementalSolver.cpp` `collectCtxExportedSymbols`, `levelPrivate`,
and the `ctx` re-join in `checkSatOnCurrentStack`.

D1's fix refuses to eliminate any symbol a live `ctx` body can export to a
deeper level. But eliminating such a symbol is sound *when the re-join
succeeds*, because the deeper level then has that symbol substituted away too.
The predicate does not ask whether the re-join would have covered it, so it
refuses some eliminations that were legitimate.

### What it costs, measured

Over all 73 files of `tests/query-files/incremental-tests/`, comparing the
pre-fix binary against the fixed one (`-s --incremental`, summing the
`N eliminated` line across every solve):

```
eliminations, pre-fix : 93
eliminations, current : 89
```

Three files differ, and two are D1's own witnesses (`6 -> 5` each) where the
lost elimination **is** the unsound one --- the fix working, not a cost. The
entire genuine cost in the corpus is one file:

```
level-elimination.smt2   4 -> 2      (per check: 2 0 0 0 0, was 2 1 1 0 0)
```

Check 1 is untouched. The losses are checks 2 and 3, where a deeper level names
`x` and `ctx[x] = (bvadd a #x01)` exports `a`.

The shape needed to trigger it: a level defines `x := f(a)`, a deeper level
names `x`, and `a` is otherwise private. Rare in this corpus --- but the corpus
is small, so if a real workload shows preparation eliminating noticeably less
than before, this is the first thing to check.

### The fix, and the fix NOT to make

**Do not** have `levelPrivate` predict whether the re-join will succeed by
replicating its three decline conditions. That is precisely how D1 arose: one
invariant maintained by agreement between two sites, which drifted. A fourth
decline condition added to the re-join and not to the predicate reintroduces
the wrong answer.

Make elimination and context-inlining a **single transaction** instead.
`preparePiece` should record an elimination only if the caller will inline it;
the caller's three declines then become guaranteed rather than silent. One
decision, evaluated once, consumed twice, with no possibility of divergence.

That has a strong consequence: if *every* eliminated variable is guaranteed to
have a `ctx` entry, then no eliminated variable can reach the encoder through a
context body at all --- and `collectCtxExportedSymbols` can be **deleted
outright**, along with its per-entry lookup. The endpoint is strictly better
than both the current state and the pre-fix state: it recovers the
eliminations, removes code, and removes a query.

⚠ It would make soundness newly depend on `SubstitutionMap::replace` expanding
context entries through each other transitively (`x -> f(a)` with `a -> 0`
collapsing in one pass). That behaviour is real and documented in the `sigma0`
comment, but it must be *verified* rather than assumed before this lands.

This is the same work as [Part V](#part-v--work-queue) item "give the
elimination invariant one owner", whose "delete the `ctx` re-join" clause this
supersedes with a concrete mechanism.

---

## D14 — SOUNDNESS: the relief rebuild keeps a definition whose dependency it just dropped

**Status: FIXED, `87a77ac2`.** Class: soundness (`sat` on an `unsat` query).
Flags: none on the path itself; the session must take a relief rebuild.
In master: no --- `resimplifyBaseAtRebuild` is branch-only code.
Pre-existing on this branch: **yes**, reproduced identically at `933a3b4b`.

Sites: `lib/Incremental/IncrementalSolver.cpp:3833` (`resimplifyBaseAtRebuild`),
`:3898` (`untouch` construction), `:3976` (`RemoveUnconstrained`), `:3993` (the
keep-vs-eliminate filter). The fix is the closure at `:3941`.

### Mechanism

The relief rebuild re-derives the whole base semantically before re-encoding
it. Two things happen in that pass that are individually correct and jointly
are not.

1. `PropagateEqualities` harvests `u -> (bvadd v #x01)` from a base equation
   and **deletes the equation from the formula**. The definition now lives only
   in the substitution map.
2. `untouch` (`:3898-3902`) is the symbols of every live pushed level. A level
   constrains its symbols from outside the base, so the base pass must not
   eliminate them. With `u` on a live pushed level, `u` is untouchable and `v`
   --- mentioned nowhere but the base --- is not.
3. `RemoveUnconstrained` runs (`:3976`) and decides unconstrainedness **from
   the formula alone**. By this point `v`'s only surviving occurrence is inside
   the map *value* `(bvadd v #x01)`, which it cannot see. It drops
   `(bvult v #x02)` --- `v`'s last constraint --- and records a witness for `v`.
4. The filter at `:3993` keeps `(= u (bvadd v #x01))` as an asserted conjunct,
   because `u` is untouchable.

What re-encodes is therefore a definition of `u` in terms of a variable nothing
constrains. **The rebuilt base is strictly weaker than the raw base it
replaced.** `u` is free.

Nothing restores it. The restore path covers content screened *after* the
rebuild; this level was already live, which is precisely why the rebuild had to
treat `u` as untouchable in the first place.

### Witness

`tests/query-files/incremental-tests/relief-kept-definition-dependency.smt2`.
Base `u = v + 1` and `v < 2`, so `u` is 1 or 2 and `(= u #xff)` is **unsat**.
Ten dead push/check/pop rounds, then that query.

| | answer |
|---|---|
| branch, `--incremental` | **`sat`** |
| branch, batch pipeline | `unsat` |
| branch, `--incremental-base-resimplify-limit 0` (pass off) | `unsat` |
| Bitwuzla, cvc5, Z3 | `unsat` |

`--check-sanity` rejects the model outright ("the model does not satisfy an
asserted formula"), so a campaign validating models would have caught it.

Ten rounds is not arbitrary and the reduction is fragile: the valve must fire
**on the final check**, when the `u` level is the live one. At nine rounds and
at eleven it fires elsewhere and the answer is correct. Three earlier
reductions --- screening order, query novelty, a single query after the
rebuild --- all failed to reproduce, because in each of them the rebuild landed
on a throwaway level and the ordinary restore path handled it correctly.

### Why neither the sweep nor 23,000 files of fuzzing found it

The alignment is narrow: a base definition whose dependency appears nowhere
else, a pushed level naming the *defined* variable but not the dependency, and
a relief rebuild landing on exactly that check. Relief needs
`nVars >= --incremental-reencode-limit`, default **1,000,000** --- so a corpus
whose sessions never reach a million variables never enters this code at all,
no matter how many files it has. Of 82 suite files, 11 reach a rebuild, and
every one forces the limit to get there.

The sweep did examine this pass --- it is D3, filed as *architecture: cost and
coupling*, with "no soundness consequence found" written in its own write-up.

### Fix

Close `untouch` under the substitution map's right-hand sides, to a fixpoint,
before `RemoveUnconstrained` runs (`:3941-3974`). If `k` is untouchable and the
pass has harvested `k -> d`, then `k`'s value comes from `d` and every symbol of
`d` carries exactly the weight `k` did. The fixpoint is needed because a symbol
added that way can itself be a map key.

Restoring `(= v witness)` instead would be **wrong**: it over-pins `u`.
Substituting the witness into the kept definition would be wrong for the same
reason.

### Verification recipe

```sh
# reproduce (pre-fix), and check the four-engine agreement
build/stp --incremental --incremental-reencode-limit 1 \
    tests/query-files/incremental-tests/relief-kept-definition-dependency.smt2
build/stp  tests/query-files/incremental-tests/relief-kept-definition-dependency.smt2   # batch: unsat
# isolate the pass without touching the source
build/stp --incremental --incremental-reencode-limit 1 \
    --incremental-base-resimplify-limit 0  <witness>    # unsat: the pass is the cause
```

### What this says about the rest of the branch

It was found by adversarially challenging **F43**, a Tier 4.6 tidiness row
about four duplicated preprocessing prefixes. The challenge agreed the shared
helper that row proposes would be churn --- and then asked the question the
helper would have hidden: *does each of the four still enforce what its siblings
enforce?* `preparePiece` asserts (`:2103-2112`) that no variable it recorded as
eliminated occurs in any conjunct it keeps. This pass keeps conjuncts too, runs
`RemoveUnconstrained` afterwards, and had neither that assert nor an argument
for why it did not need one.

Porting that assert is therefore not tidiness; it is the check that would have
caught this. It is tracked in [Tier 4.6](#46-findings-the-sweep-recorded-and-never-queued).

---

# PART II — VERIFIED CORRECT (do not re-chase)

Each item below was actively attacked during this review and survived. The
argument is recorded so it can be re-checked cheaply rather than re-derived.

### Retraction and level identity

- **Base-as-permanent-units is justified.** The frontend guarantees the one
  invariant it needs: level 0 only grows, and `reset`/`reset-assertions` destroy
  the driver (`cpp_interface.cpp:491-495, 527, 571`). The C API, which guarantees
  nothing of the kind, correctly prepends a synthetic `TRUE` base and treats
  every real level as retractable (`c_interface.cpp:818-831`).
- **Activation literals are keyed correctly** --- on the sorted, deduped root
  vector, not the formula (`:3801-3832`) --- which is exactly right, since the
  same formula can encode to different roots under different pushed definitions.
  `actLitOf` is cleared on every rebuild (`:3383`), so no stale literal survives
  a re-mint.
- **Retirement by pinning is sound, for precisely the stated reason and no
  other.** An activation variable occurs *only* negatively (all its clauses are
  `¬a ∨ root`), so pinning `¬a` is a pure-literal fixing that preserves
  satisfiability; and the entry is erased from `actLitOf`, so a recurring root
  set mints a fresh variable rather than reusing a pinned one (`:3295-3330`).
  Extending eviction to encoding variables would violate their Tseitin clauses
  --- the boundary is correct.
- **Unsat-core attribution is conservative everywhere it must be.**
  `SATSolver::unsatAssumptions`'s default returns the whole assumption set
  (`SATSolver.h:198-204`); extensionality and provisional blocks set
  `lastUnsatCoarse` so every level is reported (`:4050`, `:4460-4470`); promoted
  levels are floored into every core (`:4474-4482`); the frontend only ever takes
  `core.back()` to truncate, so a coarser core is always safe.

### Frontend

- **The verdict cache's SMT reasoning is in the right layer and is sound.**
  `cache[deepest]` is only written for a level strictly beneath the top
  (`cpp_interface.cpp:751-760`). The obvious hole --- a refutation resting on a
  *promoted* level asserted unconditionally --- is explicitly closed by the core
  floor above. `check-sat-assuming` as an internal level is safe: its own cache
  entry is always fresh, so the only way it can be answered without a solve is
  push-inheritance, which means the stack *below* the assumptions is already
  unsat and any reported assumption subset is a correct core.
- **Model lifetime is modelled properly** by `model_valid` plus lazy
  `materializePendingModel()`, with SMT-LIB invalidation on assert/push/pop/reset
  and the C API's historical post-pop model contract preserved deliberately.
- **`bm->ValidFlag` is not stale on the incremental path.** I hypothesised that a
  C-API session could read `ASTUndefined` from `GetCounterExample` after an
  incremental `sat` following a batch `unsat`. **Refuted empirically:**
  `ToSATBase::PrintOutput` --- the only writer --- is called from
  `Cpp_interface::checkSat` for *both* engines, and the C API never sets it true
  at all. A compiled C-API probe (batch `sat`, batch `unsat`, incremental `sat`,
  then `vc_getCounterExample`) returned the correct value.

### SAT layer

- **The facade rework is clean.** Non-virtual `addClause` + virtual
  `addClauseInternal` means theory-refinement code that only holds a
  `SATSolver&` cannot bypass accounting; capability queries degrade to "hint
  declined, not an error"; `supportsAssumptions`/`solveWithAssumptionsInternal`
  defaults are mutually coherent, so the `exit(-1)` default is unreachable at
  runtime.
- **CaDiCaL's factor translation is complete.** *Every* path that names a
  variable goes through `ext_of_stp`: `addClauseInternal` (`Cadical.cpp:324-338`),
  `solveWithAssumptionsInternal` (`:91-114`), `unsatAssumptions` (`:269-285`),
  `suggestPhase` (`:287-299`), `modelValue` (`:340-348`). The assumption path
  correctly declares *before* naming rather than relying on `solveInternal`.
  I went looking for the missing one; there isn't one.
- **The configuration-window rule is respected at every live call site** ---
  constructor and `rebuildEncodings` configure a fresh solver;
  `resimplifyBaseAtRebuild` deliberately submits no clause; `decideBVA` (`:4814`)
  precedes the first `addClause` (`:5026`/`:5077`); `retireStaleActivation`'s pins
  (`:5043`) come after. It is respected *by call ordering only* --- see the
  suggested `configuration_closed` latch in [Part V](#part-v--work-queue) --- but
  it is respected.
- **Trail reuse has no soundness precondition to violate.** CaDiCaL sorts the
  assumption vector by trail position before comparing, so the mechanism depends
  on set overlap, not caller ordering. The `SATSolver.h:155-158` comment states a
  sufficient condition as if it were necessary; that is a wording imprecision,
  not a defect. Promotion and activation re-minting shrink the reusable set,
  which is exactly why both are gated on trail retirement.

### CBP

- **The engine's undo trail is complete.** Every piece of state `feedLevel`
  mutates is restored: `fixedMap` via `fixedUndo` + `fixedCreated` with the
  correct "created this level ⇒ delete, not restore" split
  (`IncrementalCBP.cpp:327-334, 151-171`); `msm` via
  `multiplicationCreated`/`multiplicationUndo` (`:105-122`); **the parent map and
  `depsVisited`** via `dependenciesAdded`, popped in reverse so duplicate child
  positions unwind exactly (`:127-149`); `conflict` via the per-checkpoint field
  (`:71-73, 173`); worklists, `newlyFixed`, and per-step scratch cleared
  (`:92-97`). Caller-side: `callCbpSubst`, `callCbpFedConjuncts`,
  `callCbpFactEmitted`, `callCbpFed`, `cbpFedArrays`, `callCbpOff`,
  `callCbpConflict`, `cbpFedLevels` all checkpointed or trailed (`:1066-1171`).
- **Prefix discipline is enforced by evaluation order, not by bookkeeping** ---
  feed level L → adopt L's conjuncts → `cbpFinishLevel` releases L's own fixings
  → feed L+1 (`:5187, :5345, :5472`). Deeper levels' facts therefore cannot reach
  a shallower conjunct *by construction*. This is the best structural decision in
  the newest machinery.
- **Conflicting feeds are recorded as fed levels** (`:1297-1319`), so popping a
  contradictory level removes its effect --- the fix for the one real CBP
  soundness bug in the branch's history.
- **The memo replay is sound.** The key includes the base conjunction, so it is
  trimmed by every event that can change `ctx` except elimination decisions; the
  surviving drift is neutralised by two explicit invariants (harvested definers
  always stay asserted; `levelPrivate` permanently refuses any bit-blasted
  symbol, and `bbMgr.symbolToBBNode` is never cleared, including across
  `rebuildEncodings`).

### Arrays and naming

- **Congruence-lemma permanence genuinely holds.** Abstraction variables and
  index anchors are deterministic functions of the `(array, index)` node pair;
  node uids are allocated monotonically and never recycled
  (`ASTInternal.h:191`, `node_uid_cntr += 2`); the registry itself holds the index
  nodes, so a re-minted node cannot collide with a live row's name. Even if a
  popped row leaked into the axiom set, the axiom is a Horn implication
  `idx_a = idx_b → val_a = val_b` over variables that are unconstrained once
  their root literal is unassumed --- every model of the live formula extends to
  it. Permanence is a conservative extension, not a convention.
- **Eager Ackermannisation with a persistent `myAckPairs` is sound**: the
  new-versus-existing ITE shape means any two reads are related by whichever was
  encoded later, and popped rows only ever offer an unconstrained alternative.
- **Naming by node number is sound.** `node_uid_cntr += 2` is strictly monotone
  and never recycles, so two live nodes can never collide onto one generated
  name; the worker thread hands the counter back (`:4585-4601`). What is coupled
  to GC is only the *reuse* property, and `exactStackKeepAlive` pins whole cones
  (an `ASTNode` holds its children), which is sufficient. **Weakness, not
  defect:** it is enforced by four manual inserts at one call site with no
  assertion and no test --- disabling all four leaves every incremental and
  extensionality RUN line byte-identical, so no test would notice if the pin
  stopped covering the right nodes. Consider moving the pin into
  `CreateDeterministicVariable` itself.

### Accounting

- **The exact AIG-cone walk is a sound estimator, not a heuristic.**
  `encodedAigConeMass` (`:2498-2530`) charges 3 per AND, 1 for the shared TRUE
  node, 0 for CIs, deduped by `Aig_ObjId` --- exactly what `ensureEncoded`
  (`:2616-2680`) emits --- and every node in a live cone is provably encoded in
  the current epoch because `aigRootOf` is cleared and repopulated per epoch.
- **Both sides of the relief ratio are submission counts in the same epoch**, so
  backend-internal simplification cancels rather than skewing the trigger.
- **The cheap per-key estimate is provably a lower bound** (a first-encode delta
  counts only nodes first encoded at that key, so summing over live keys counts
  each node at most once, and only nodes in some live cone). Its only failure
  mode is a *premature* rebuild, never a missed one; the lazy exact repair closes
  it. **Do not delete the cheap tier** --- an agent proposed exactly that, and
  the verifier showed it is what makes relief fire *less* eagerly: without it,
  recorded live mass collapses to hundreds of clauses against 10⁵--10⁶ retained
  and `reliefRatioReached()` becomes essentially unconditional past the variable
  floor.
- **Choosing whole-solver rebuild over cvc5's propagator pinning is right** given
  MiniSat/CMS/Riss have no propagator interface --- and the branch already
  applies the cvc5 trick exactly where it *is* portable and sound (activation
  literal false-pinning).
- **`SessionProfile::add()` is complete.** I diffed the field sets
  programmatically: 91 `CheckProfile` fields, 80 `SessionProfile` fields, 0
  omissions in `add()`. The 12 Check-only fields are per-check snapshots
  (`activeKeys`, `assumptions`, `levels`, `liveClauses`, `peakLiveClauses`,
  `retainedClauses`, `readRowsLive`, `stablePrefix`, `contextEntries`, `check`,
  `enabled`, `extensionality`), correctly non-additive. The duplication is
  verbose, not buggy.

### Explicitly refuted claims (do not resurrect)

| Claim | Why it fails |
|---|---|
| "Six ad-hoc invalidation mechanisms, no shared predicate" | There *is* one shared predicate: `levelPrivate`, applied with identical arguments both when an elimination is created (`:1862`) and on every cache hit (`:1738`). Two of the alleged mechanisms are contributors to one `protectedSymbols` argument; two others are re-armings of the screening memo. `ee8685bb` deliberately *replaced* `56de220c`'s ad-hoc partial invalidation with the general revalidation --- convergence, not divergence. |
| "Exact-stack scoped elimination lacks a freeze check" | The block encodes the complete active stack **including the base**, so each permanent unit is a conjunct of the block's own source formula: it can neither over- nor under-constrain the round. Hiding the eliminated symbols' bits in `buildSymbolMap` is *required*, not a bug --- `ConstructCounterExample` copies the model channel first and overwrites from SAT bits, so reporting stale bits is precisely what would produce a contradictory model. |
| "Two parallel live-mass estimators; delete the cheap one" | See above --- the cheap tier is the numerator's floor and deleting it makes relief nearly unconditional. Measured. |
| "Forced-first recovery is gated on CLI provenance" | `firstForcedIncrementalSolve` is `--incremental && session's first check-sat`, i.e. "no batch solve preceded this one" --- a session fact the driver genuinely cannot derive from `engagedSolves`/`cbpFedLevels`/`cbpMemo`. Two of the four sites are *skips*, so the auto path is not deprived. (A cleaner `engagedSolves == 0` predicate is still worth doing; see Part V.) |
| "`enableTrailReuse`'s correctness precondition does not exist" | Not a correctness contract at all --- a performance hint. See above. |
| "The CBP memo caches four subsystems behind a CBP-shaped key" | The key includes the base conjunction, and the two documented invariants neutralise the surviving drift. `--check-sanity` does validate models on this path. |

---

# PART III — ARCHITECTURE ASSESSMENT

## 1. What is right, and should not be replaced

The **retraction core**. One persistent SAT solver, one AIG, one bit-blast memo;
everything encoded is a conservative extension (fresh Tseitin variables and
definitional clauses), so it is valid in every context forever; base-level
conjuncts become permanent units; pushed levels are asserted through one
activation literal per level; a pop retracts by *not assuming*. Learned clauses
survive checks and pops by construction. This matches Bitwuzla's default
bit-vector engine closely and is responsible for the branch's measured wins.

Snapshot reconstruction --- the driver receives no `push`/`pop` notification and
rebuilds the active context from the assertion-stack snapshot each check --- is
also a **defensible** choice for STP specifically. It makes pop correctness free
and total: a popped assertion vanishes because it is not in the next snapshot.
The reference solvers all chose scoped containers instead, but they had
context-dependent infrastructure to build on and STP does not.

## 2. The root pattern behind both soundness defects

Both D1 and D2 are the *same shape*:

> **A predicate computed over one representation of the stack governs something
> computed over a different representation.**

- D1: `levelPrivate` decides over the **raw** stack; the encoder consumes the
  **ctx-substituted** stack.
- D2: `updateStackStability` validates the **raw** conjunction; promotion pinned
  the **prepared** conjuncts.

This is the price of snapshot reconstruction *as currently implemented*: because
no structure owns a level, every derived fact is re-derived ad hoc, and the
easiest thing to re-derive it from is the raw stack --- which is not what the
encoder sees.

Six mechanisms currently defend the one invariant "nothing eliminated may still
be reachable": the prefix discipline, `screenNewContent`'s memo, the cache-hit
revalidation, `eliminationUsers`/`dropPreparedLevel`, the `ctx` re-join, and the
CBP protected-symbol set. None *owns* it. D1 is what happens when the one route
none of them covers (a `ctx` body) is taken.

**This is the finding that matters most**, because it predicts future bugs of the
same class. The fix is not the full assertion-journal refactor: it is a single
maintained occurrence index consulted by one `eliminable(v)` predicate, plus a
level-owned record of what promotion pinned. Both are small, and both also fix
D4's quadratic cost.

## 3. The cost model contradicts the feature's purpose

Delaying `QF_BV`/`QF_ABV` --- the theories STP exists for --- to the **32nd**
solve is not a tuning constant. It is the measured price of per-check
reconstruction (D4). See [Part IV](#part-iv--cost-model-and-measurements).

## 4. Overreach inventory

**The forced-first-solve family.** Three pipelines exist so that `--incremental`
(a forcing/diagnostic flag) is not embarrassed on solve 1: base-only pure-literal
elimination (`:3426-3500`), the whole-stack "must at least halve" collapse trial
(`:4840-4866` → `exactStackCheckSat(requireScopedCollapse=true)`), and the CBP
bootstrap deferral (`:4896-4927`). The adversarial verifier correctly narrowed
this: all three are *entry conditions into machinery that already exists* and is
reachable without `--incremental`, the witness restore path is sound, and each
has regression coverage. What survives is the **regime count**: a single
`check-sat` now has ≥5 distinct routes (ordinary per-level; extensionality block;
provisional plain-BV block; base-only pure-literal; deferred-CBP), and **73 of the
branch's 87 lit RUN lines use `--incremental`** --- so the suite predominantly
tests the mode production never takes.

**The CBP subsystem.** ~700 lines of engine plus caller overlay, its own
transactional undo trail, memo replay, a pinning-fact discipline, harvest and
feed caps, a two-tier retirement state machine, and `--incremental-cbp-reset`
shipped as a production flag --- motivated by one benchmark family where "4
adopting solves near solve 115 are the entire 40×". It is whole-formula
preprocessing in a design whose central invariant is that facts must not cross
levels, which is why it then needs pinning facts to stay sound, and why it
already produced one soundness bug (`precise.smt2`, fixed by `56de220c`/`ee8685bb`).
The *engine* is the best-built new component in the branch (see Part II); the
question is whether it is earned at all. D7 shows its retirement heuristic does
not measure what it claims.

**Policy constants.** 21 `static const` in `IncrementalSolver.cpp` plus a
self-doubling `promoteAfterSolves`, the 32/3 engagement ordinals, and the 4×
relief ratio:

| Constant | Value | Derivation stated? |
|---|---|---|
| `inprobingRetireSolves` | 8 | measured class split (1--2 vs 20+ solves) |
| `inprobingRetireMinVars` | 20000 | measured |
| `defInlineCap` | 200 | measured (10M clauses from 7 conjuncts) |
| `bigFormulaCap` | 20000 | measured |
| `firstStackCollapseMinNodes` | 128 | asserted, not derived |
| `firstStackMinReencodeLimit` | 1000000 | policy tie-break |
| `cbpRetireBarrenNeverFixed` | 8 | benchmark-fitted (and see D7) |
| `cbpRetireBarrenFixed` | 64 | benchmark-fitted |
| `cbpHarvestCap` | 4096 | asserted |
| `cbpFeedCap` | 200000 | asserted (and see D7b) |
| `reachesAnyOf` walk budget | 2000 | asserted |
| `actLitRetireAge` | 16 | none |
| `trailReuseVarLimit` | 100000 | measured |
| `trailReuseFpRetireSolves` | 7 | measured |
| `trailReuseLateArrayFpProbeSolves` | 3 | measured |
| `trailReuseEstablishedVarFloor` | 10000 | measured |
| `trailReuseRefinementClauseFloor` | 500 | asserted |
| `promoteAfterSolves` | 8, doubling | measured |
| big-stack worker | 256 MB | derived (27k chained defines → depth ~25k) |
| `symbolVisitPage*` | 2¹⁶ | implementation detail, fine |

Plus 8 new CLI flags (`--incremental`, `--incremental-auto-engage-at`,
`--incremental-profile`, `--incremental-cbp-reset`,
`--incremental-cbp-bootstrap-limit`, `--incremental-reencode-limit`,
`--incremental-promote-units`, `--incremental-inprobing`), two of which are
purely diagnostic and one of which exists to bound a workaround.

Worse than the count is the **mutual gating**: trail-reuse retirement gates
inprobing retirement (`:4729`) *and* unit promotion (`:5502`); inprobing
retirement also disables `elim` and `shrink` (undocumented outside the commit
message and `SATSolver.h` --- F36 in the ledger). Three independent constant sets
implement one latent concept: *session shape*.

**The measurement apparatus as deliverable.** 171 hand-maintained counter fields
across two structs, ~200 lines of stream formatting, and 1,938 lines of Python
(`incremental-bench.py` 848, `incremental-bench-report.py` 1090) in the repo. The
counters are correct (verified) and the harness's verdict discipline
(`FULL_OK` / `PREFIX_ONLY_INCONCLUSIVE` / `DISAGREEMENT`) is genuinely good. But
the profiler is not behaviour-neutral (D6), and it did not catch either soundness
defect --- because it measures work, not correctness.

## 5. Layering inventory

| Violation | Site | Note |
|---|---|---|
| Node factory reads a mutable solver-mode flag | `SimplifyingNodeFactory.cpp:946` | D10; contradicts the branch's own documented invariant |
| Driver owns the batch pipeline's mutable tables | `:2884-2893`, `:4241-4243` | `arrayToIndexToRead`, `ack_pair`, `recordTouchedReads` assigned by value both ways; D8 |
| Model channel is a shared `SolverMap` with a hand-rolled withdraw protocol | `:3839-3886` | `batchSimp->Return_SolverMap()`; correct today, but the protocol is the driver's and the map is not |
| `construct_counterexample_flag` used as an accumulator | `STP.cpp:448`, `:4337` | D9 |
| `bm->ValidFlag` poked directly | `:4076`, `:5813` | benign (Part II) but reaches into manager state |
| Engagement policy split across two frontends | `cpp_interface.cpp:712-731`, `c_interface.cpp:809-811` | the C API hard-codes 3 and cannot see `--incremental-auto-engage-at` |
| `exit(-1)` in a library | `:149`, `SATSolver.h:339` | pre-existing STP convention; unreachable today |

## 6. Resource shape

The driver is a **never-free** design by construction: `rootLitOf`,
`clauseMassOf`, `aigRootOf`, `preparedPieceOf`, `fragmentCache`,
`symbolsOfCache`, `readsOfEncoded`, `cbpMemo`, `myReads`, `myAckPairs`, and
`exactStackKeepAlive` all hold `ASTNode`s as keys, so every node of every formula
version ever seen is pinned; the AIG and bit-blast memo grow monotonically too.
The relief valve reclaims **only** the SAT solver. For the KLEE-class workloads
this feature targets (10⁴--10⁵ queries), node/AIG memory is the dominant
resource, and nothing reclaims it. This is documented as a limitation; it is
worth re-reading as a design constraint rather than a footnote.

**Per-check thread creation.** `runOnBigStack` (`:4542-4573`) creates and joins a
fresh 256 MB-stack `pthread` **per check-sat**, and again per deferred model
materialization. It is purely a stack-size trick (the thread is joined
immediately; there is no parallelism), working around recursion depth in the
batch passes --- a problem the project already knows about (see the deep-DAG
stack-safety work). One persistent worker fed by a queue would remove the
per-query `mmap`/`munmap` of a 256 MB reservation. On the many-small-queries
workloads this feature exists for, that is measurable fixed overhead --- and it
is a candidate explanation for the RTOS tail the old review left unexplained.

---

# PART IV — COST MODEL AND MEASUREMENTS

## The engagement ordinal is a symptom

```cpp
// cpp_interface.cpp:712-731
int64_t engageAt = bm.UserFlags.incremental_auto_engage_at;
if (engageAt < 0)
  engageAt = delayed_bv_auto_engagement ? 32 : 3;   // QF_BV / QF_ABV : everything else
```

A policy that says *"for the theory STP is built for, do not use the incremental
engine until the 32nd solve"* is a strong statement about where the incremental
path stands relative to the batch pipeline. The commit message records a
"targeted 107-session sweep" finding 32 to be the best finite compromise.

Read together with D4, the interpretation is: **per-check reconstruction cost
exceeds encoding-reuse benefit for up to 31 solves on QF_BV.** The principled
version is not a larger ordinal --- it is to make reconstruction incremental and
then re-derive the ordinal from a cost model. D4's three fixes are the concrete
path.

Two secondary problems with the ordinal as implemented:

- The C API hard-codes `incrementalSolvesRun > 1` (threshold 3) with no logic
  knowledge, and `--incremental-auto-engage-at` cannot reach it. The documented
  override is silently inert for C API clients.
- The counter counts real checks made **before** the first push, so two pre-push
  checks can cause the first post-push check to engage immediately. That is not
  the stated "two batch warm-ups in the incremental session" policy. *(Carried
  over from the previous review; still true.)*

## My measurements (this review)

All on `build/` (Release + assertions), tip `278552ce`. Indicative only --- not
interleaved quiet-box A/B.

**Fixed per-check cost, toy stack** (`incremental-profile.smt2`, 3 levels, 9
nodes, 6 checks, `--incremental --incremental-profile`):

```
total-us=3795  semantic-us=1758 (46%)  prepare-us=467  encode-us=356
cbp-us=450     sat-us=210 (5.5%)
```

**Scaling with depth** (agent-generated `w1_{100,200,400}.smt2`): see the table in
[D4](#d4--cost-the-privacy-predicate-makes-a-no-op-check-quadratic-in-stack-depth).
Per-check semantic reconstruction 9.4 ms → 13.2 ms → 20.4 ms for depths
100 → 200 → 400.

**Relief-valve regime check:** `reencode-relief.smt2` with
`--incremental-reencode-limit 500` fired exactly one rebuild both with and
without `--incremental-profile`. The two regimes are established from the code
paths (D6), not from a divergence on that file.

## Test-suite shape

69 files, 87 RUN lines in `tests/query-files/incremental-tests/`:

| flag | RUN lines |
|---|---|
| `--incremental` | 73 |
| `--check-sanity` | 26 |
| `--incremental-profile` | 17 |
| `--array-equality` | 10 |
| `--incremental-reencode-limit` | 8 |
| `--incremental-cbp-reset` | 5 |
| `--incremental-auto-engage-at` | 4 |
| `--disable-cbitp` | 4 |
| `--ackermanize` | 4 |
| `--incremental-cbp-bootstrap-limit` | 1 |

Two structural observations. **(a)** The suite tests the *forced* mode; production
runs the *automatic* mode, whose first solves take entirely different paths.
**(b)** Only 26 of 87 lines use `--check-sanity` --- the one check that catches
both D1 and D2.

---

# PART V — WORK QUEUE

Re-ordered 2026-08-11 after D1, D2 and most of D4 were fixed. The ordering
principle changed with them: while two silent wrong answers stood, everything
else was noise. With no known soundness defect remaining, the question becomes
*what would find the next one*, and only then *what costs the most*.

Each item states what it buys, so the order can be argued with rather than
followed blindly.

## Tier 0 — before this branch merges

### 0.1 Re-run the corpus campaign with model validation

**The single highest-value action available, and a merge gate.** Two proven
soundness defects survived a 22,999-file differential campaign because it
compared answer streams only, and a wrong `sat` produces a perfectly
self-consistent stream. `scripts/incremental-bench.py` now gives the candidate
arm `--check-sanity` by default (`9bbdd056`), so a re-run actually tests what
the last one was assumed to.

Everything below this line is an optimisation of a system whose correctness at
scale is currently unverified. Do this first.

Add arms that break the masking relationships, because both defects were partly
hidden by *other* mechanisms re-deriving what they lost:
`--disable-cbitp`, `--no-incremental-promote-units`, and
`--incremental-auto-engage-at 1`.

### 0.2 Fix D5 --- non-deterministic naming in front of the block cache --- DONE, `45504ef9`

**Under-rated in the first review; it belongs here.** `RemoveUnconstrained`
mints counter-named variables, and it sits directly in front of a cache keyed
on the resulting node, so an **identical re-pushed stack misses the cache and
re-encodes from scratch**: 4,177 -> 56,299 SAT variables over 15 identical
repeats. That is unbounded growth on precisely the workload incremental solving
exists for, it silently defeats the branch's headline reuse claim
(`docs/incremental-solving.rst:341-344` promises the opposite), and on a long
session it ends in memory exhaustion rather than a wrong answer --- which is
why it reads as a performance note and is really a robustness bug.

Fix: memoise the pass by input node, storing `(output, eliminated definitions)`
together --- which restores determinism *and* makes a repeated stack O(1) above
the transform --- or give the stand-ins deterministic names via the branch's own
`CreateDeterministicVariable`.

### 0.3 Fix D3 --- unbudgeted whole-base pass welded to `rebuildEncodings` --- DONE, `e093b0d2` (residue below)

A semantic pass over the entire base --- constant-bit propagation, equality
propagation, simplification, unconstrained elimination --- fires on **all four**
rebuild reasons, including the two that are pure SAT-backend configuration
latches, with no size test, no trial gate, no memo and no off-switch. Measured
at **9.4 s** inside a single trail-retirement rebuild whose entire purpose was
to set one CaDiCaL option. Every neighbouring use of those same passes is
budgeted.

Fix: content-key it on the base conjunction, give it the same halving gate its
neighbours have, and invoke it only from the `Relief` path. Clear
`baseEliminatedDefs` in `rebuildEncodings` beside `restoredBaseRoots` (D3b).

**What `e093b0d2` did not do.** It gated the semantic pass on the rebuild
reason, so the three pure-SAT-configuration rebuilds (inprobing, trail,
promotion) no longer pay it. On the **Relief** path --- the one reason that is
genuinely about size, and the only one that still runs it --- the pass is
unchanged: whole-base, unbudgeted, unmemoised, the shape D3 measured at 9.4 s
over 23,294 conjuncts. That is defensible, because a relief rebuild is
re-encoding everything anyway and the size gate makes it rare, but it is not
closed: nothing bounds the pass against the rebuild it is part of. Re-open if a
workload is ever seen taking relief rebuilds on a large base.

**Budgeted (`--incremental-base-resimplify-limit`, default 100,000 DAG nodes).**
The pass is an optimisation, so a base too large to digest is now re-encoded
raw --- the path an array base and the three non-size rebuild reasons already
take --- and the size is what triggers it, which is what the rebuild itself
still lacks. The budget measures the base CONJUNCTION, not the sum over
conjuncts, because base conjuncts share structure. Pinned by
`relief-base-resimplify-budget.smt2`, which takes real relief rebuilds and
checks the answers against both the unbudgeted pass and the batch pipeline;
it fails with the budget removed.

## Tier 1 — before any measurement or tuning is trusted

### 1.1 Fix D6 --- make the profiler behaviour-neutral --- DONE, `635b3b04`

`--incremental-profile` substitutes a different live-mass estimator, so it
changes **when relief rebuilds fire**. Any number taken with the profiler
describes a configuration production does not run, and 17 of the suite's RUN
lines assert counters produced under it.

This gates the timing campaign and every tuning decision below it: fix it
*before* re-deriving thresholds, or the thresholds are fitted to the profiled
regime. Compute one live value for the decision on both paths; let profiling add
reporting only. If the exact walk is affordable every solve it is the right
production estimator and roughly 80 lines plus 4 fields can be deleted.

### 1.2 Re-derive the engagement ordinal --- seam DONE `60e83767`; ordinal MEASURED, unchanged

**Newly worth doing, and potentially the largest single win.** QF_BV/QF_ABV
sessions are held on the batch pipeline until their **32nd** solve, a threshold
fitted to a per-check reconstruction cost that `00ea5c1e` has now substantially
reduced. The number may simply be wrong now, and every solve before it is a
session not getting the feature.

**The seam is done (`60e83767`).** `IncrementalSolver::automaticEngagementReady`
is the single policy; both frontends call it, and `INCREMENTAL_AUTO_ENGAGE_AT`
gives `vc_setInterfaceFlags` a way to reach the ordinal, which no C API client
previously had. Five unit tests and four C API tests pin it.

**The ordinal was re-measured and is unchanged, deliberately.** The 32 was
fitted on a 107-session corpus that is not available here, so it cannot be
re-fitted against the same evidence; what follows is a synthetic sweep, and it
is reported as such. Sixteen QF_BV variables, a six-conjunct base, then N
rounds of push/assert/assert/check --- once popping each round, once monotone.
Interleaved, medians of three, times in ms:

| session | at=0 (batch) | at=1 | at=3 | at=8 | at=16 | at=32 |
|---|---|---|---|---|---|---|
| popping-8 | **25** | 52 | 50 | 33 | 25 | 25 |
| popping-16 | **33** | 154 | 167 | 101 | 45 | 33 |
| popping-32 | **39** | 363 | 355 | 303 | 186 | 52 |
| popping-64 | **64** | 1107 | 1056 | 989 | 710 | 463 |
| monotone-8 | 58 | 65 | 62 | 69 | 58 | **58** |
| monotone-16 | 262 | **196** | 206 | 212 | 315 | 272 |
| monotone-32 | 234 | 188 | **160** | 211 | 258 | 226 |
| monotone-64 | **81** | 81 | 84 | 94 | 81 | 81 |

This reproduces exactly the tension the fitting commit described, and it says
something the ordinal cannot act on: **the discriminator is the session's
shape, not its length.** A monotone session that engages at 1--3 beats the
same session at 32 by about 1.4x (196 against 272; 160 against 226) --- that is
the win being left on the table. A pop-per-query session loses by 7x at depth
64 (463 against 64) and would lose by 17x if it engaged at 1. No single ordinal
separates those, because they differ in whether retained encoding can ever be
reused, not in when.

So the ordinal is not the thing to tune, and lowering it on this evidence would
trade a measured 1.4x gain on one shape for a measured 7x loss on the other.
What the seam now makes possible is the real fix: `automaticEngagementReady`
takes the session's solve count today, and a `worthEngaging(stack, solvesRun)`
that also sees whether the session has ever popped --- retained encoding is
dead the moment it does --- can hold pop-per-query sessions on batch
indefinitely while engaging monotone ones almost immediately. **Do not land
that on synthetic sessions.** Re-run this table on the 107-session corpus
first; if it shows the same shape split, the ordinal should be replaced rather
than re-fitted.

## Tier 2 — real costs, no correctness exposure

### 2.1 Fix D7 --- CBP retirement measures the wrong thing --- DONE, `8ab75f81` + `e438bbba`

`cbpEverFixed` is set by a level's own assumed truth, so the 8-divergence tier
is unreachable for array-free sessions and the two tiers are effectively
inverted. Drive the leash off evidence that a fixing *crossed a level boundary*
--- the property the pass exists for.

**D7b, done in `e438bbba`.** The cap is now charged what a level ADDS: the
engine answers `freshNodeCount` under `extendParentMap`'s own stopping rule, so
an accepted feed grows its dependency set by exactly what was charged, and that
is asserted. The old per-level sum billed one shared cone once per level that
mentioned it --- nine charged against five retained on a three-level toy. A
refusal is no longer the session-wide futility latch: it is keyed to the
fed-level count refused and released once the stack falls back below it, which
is what the trail already does for `callCbpOff`. `--incremental-cbp-feed-cap`
makes both halves reachable from a test; both regressions were confirmed to fail
against the old accounting.

### 2.2 Fix D8 --- per-encode registry copy and whole-table anchors --- DONE, `8ffd109f`; D8b CLOSED, measured

Every array encode installs the entire session registry into the batch
transformer by value and copies it back, and the transformer then re-conjoins an
index-binding equation for **every registry row with a computed index** onto
every array conjunct --- including rows from popped levels. Hand the transformer
a registry by reference and emit anchors only for `touchedReads`, which the
driver already collects.

**D8b: CLOSED, declined with the measurement (`95014cd7`).** Theory lemmas are
charged to the emitting solve, keyed on that solve's whole-stack conjunction, so
one push of an unrelated level mints a key whose mass is zero and every lemma
ever emitted stops counting at once. The code called that a middle ground; it is
not one --- the only two behaviours are "repeat the identical stack" and "drop it
all". Reproduced on a 250-level read-heavy QF_ABV churn session forced to the
valve at `--incremental-reencode-limit 8000` (125x tighter than the default,
which no constructed workload reaches at all): **one** relief rebuild the true
live mass would not have permitted, and 646 of 6800 refinement clauses
re-derived after it. Across three interleaved pairs the time is a wash --- the
rebuild compacts what it discards.

The remedy is not free. Counting lemmas permanently live removes the rebuild and
then never relieves at all on that session, which is the failure the policy
exists to prevent, and it is the extreme the design already weighed and rejected.
Charging mass to the live read rows is the answer that would be right, and needs
always-on per-row clause accounting: the only per-row liveness today is a
**profiling** counter, and feeding that into the valve recreates D6 exactly.
Declined on the same standard as F10, F23 and D12; the code now states the cost
instead of misdescribing the behaviour, including the map's one-entry-per-
distinct-stack growth, which cannot be bounded without changing the policy.

### 2.3 Finish D4 --- the remaining linear term --- CLOSED, measured

Both things this item named were profiled and neither dominates. On a
400-level stack with one elimination per level the driver is semantic-bound
(653 ms of 809 ms) but the profile is **flat**: the largest single entry is
6.9%, and `ensureLevelOccurrences` --- the per-solve index rebuild that
longest-common-prefix maintenance would remove --- does not reach 3%. Neither
LCP-maintaining the index nor restructuring the per-check context rebuild is
worth its risk on that evidence. Re-open only if a real workload's profile says
otherwise.

What the profile *did* justify was taken (`46f2af21`): `symbolsOfCache` hashed
rather than ordered --- probed once per candidate per piece per check, never
iterated --- and the level's own symbol set hoisted out of the per-candidate
loop in `namedByAnotherLevel`. About 9%: medians 830 ms → 757 ms, ahead in all
six rounds of an interleaved A/B between saved binaries.

### 2.4 Fix D13 --- one transaction for elimination and context inlining --- DONE, `570bce9c`

Recovers the eliminations D1's fix conservatively refuses (measured: 4 of 93
across the corpus, 2 of them genuine) **and** deletes `collectCtxExportedSymbols`
outright. Strictly better than both the current and the pre-fix state. Verify
`replace`'s transitive expansion before relying on it. Do **not** implement it by
predicting the re-join's declines in a second place --- that is how D1 happened.

### 2.5 Fix D12 --- incremental symbol map --- CLOSED, measured

~1.8 ms per call, several calls per refinement round, walking every symbol ever
blasted. Maintain it at `totalizeSymbol`/`ensureEncoded`/`rebuildEncodings` and
return it by reference.

## Tier 3 — batch-path regressions this branch introduced

These are small, but they are behaviour master did not have, and two of them
touch code outside the driver.

### 3.1 D10 --- node-construction rewrite gated on a session mode flag --- DONE, `0767b22a`

`SimplifyingNodeFactory` reads `UserFlags.incremental_solving`, which `push()`
sets, so a pushing session gets a different word-level DAG **even when the driver
never engages**. It contradicts the branch's own stated invariant and it means
the batch-vs-incremental differential compares two engines handed different node
graphs. Keep the rewrite unconditional; express encoding-order preferences where
order is chosen. Split the flag into request vs session state (D10b: a
`push` followed by `reset` currently promotes the whole rest of the session to
forced-incremental).

### 3.2 D9 --- `construct_counterexample_flag` made sticky --- DONE, `060cc34f`

One array round or one `:produce-models` permanently disables the documented
unchanged-stack cache shortcut and re-enables per-solve counterexample
construction in the batch pipeline. Give the driver a private
`needsCandidateModel`; restore per-check derivation.

## Tier 4 — cleanups, any order

### 4.1 D11 --- dead code --- DONE, `8a618f99`

`Backtrack.h` (273 lines + test, zero production users): delete it, **or** land
its first consumer. The natural one is the occurrence index `00ea5c1e` just
added --- it is insert-only per level, exactly this header's discipline.
`canHandle()` is a `return true` stub whose batch fallback is therefore dead;
`batchTablesSeeded` is write-only with a stale comment;
`CbpCallerCheckpoint::offBefore`/`conflictBefore` are a dead store/restore pair.
Switch the three `Cpp_interface` model readers to `hasIncrementalSolver()` so a
batch session stops allocating a driver to ask whether one exists.

### 4.2 Consolidate session shape --- PARTLY DONE; the object declined

Trail-reuse retirement, inprobing retirement and unit promotion are three
constant sets with mutual gating (trail gates inprobing gates promotion),
implementing one latent concept.

**The duplication is gone.** The inprobing-retirement predicate --- a five-term
conjunction over two fitted constants --- was written out in full at three sites
that must agree: whether to retire now, whether a rebuild happening anyway can
absorb the retirement, and whether to take it as that rebuild lands. The third
site exists *because* the first two disagreeing by one solve cost a measured 2x
on a double rebuild, which is the strongest possible argument against keeping
three copies. It is now one `inprobingRetirementEarned()`.

**The `SessionShape` object is declined.** The three concepts have genuinely
different lifetimes --- trail reuse is decided per solve, inprobing retirement
is a one-way latch on the backend instance, unit promotion is per level and
survives rebuilds --- and a single value type computed per solve would have to
carry all three anyway while implying they move together. What made them look
like one concept was the shared constants and the copied predicate; with the
predicate shared, what remains is three policies that read each other's
results, which is what the code says. Re-open if a fourth consumer appears.

### 4.3 Backend epoch as an object --- window CHECKED `497bb966`; the object declined

~28 fields hand-reset in `rebuildEncodings`, four trigger sites, one eligibility
predicate written out three times.

**The checkable part is done (`497bb966`).** The configuration window is now an
invariant the code enforces rather than a convention backed by a third-party
`abort()`: the six setters carrying the rule are non-virtual facades that check
before dispatching, following the pattern `addClause` and `solve` already use in
that header. It needed no new state --- `submitted_clauses` already counts what
STP handed *this* backend instance, and a rebuild constructs a new one, so
`configurationOpen()` is that counter being zero. The whole suite passes in the
assertion build, so nothing configures late today; three unit tests pin the
window itself. The thrice-written predicate is 4.2's, and is also done.

**The `BackendEpoch` value type is declined.** What is left of this item after
the above is moving ~28 fields from one struct into another so that
`rebuildEncodings` assigns an object instead of assigning fields. That is a
mechanical rewrite of the reset path of a 6,000-line file whose invariants are
subtle and mostly untested at that granularity, in exchange for no behaviour
change and no new check --- the check was the part with value, and it landed
without the refactor. The field count is the only evidence offered for it. Do it
if the epoch ever needs to be copied, compared, or snapshotted; until then it
buys a shorter diff at the cost of a risky one.

### 4.4 Rebalance the test suite --- DONE

**DONE.** The complaint was that production engages the driver automatically
while the suite almost always forced it, and that models mostly went
unvalidated. Both are addressed; the figures below are current.

Before: 78 files, 101 RUN lines, 84 forcing `--incremental`, **9 files**
touching the automatic path, 23 carrying `--check-sanity`. (An earlier revision
of this item quoted 73 of 87 and called
`elimination-context-export-default-engagement.smt2` the only test reaching
engagement-at-32; both were wrong when written --- `engagement-default-bv.smt2`
and `engagement-default-abv.smt2` were added by `06dbdccf`, two commits before
this review began.)

After: 81 files, 139 RUN lines, **43 files** touching the automatic path and
**33** carrying `--check-sanity`.

The automatic coverage came from a second RUN line on 32 behaviour-critical
tests, substituting `--incremental-auto-engage-at 1` for `--incremental`. That
is not a cosmetic difference: it engages through the automatic predicate
instead of `incremental_from_start`, so `firstForcedIncrementalSolve` is false
and the forced-first recovery family (F3) is not taken --- exactly the shape
production runs at solve 32. All 32 passed unmodified. A sweep of all 72
force-`--incremental` files found 71 give byte-identical answers on the
automatic path; the one that differs,
`ackermanize-model-cache.smt2`, differs only in **which** satisfying assignment
it reports, and the automatic path agrees with the batch pipeline while the
forced path does not.

Two files are deliberately left without `--check-sanity`, with the reason
recorded in each: `produce-models-lazy.smt2` exists to check that a model is
built only when asked, and the flag always asks; `ackermanize-model-cache.smt2`
pins the values the model cache returns, and the flag reconstructs and can pick
a different assignment.

### 4.5 The untracked findings --- DONE

All seven are resolved --- F9 (`96f14b16`), F16 (`cd34049d`), F26 and F38
(`bac4c110`) fixed; F10 and F23 built, measured and reverted; F22 deferred with
its reason. See [Appendix B](#appendix-b--full-finding-ledger).

### 4.6 Findings the sweep recorded and never queued

Collected here because until now they pointed at a section that does not exist.
None is a correctness item; each needs a decision rather than analysis.

- **F43** --- four re-implementations of the batch preprocessing prefix, three
  replay representations. This row had no write-up anywhere in this document.
  **The shared helper is DECLINED** on two independent readings: the four
  differ on nine axes (pass set, order, `apply` variant, untouchable set, fp
  policy, theory refusal, acceptance gate, elimination filter, replay sink and
  memo key), each using a distinct combination, so a single helper would
  parameterise itself into churn on the most subtle code on the branch.
  **The invariant check is DONE** (`see below`). What remains of this row is
  only the docs table. See
  [D14](#d14--soundness-the-relief-rebuild-keeps-a-definition-whose-dependency-it-just-dropped),
  which came out of exactly this question and was a wrong answer:
  1. **DONE.** `preparePiece`'s assert is ported to `resimplifyBaseAtRebuild`
     and to `preprocessExactStackBlock`: no variable recorded as eliminated may
     occur in anything the pass emits. **Verified to catch D14** --- with the
     untouchable-set closure removed, the assert fires on D14's witness instead
     of the wrong answer being returned silently. On the block pass it is true
     by construction (the emit loop skips any key still in the output), which
     is what makes that pass's unconstrained call safe with no untouchable set
     at all; it is asserted rather than argued.
  2. **DONE, as symmetry, and labelled as such.** The `apply` between
     constant-bit propagation and `RemoveUnconstrained` that batch has
     (`STP.cpp:676-677`) and the exact-stack block has is added. The argument
     for it is concrete --- CBP puts SYMBOL fixings only into the substitution
     map, and `SimplifyFormula_TopLevel` cannot be relied on because
     `is_simplified` is a permanent node flag the driver sets when base
     conjuncts are asserted --- but **no failing case is in hand**: removing the
     line and running the relief corpus with
     `--unconstrained-variable-elimination 0` does not trip the assert. It is
     kept because this pass being the odd one out with nobody checking is how
     D14 happened, and the cost is one DAG walk on a rare path.
  3. **STILL OPEN:** the docs table describing the four prefixes, cheap and
     matching the F36 precedent --- but note it would **not** have surfaced D14,
     since it records pass order, gate and replay channel, and the defect was in
     none of those.
- **F3 --- DONE, and the review's own proposal declined.** The three entry
  conditions are one concept ("this solve has no batch-preprocessed
  predecessor, so run the cheap part of the batch prefix now") applied to three
  DISJOINT stack shapes, plus a fourth consumer inside `exactStackCheckSat`
  and a fifth in the opposite direction (skip a bootstrap that cannot
  amortise). They are mutually exclusive by stack size and run at points that
  cannot be co-located, so merging them is churn.

  **Deriving forced-first from `engagedSolves == 0` would be a defect, not a
  refactor.** That predicate says only "this driver object has not solved
  before", which is also true of the automatic path's first engaged solve ---
  and that solve HAS had batch-preprocessed predecessors. Deriving would widen
  all four policies onto the path production runs, and at the fourth consumer
  it is worse: post-increment, `engagedSolves > 1 || engagedSolves == 0` is a
  tautology, deleting the distinction `45b846fa` introduced. The four tests
  that pin these counters all force `--incremental`, so the change would have
  landed uncaught. The three ways the two facts come apart are all reachable:
  `resetAssertions()` destroys the driver without resetting the frontend's
  counter; the C API's `'i'` flag can arrive after batch queries; a
  `canHandle()` refusal bumps the counter without engaging.

  What was done instead is the residue that does meet the standard: the
  judgement was written character-identically in both frontends, so it is now
  one `IncrementalSolver::forcedFirstSolve` beside
  `automaticEngagementReady`, and the driver asserts the one direction that
  must hold (`forced-first` implies `engagedSolves == 0`) --- exactly the
  mis-plumbing a new frontend would introduce. Two unit tests.
- **F36** --- `--incremental-inprobing` silently disables bounded variable
  elimination, learned-clause shrinking and lucky phases, documented only in a
  commit message and `SATSolver.h`. One paragraph in
  `docs/incremental-solving.rst` closes it.
- **F44** --- ~20 fitted constants and 8 flags, with the most intricate policy
  undocumented.
- **F7 (second half)** --- `symbolsOfCache` is never cleared, so it holds a
  symbol set for every node measured since the session began. Entries can never
  be stale (symbol sets are a pure function of the node), so a clear at
  `rebuildEncodings` is pure reclamation. D4 is marked FIXED/closed while this
  named sub-item is neither fixed nor declined.
- **F24** --- the deterministic-name keep-alive pin is a convention held at one
  call site, with no assertion and no test. Move it into
  `CreateDeterministicVariable`, or pin it with a test.
- **Per-check thread creation** --- `runOnBigStack` spawns a worker per check.
  It is this document's own leading hypothesis for an unexplained
  small-session loss, and it was never queued. A persistent worker, or an
  explicit acceptance.
- **Model channel `SolverMap`** ([Part III.5](#5-layering-inventory), row 3) ---
  correct today; the review never says whether not owning the map is accepted.

## Tier 5 — after the above

### 5.1 The three-run timing campaign

Runnable again now D1/D2 are fixed. Run it with `--no-check-models` (validation
is not free and would distort timings), **after** D6, and after 1.2 in case the
engagement ordinal moves.

### 5.2 The assertion journal

[Part VIII](#part-viii--recommended-scoped-state-architecture) remains the right
destination, but 2.3 and 4.2 capture most of its value at a fraction of the
cost. Reassess after they land.

# PART VI — REFERENCE SOLVER INVESTIGATIONS

*(Retained from the 2026-08-07 review. Reference-solver paths and line numbers
refer to the revisions in the table below. Still accurate and still the best
available justification for the design choices.)*

| Solver | Revision read |
|---|---|
| Bitwuzla | `e92a4c517bc4aa9c65551947f7bffe9a57236151` |
| cvc5 | `e8c0387caeceaf631e0d3b114373b1bc7942334b` |
| Z3 | `4af3410d104ad291437275ad1553d2b82b152727` |

The reference solvers use different internal machinery but converge on the same
separation of concerns: (1) a scoped assertion source or working stream; (2) an
explicit frontier for each independently advancing pipeline, or an atomic commit
boundary across stages; (3) scoped preprocessing facts and model reconstruction;
(4) permanent structural encoding where sound; (5) explicit query/assumption
result lifetimes; (6) hard gates or repair rules for transformations that are not
naturally incremental.

## Bitwuzla: the closest end-to-end model

One scoped `AssertionStack`, a solver-wide backtrack manager, a preprocessor, and
a solver engine (`src/solving_context.h:159-180`). Each assertion is appended with
its scope level (`src/backtrack/assertion_stack.cpp:24-34`); push records a count
watermark, pop truncates and clamps all registered consumers
(`assertion_stack.cpp:126-157`). It is a mutable *working stream*, not an
immutable raw journal: preprocessing may replace entries and insert derived
assertions, with original user assertions retained separately
(`src/solving_context.cpp:112-123,245-248`).

**Independent assertion views.** An `AssertionView` carries its own `d_index` and
exposes only unseen assertions (`src/backtrack/assertion_stack.h:24-104`). The
preprocessor and solver engine own separately tracked views
(`src/preprocess/preprocessor.cpp:42-60,70-118`;
`src/solver/solver_engine.cpp:32-54,457-494`), so advancing one does not claim
work for the other. Pending assertions carry their insertion level, so each
consumer can defer across pushes and later synchronize. The views are not freely
reorderable: preprocessing always runs before the solver-engine view consumes its
output (`src/solving_context.cpp:52-70`).

**Substitution safety.** Bitwuzla handles the core incremental-elimination hazard
explicitly: if `F(b)` was already encoded and a later batch discovers `b = s`, the
equality may simplify new formulas but is **not** replaced by `true` --- the
defining equality is retained unless the variable first appeared in the current
batch (`src/preprocess/pass/variable_substitution.cpp:751-803,820-827`). A
deliberately conservative forward-only policy: it loses eliminations STP's
privacy analysis can recover, and its lifetime invariant is far simpler. **D1 is
exactly the hazard this policy exists to prevent.**

**Permanent encoding and active roots.** The default bit-vector engine keeps its
bit-blaster, AIG-to-CNF encoder, and SAT backend alive; new top-level assertions
are encoded with roots asserted, retractable ones definitionally encoded without
a unit and supplied as assumptions each solve
(`src/solver/bv/bv_bitblast_solver.cpp:154-187,225-256`). Term-to-AIG and
AIG-to-CNF maps permanent; active root vectors scoped. **This is almost exactly
STP's design.** Mode-specific exceptions exist (unsat-core production routes all
user assertions as assumptions; interpolation schedules SAT/CNF reconstruction
after pop).

Bitwuzla's FP solver separates a permanent word-blast cache from backtrackable
records saying the associated validity constraints are active in the current
scope (`src/solver/fp/fp_solver.cpp:64-109`; `src/solver/fp/word_blaster.h:162-166`).
STP's array-row and FP-side-condition designs observe the same
content-cache/active-side-condition rule.

**Models and temporary assumptions.** `check_sat(assumptions)` pushes a temporary
context, appends assumptions as ordinary formulas, solves, and **delays the pop**
so values and cores still observe the solved state
(`src/api/cpp/bitwuzla.cpp:1609-1643`); the next mutating call realizes the
pending pop (`:1808-1819`).

**What to borrow:** the level-stamped working stream, separate preservation of
original inputs, independently tracked stage views, deferred processing, and the
permanent-content/scoped-activation distinction. **Not** every backtrackable
container.

## cvc5: context-dependent state and explicit flush boundaries

Assertions in a user-context `CDList` (`src/smt/assertions.cpp:36-40`); a
user-context `CDO<size_t>` is the frontier into it
(`src/smt/smt_driver.cpp:151-155,204-215`); only `[frontier,end)` enters the
pipeline.

**Container cost models** rather than one universal map: `CDO<T>` for scoped
scalars, `CDList` for append/truncate, insert-only maps/sets that trail inserted
keys, fully mutable context-dependent maps where overwrite restoration is
required, and notification objects for caches cheapest to invalidate wholesale.
It also distinguishes the *user assertion* context from the *SAT/theory decision*
context.

**Flush before push.** cvc5's raw assertions are not individually stamped, so it
enforces a different clean invariant: flush all pending assertions through
preprocessing and into the propositional engine before a user push
(`src/smt/smt_driver.cpp:119-147`; `src/smt/context_manager.cpp:142-187`).

> Two sound alternatives: **Bitwuzla** stamps each pending assertion and lets each
> stage synchronize lazily; **cvc5** makes raw-to-internal processing atomic and
> flushes before establishing the next scope. STP should choose explicitly, and
> should not let a single cursor imply that several independently fallible stages
> have all completed unless their transaction boundary really is atomic.

**Incremental preprocessing.** If preprocessing finds `x = t` after `x` has
appeared in materialized formulas, cvc5 keeps the equality as a real assertion
while using the substitution on subsequent inputs
(`src/preprocessing/passes/non_clausal_simp.cpp:316-346`) --- the same semantic
rule as Bitwuzla through different structures.

**SAT lifetime.** The Minisat-derived CDCL(T) backend tags variables and clauses
with assertion dependency levels and can physically remove them above a saved
level; the CaDiCaL path uses activation literals through the attached propagator;
the dedicated BV bit-blasting solver resembles STP/Bitwuzla. **STP should not
copy clause-level deletion** --- it depends on owning the SAT solver's internals.

**Reset.** `reset-assertions` unwinds user assertions and reconstructs the main
propositional engine, SAT solver, and CNF stream while retaining the theory
engine (`src/smt/smt_solver.cpp:102-117`). STP's live-journal replay across a
fresh backend is a stronger, branch-specific rebuild contract.

## Z3: cursor-based rewriting with replay and repair

**Hybrid driver selection.** `combined_solver` wraps a from-scratch child and an
incremental child (`src/tactic/portfolio/smt_strategic_solver.cpp:153-188`); both
receive every raw assertion; a push, pop, assumptions, or an assertion after a
completed check selects the incremental child
(`src/solver/combined_solver.cpp:162-220`). Z3 deliberately **duplicates**
frontend state rather than translating optimized batch state at the switch. STP
chose a related but cheaper policy.

**Assertion cursor and scoped simplifier state.** Dependent formulas in a scoped
vector with append-only ingestion and a mutable unprocessed suffix; `qhead` marks
the committed prefix (`src/ast/simplifiers/dependent_expr_state.h:45-88,119-185`);
simplifiers iterate only `[qhead,qtail)`. Push trails the cursor and frozen-symbol
state; pop restores. The classic `asserted_formulas` path has the same discipline
(`src/solver/assertions/asserted_formulas.cpp:190-242,266-307,491-537`).

**Freeze, replay, and repair.** Once a prefix is handed to the backend, Z3 freezes
the symbols it contains (`src/ast/simplifiers/dependent_expr_state.cpp:92-100`).
Its model-reconstruction trail distinguishes equivalence-preserving
definitions/substitutions from *loose* substitutions, loose constraints, and
hidden terms that must be disabled or replayed when later formulas intersect them
(`src/ast/simplifiers/model_reconstruction_trail.{h,cpp}`):

- stable definitions may rewrite the new suffix;
- a loose substitution is **disabled and its equality reasserted**;
- a loose removed constraint is replayed;
- the same records reconstruct eliminated values in the model.

> The taxonomy is powerful, but incorrectly classifying a loose transformation as
> equivalence-preserving is a direct soundness risk. **STP's private-elimination
> screening is a specialized form of the same repair idea, currently without a
> first-class level record to rewind --- and D1 is exactly the misclassification
> this warns about.**

**Three distinct lifetimes** --- user assertion scopes, temporary
query/assumption/search scopes, SAT decision/theory scopes --- each either
trailing mutations or exposing a watermark/pop hook
(`src/smt/smt_context.h:677-727`; `src/smt/smt_context.cpp:3122-3155,…`).

**Incremental SAT mode.** `inc_sat_solver` is especially close to an STP target:
formula log, `m_fmls_head`, per-scope limits, one bit-blaster, one persistent SAT
solver (`src/sat/sat_solver/inc_sat_solver.cpp:50-82`); user scopes are marker
literals; pop drops markers and garbage-collects clauses mentioning popped
variables while retaining learning over survivors
(`src/sat/sat_solver.cpp:351-373,1887-1912,3765-3800`). SAT simplification
explicitly disables unsafe variable/clause elimination in incremental mode ---
the same gate STP applies by substituting plain MiniSat for the simplifying one.

## Convergence table

| Question | Bitwuzla | cvc5 | Z3 | STP branch |
|---|---|---|---|---|
| Assertion source | Scoped original-input list + level-stamped mutable stack | User-context raw `CDList` | Scoped dependent-formula vector with mutable suffix | Per-level raw `ASTVec`, destructively conjoined |
| Unprocessed work | Stage-ordered assertion views | One context-dependent frontier | `qhead` per simplifier | Recomputed whole-stack loops + subsystem memos |
| Pop of semantic state | Backtracked containers, clamped views | Context-dependent objects | Trails and watermarks | Mostly reconstruct next check; manual repair |
| Reprocess old levels | No | No | Only if replay/repair invalidates | Metadata rebuilt; heavy transforms usually cache-hit |
| Structural BV encoding | Permanent (default path) | Persistent in BV solver | Persistent in incremental SAT mode | Session AIG/cache + backend-epoch CNF/root map |
| Retractable assertions | Assumed roots | Assumptions / clause levels / activations | Marker/assumption scopes | Root or per-level activation assumptions |
| Late variable definition | Keep equality unless safe in current batch | Reassert if symbol already materialized | Freeze, or replay/repair | Dynamic privacy test + future-content invalidation **(D1)** |
| Temporary assumptions | Delayed-pop assertion scope | Delayed cleanup of temp context | Query scope/proxies | Temporary frontend level, solved state retained |
| Batch path | Same engine, gated passes | Same driver, option gates | Separate tactic child | Separate batch driver, delayed engagement |

No solver provides a zero-cost universal answer. The shared lesson is not a
container: **state lifetime is explicit and local rather than inferred by
reconstructing the whole active query.**

---

# PART VII — STATE-LIFETIME AUDIT

*(Retained and updated. The table is still accurate at tip `278552ce`.)*

| Lifetime | Representative state | Current mechanism |
|---|---|---|
| Session-owned semantic content | fragment, symbol, DAG-size, generated-name, array-read, eager-Ackermann and FP caches; retired-epoch clause accumulator | Content-keyed maps retained for the `IncrementalSolver` lifetime |
| Explicitly invalidatable semantic caches | prepared pieces, elimination users, screened content | Retained until dependency invalidation or rebuild repair |
| SAT-backend epoch | SAT variables, AIG→variable map, root literals, activation literals, learned clauses, refinement lemmas, retained-submission counter, root/ownership maps, permanent-root/unit mass, pending live-cone snapshot, current/peak live mass | Retained until a relief/policy rebuild; cleared by `rebuildEncodings()` (~28 fields, by hand) |
| Permanent base semantics | `level0Asserted`, `sigma0`, restored base eliminations | Monotone on the SMT-LIB path because reset destroys the driver |
| Active user scopes | raw frontend `ASTVec` levels | Supplied again as a complete snapshot at each check |
| Subsystem views of active scopes | CBP fed prefix/memos, promotion stability, active read-key refcounts, current eliminated definitions | Independently maintained ad hoc, usually by LCP or set difference |
| One query/refinement round | assumptions, active roots, pushed definition context, batch array table, extensionality records | Rebuilt for the current snapshot and discarded |
| Last result | model-pending state, failed literals, assumption→level map, eliminated-definition model seeds | Retained after solve under API-specific invalidation rules |

This table explains why `Backtrack.h` is not yet the missing architecture: it
supplies insert-only containers, but several important states **overwrite**
existing values --- CBP tightens `FixedBits`, preparations are invalidated,
row refcounts rise and fall, SAT literals are replaced wholesale at a rebuild.
Insert-only containers cannot express those lifetimes without a value-undo trail.
*(The symbol→levels index of Part V item 4 is insert-only per level, which is why
it is the natural first consumer.)*

## What is reconstructed on an ordinary check

Even when nothing is newly encoded, `checkSatOnCurrentStack()` does work
proportional to the active stack: compares saved level conjunctions for promotion
and CBP prefix stability; scans levels for FP/array-equality/array fragments
(cached); screens newly observed raw content; splits each live level and
re-harvests pushed definitions into `ctx`/`ctxSources`/`ctxHasFp` in prefix order;
reconstructs per-level symbol counts and the current eliminated-definition list
(usually hitting preparation caches --- **and re-proving privacy on every hit,
D4**); reconstructs roots, activation assumptions, failed-core provenance, active
encoding keys, and live clause mass; computes the active read-key difference and
materializes fresh batch array rows; rolls CBP back to the LCP and feeds the
replacement suffix on divergence; seeds reconstruction definitions when a model
is materialized.

Some whole-query work is **irreducible** under the present semantics: SAT
assumptions must describe every active retractable root; counterexample
validation must establish the candidate satisfies the current query; ordinary
array refinement needs a fresh table containing all live rows; whole-array
equality deliberately reasons about the complete active graph; a SAT rebuild must
rematerialize every live semantic root.

> The objective of scoped state is therefore **not** "make every check O(delta)".
> It is to stop rediscovering semantic facts that already have a precise scope,
> and to make pop correctness local and auditable. D1 and D2 are what
> rediscovery costs.

## Why one monotone preparation cursor would be unsound

1. More assertions can be appended to an existing top level without a push --- the
   conjunction node and level revision change at the same depth.
2. A later assertion can mention a variable privately eliminated from an earlier
   live piece; `screenNewContent()` must invalidate that preparation.
3. A deeper definition may rewrite deeper assertions but must never change an
   already materialized shallower one.
4. Whole-array equality routes all levels through a different pipeline; passing
   the ordinary encoder is not passing the extensionality pipeline.
5. A SAT rebuild invalidates every literal cursor without invalidating the
   semantic preparation cache.
6. `check-sat-assuming` needs individual assumption provenance and a result
   lifetime extending beyond removal of its temporary frame.
7. Stack depth is ambiguous as identity: after pop and push, a new level at the
   same depth is a different scope even if structurally equal.

Consequently the target is an assertion journal with versioned scope identity,
independent stage cursors, and explicit invalidation --- not one global
"processed up to here" index.

---

# PART VIII — RECOMMENDED SCOPED-STATE ARCHITECTURE

*(Retained. Still the right destination; see Part V item 11 for sequencing.)*

### 1. A versioned assertion journal

```text
AssertionEntry = { assertion_id, scope_id, level, raw_formula }
ScopeRecord    = { scope_id, kind, revision, begin, end, cached_conjunction }
Journal        = { epoch, entries, scope_watermarks, next_unique_id }
```

`assertion_id`/`scope_id` are monotone and never reused merely because a depth is
reused after pop; appending at the current level increments that scope's
revision; push records the journal length; pop truncates and reports removed
scope IDs; reset increments the epoch, invalidating every external cursor; the
per-level conjunction is a **cached view**, not canonical data.

`kind` must encode frontend semantics (`permanent_user`, `retractable_user`,
`query_overlay`); depth zero alone does not imply permanence --- the C API
prepends a synthetic `TRUE`, treats every real level as retractable, and appends
`NOT query` only to the local solve vector (`c_interface.cpp:817-830`).

⚠ `STPMgr::getVectorOfAsserts()` **destructively** replaces each level's entries
with one conjunction (`STPManager.cpp:860-883`), so batch warm-ups erase assertion
boundaries before delayed engagement. Either make that accessor non-mutating, or
make the journal canonical from session start at `AddAssert`/push/pop time.

### 2. Independent stage cursors

```text
StageCursor = { journal_epoch, next_entry, per_scope_limits, reset_epoch }
```

Consumers advance only after their outputs are committed. If processing throws,
times out, routes elsewhere, or triggers a SAT rebuild, no unrelated cursor is
advanced implicitly. Low-risk first consumers: assertion/scope metadata and
cached conjunction views; statistics; pure symbol-set and DAG-size memoization;
frontend-aware base-symbol discovery. `screenNewContent()` migrates **later**,
with processed-level dependency state.

### 3. Versioned processed-level records

```text
LevelState = {
  scope_id, revision, prefix_generation, preprocessing_mode,
  raw_conjuncts, prepared_conjuncts,
  context_delta, context_sources, context_has_fp,
  eliminated_definitions, eliminated_variables,
  semantic_root_keys, array_row_keys, clause_mass,
  fragment_summary, dependencies
}
```

Reusable only when scope revision, prefix generation, mode, and semantic-cache
epoch match. **`prepared_conjuncts` in this record is precisely what D2's fix
needs.** Context maps as per-level deltas plus watermarks, not copied wholesale
per check.

### 4. Separate semantic-cache and SAT epochs

Every record containing SAT literals carries a backend epoch; a rebuild
increments it and invalidates literal/activation views while preserving AST-level
preparation, canonical array rows, and FP circuits.

### 5. Keep result lifetime separate from assertion lifetime

Snapshot or pin everything needed to interpret the result **first**, then clamp
assertion cursors, then destroy the snapshot on the next invalidating operation.
The C API's model-survives-the-bracket contract must be preserved.

---

# PART IX — TEST MATRIX FOR SCOPED STATE

Journal/view unit tests: independent consumers advancing at different rates;
append at the current level and revision invalidation; empty push/pop and
multi-level pop; cursor clamping and reset epochs; pop followed by a new scope at
the same depth; identical re-pushed content receiving new scope identity while
still hitting content caches; a consumer failing before commit and retrying.

Solver tests: repeated unchanged checks and extension-only stacks; append, pop,
alternate re-push, identical re-push; same-level late definitions and deeper
definitions that may not rewrite a shallow prepared root; later content
invalidating private elimination and restoring the equation; content seen before
a pop, a later elimination, and an identical re-push screened under a new
semantic/rebuild generation; base growth after engagement and after a rebuild;
`check-sat-assuming` models and failed-assumption granularity; SMT-LIB model
invalidation versus the C API's post-pop model lifetime; the C API's synthetic
base and query-local `NOT query` overlay; lazy arrays across forced rebuild,
active-row withdrawal, and refinement; eager Ackermannization, FP side
conditions, array equality; SAT-backend epoch changes, promotion repair, and
re-materialized roots.

**Added by this review:**

- **A definition eliminated from a piece while a live `ctx` body names the same
  variable** (D1).
- **Re-preparation of a promoted level** (D2) --- the existing
  `unit-promotion.smt2` covers firing, binding, and demotion-on-retraction, but
  never this.
- An `--array-equality` stack pushed, popped, and re-pushed identically, asserting
  that solver variable count does **not** grow (D5).
- A session that engages automatically (not via `--incremental`) exercising each
  of the five check-sat routes.
- `--check-sanity` on every incremental behavioural test that produces a model.

---

# PART X — APPROACHES NOT RECOMMENDED

- Do not replace permanent definitional CNF plus assumptions with SAT-clause
  deletion. STP's multiple external backends make cvc5/Z3-style clause provenance
  a poor fit.
- Do not introduce cvc5's complete dual-context/region/proof infrastructure to
  obtain assertion cursors.
- Do not copy Z3's E-graph deletion and re-internalization machinery.
- Do not backtrack canonical structural encodings merely because their current
  activation is scoped. Preserve the content/activation separation.
- Do not equate a cache with liveness. Canonical array rows, FP rewrites, and
  root encodings may persist while their participation in the current model or
  query must be explicitly scoped.
- Do not promise O(delta) checks where the API or configuration requires all
  active assumptions, a whole-query model check, live-row materialization, or
  extensionality over the complete graph.
- **Do not delete the cheap live-mass estimator** (Part II) --- it is the relief
  ratio's floor, not redundancy.
- **Do not rely on one mechanism to cover another's soundness gap.** D2's four
  incidental rescuers are the argument.

---

# APPENDIX A — WITNESS FILES

Verbatim and self-contained. All four reproduced at tip `278552ce` on both
`build/` and `bd-dbg/`, and each was re-checked against the pre-fix source
after the fixes landed to confirm it still fails there.

**These are now regressions in the tree**, under
`tests/query-files/incremental-tests/`:

| Witness here | Landed as |
|---|---|
| `w6.smt2` | `elimination-context-export.smt2` |
| `w7.smt2` | `elimination-context-export-default-engagement.smt2` |
| `repro3.smt2` | `unit-promotion-repreparation.smt2` |
| `promote7.smt2` | `unit-promotion-repreparation-chained.smt2` |

The landed versions carry lit `RUN`/`CHECK` lines and additional
`--check-sanity` and `--disable-cbitp` configurations; the bodies are the same.
They are kept below because a witness stripped of its harness is the form you
want when bisecting.

## A.1 `w6.smt2` — D1, minimal (needs `--incremental` or `--incremental-auto-engage-at 1`)

True answer **unsat**: `y = ~v` and `y*y = y` force `y ∈ {0,1}`, contradicting
`y > 1`.

```smt2
(set-logic QF_BV)
(declare-fun v () (_ BitVec 8))
(declare-fun p () (_ BitVec 8))
(push 1)
; keeps the node (bvnot v) alive and numbered before y is declared
(assert (bvult (bvnot v) p))
(declare-fun y () (_ BitVec 8))
(assert (= (bvnot v) y))
; y*y = y  =>  y in {0,1}; constant-bit propagation cannot see this
(assert (= (bvmul y y) y))
(declare-fun w1 () (_ BitVec 8))
(declare-fun w2 () (_ BitVec 8))
(declare-fun w3 () (_ BitVec 8))
(declare-fun w4 () (_ BitVec 8))
(declare-fun w5 () (_ BitVec 8))
(declare-fun w6 () (_ BitVec 8))
(declare-fun w7 () (_ BitVec 8))
(declare-fun w8 () (_ BitVec 8))
(declare-fun w9 () (_ BitVec 8))
(declare-fun w10 () (_ BitVec 8))
(assert (= w1 (bvmul v w2)))
(assert (= w3 (bvmul v w4)))
(assert (= w5 (bvmul v w6)))
(assert (= w7 (bvmul v w8)))
(assert (= w9 (bvmul v w10)))
(push 1)
(assert (bvugt y #x01))
(check-sat)
(exit)
```

## A.2 `w7.smt2` — D1 at **default flags**

`w6.smt2` preceded by 34 rounds of `(push 1)(assert (bvult q #xNN))(check-sat)(pop 1)`
(constants `#x03` … `#x24`) so the session crosses the QF_BV engagement ordinal,
then the `w6` body verbatim (35 `check-sat`s in total). Answers `sat` with **no
flags**; batch answers `unsat`.

*Generation:*

```sh
{ printf '(set-logic QF_BV)\n(declare-fun v () (_ BitVec 8))\n'
  printf '(declare-fun p () (_ BitVec 8))\n(declare-fun q () (_ BitVec 8))\n'
  for i in $(seq 3 36); do
    printf '(push 1)\n(assert (bvult q #x%02x))\n(check-sat)\n(pop 1)\n' "$i"
  done
  tail -n +4 w6.smt2   # the w6 body from its first (push 1)
} > w7.smt2
```

## A.3 `repro3.smt2` — D2 at **default flags**

True answer **unsat**. The FP conjunct retires trail reuse on solve 1 (promotion's
precondition); the stable level's BVNOT-headed equation is refused by
`recogniseDefinition` and harvested by `PropagateEqualities`; the `bvmul` nest
keeps CBP from re-deriving the lost fact.

```smt2
(set-logic QF_BVFP)
(declare-fun fx () Float32)
(declare-fun fy () Float32)
(assert (fp.lt fx fy))
(declare-fun p () (_ BitVec 8))
(declare-fun t () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(push 1)
(assert (and (= (bvnot p) (bvmul t (bvmul t t))) (bvult w #x80)))
; fourteen churning rounds on top; the stable level promotes at the ninth
(push 1) (assert (bvult w #x10)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x11)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x12)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x13)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x14)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x15)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x16)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x17)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x18)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x19)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x1a)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x1b)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x1c)) (check-sat) (pop 1)
(push 1) (assert (bvult w #x1d)) (check-sat) (pop 1)
; the level that makes p non-private; its re-prepared form is discarded
(push 1)
(assert (bvult (bvadd p (bvmul t (bvmul t t))) #xff))
(check-sat)
(exit)
```

## A.4 `promote7.smt2` — D2, second witness, isolates the CBP masking

Reproduces under `--incremental --disable-cbitp` (answers `sat`; batch with the
same flags answers `unsat`; `--no-incremental-promote-units` answers `unsat`).
Structure: `QF_BVFP` base `(bvult y #xff)` + `(fp.gt f (_ +zero 8 24))`; stable
level `(= u #x03)`, `(= (bvadd p u) #x07)`, `(bvugt z #x05)`; twelve churn rounds
`(push 1)(assert (bvugt y #x0N))(check-sat)(pop 1)` for `N` in `0`…`b`; then
`(push 1)(assert (bvugt y #x01))(push 1)(assert (= p #xff))(check-sat)`
(13 `check-sat`s in total).

The definition `p = 4` is derivable by `PropagateEqualities` after `u → 3` but not
by `recogniseDefinition` on the raw conjunct.

---

## A.5 `relief-kept-definition-dependency.smt2` — D14, landed as the regression

Unlike A.1--A.4 this witness lives in the suite rather than here, because its
shape is load-bearing: the relief valve must fire on the FINAL check, when the
`u` level is the live one, and that is what fixes the round count at ten. Nine
rounds and eleven both fire elsewhere and answer correctly.

```smt2
(set-logic QF_BV)
(declare-fun u () (_ BitVec 8))
(declare-fun v () (_ BitVec 8))
; ... y1..y10 ...
(assert (= u (bvadd v #x01)))   ; harvested and deleted from the formula
(assert (bvult v #x02))         ; v's only other occurrence
; ten push / (bvugt (bvmul yN yN) #x03) / check-sat / pop rounds
(push 1) (assert (= u #xff)) (check-sat) (pop 1)   ; unsat; the branch said sat
```

Run with `--incremental --incremental-reencode-limit 1`. The limit only makes a
small session reach the valve --- the path it then takes is the default one.

---

# APPENDIX B — FULL FINDING LEDGER

44 findings from the 2026-08-11 review. **Status** is the adversarial verifier's
verdict: `CONFIRMED` = holds essentially as claimed; `PARTLY` = a real but
narrower or differently scoped issue (the *corrected* claim is what to act on);
`REFUTED` = does not hold. **Severity** is post-verification.

| # | Status | Sev | Dimension | Finding | Tracked as |
|---|---|---|---|---|---|
| F1 | CONFIRMED | high | retraction | Unit promotion pins a PREPARED form validated only by raw-conjunction identity | **D2** |
| F2 | CONFIRMED | med | retraction | Steady-state per-check cost is O(stack); privacy predicate makes it O(depth²) | **D4** |
| F3 | PARTLY | low | retraction | Forced-first-solve recovery family --- three special-case entry conditions | Part III.4 |
| F4 | CONFIRMED | low | retraction | `Backtrack.h`: complete scoped-container library, zero production users | **D11** |
| F5 | CONFIRMED | high | preprocessing | Privacy tested on raw stack symbols; levels encoded from ctx-substituted content | **D1** |
| F6 | REFUTED | low | preprocessing | "Six ad-hoc invalidation mechanisms, no shared predicate" | Part II |
| F7 | CONFIRMED | med | preprocessing | Whole-stack rescan per candidate per check; unbounded `symbolsOfCache` | **D4** |
| F8 | REFUTED | none | preprocessing | Exact-stack scoped elimination lacks a freeze check | Part II |
| F9 | PARTLY | low | preprocessing | Trial "must halve" budget measured against a clipped size after sigma0 expansion | **fixed** `96f14b16` |
| F10 | PARTLY | low | cbp | Adoption's shrink gate ignores the pinning facts it obliges | declined, measured |
| F11 | CONFIRMED | med | cbp | `cbpEverFixed` set by a level's own assumed truth; retirement tier unreachable | **D7** |
| F12 | REFUTED | low | cbp | Memo caches four subsystems behind a CBP-shaped key | Part II |
| F13 | PARTLY | low | cbp | Engine/caller/memo triple kept aligned by asserts + repair fallback; two dead fields | **D11** |
| F14 | PARTLY | low | cbp | Session-wide retirement from prefix-scoped, double-counted evidence | **D7b** |
| F15 | PARTLY | med | arrays | Every array encode seeds the whole registry; anchors for every read ever seen | **D8** |
| F16 | PARTLY | low | arrays | No-progress guard counts SAT calls, not new axioms | **fixed** `cd34049d` |
| F17 | PARTLY | low | arrays | Active-read liveness is a refcount shadow; `batchTablesSeeded` dead | **D11** |
| F18 | CONFIRMED | low | arrays | Adapter rebuilds an O(all session symbols) map per call | **D12** |
| F19 | PARTLY | low | arrays | Congruence lemmas "permanent" but charged to a per-stack owner key | **D8b** |
| F20 | CONFIRMED | med | ext/FP | Exact-stack block cache fronted by a non-deterministic, unmemoised pass | **D5** |
| F21 | PARTLY | low | ext/FP | Solver-mode policy in the generic simplifying node factory | **D10** |
| F22 | PARTLY | low | ext/FP | Ext and ordinary rounds mint two deterministic names for the same (array, index) | deferred, reasoned |
| F23 | PARTLY | low | ext/FP | `fragment()` totalises whole levels to compute a boolean, on a memo that does not exist | declined, measured |
| F24 | PARTLY | low | ext/FP | Keep-alive pin set makes name reuse depend on GC, by convention at one call site | Part II |
| F25 | CONFIRMED | high | relief | Whole-base semantic simplification welded to `rebuildEncodings` | **D3** |
| F26 | PARTLY | low | relief | `everAssumedLits` not pruned on the extensionality route | **fixed** `bac4c110` |
| F27 | REFUTED | none | relief | "Two parallel live-mass estimators; delete the cheap one" | Part II |
| F28 | PARTLY | low | relief | `--incremental-profile` changes the relief schedule | **D6** |
| F29 | PARTLY | low | relief | `baseEliminatedDefs` epoch-scoped state cleared behind four early returns | **D3b** |
| F30 | REFUTED | low | frontend | Forced-first recovery gated on CLI provenance, not driver state | Part II |
| F31 | PARTLY | low | frontend | `UserFlags.incremental_solving` conflates request with session state | **D10b** |
| F32 | CONFIRMED | low | frontend | `construct_counterexample_flag` made sticky, disabling the cache shortcut | **D9** |
| F33 | PARTLY | med | frontend | Per-engaged-check work is O(base conjuncts) and O(levels²) | **D4** |
| F34 | CONFIRMED | low | frontend | `canHandle()` is a no-op seam; model readers construct the driver to ask | **D11** |
| F35 | PARTLY | low | sat | `SATSolver` as CaDiCaL option panel; no object owns an epoch's configuration | Tier 4.3 |
| F36 | PARTLY | low | sat | `--incremental-inprobing` silently disables three techniques, gated on one probe | Part III.4 |
| F37 | REFUTED | low | sat | `enableTrailReuse`'s stated precondition does not exist | Part II |
| F38 | PARTLY | low | sat | `suggestPhase` performs CaDiCaL's model-destroying variable declaration | **fixed** `bac4c110` |
| F39 | PARTLY | low | sat | `supportsAssumptions` pairing is a runtime `exit(-1)` invariant | Part II |
| F40 | PARTLY | low | complexity | Backend epoch is not an object: ~28 fields by hand, 4 triggers, 3 predicate copies | Tier 4.3 |
| F41 | CONFIRMED | med | complexity | `--incremental-profile` substitutes a different live-mass computation | **D6** |
| F42 | PARTLY | low | complexity | Three push/pop trail implementations; the tested generic one is unused | **D11** |
| F43 | PARTLY | low | complexity | Four re-implementations of the batch preprocessing prefix; three replay reps | Tier 4.6 |
| F44 | PARTLY | low | complexity | ~20 fitted constants, 8 flags, the most intricate policy undocumented | Part III.4 |

### Findings recorded but not tracked as defects --- all now resolved

All seven were re-checked against the tree and every one still held. Four were
fixed; three were measured and deliberately declined. Details below.

- **F9 --- FIXED (`96f14b16`).** `preparePiece` applies `sigma0` *after* the granularity gate measured
  the pre-sigma0 piece, and then measures with `dagSizeUpTo(out, bigFormulaCap)`,
  which saturates at 20001; so for any piece sigma0 grows past ~20000 nodes,
  `budget` is a fixed 10000-node ceiling rather than half the actual input.
  `harvestSigma0` has **no** inlining cap, unlike `harvestPushed`'s
  `defInlineCap`. Fix: measure `before` unclipped, and decide deliberately whether
  base definitions deserve the same inline cap.
- **F10 --- DECLINED, measured.** `cbpAdopt`'s shrink gate measures only the rewritten conjunct, not
  the pinning facts it obliges, and facts are never discharged into each other the
  way the batch pass does. Fix: build one `fromTo` from the collected domains,
  emit each fact as `EQ(replaceChildren(domain, fromTo), k)`, drop facts folding
  to TRUE, stop the walk at an emitted domain, and include surviving facts' mass
  in the gate.
- **F16 --- FIXED (`cd34049d`).** the no-progress guard fires on "no SAT call this round", which is
  strictly narrower than "no progress". Because the candidate-pair set is
  recomputed identically each round and a round exiting UNDECIDED has already put
  every pair's axiom into the solver, the loop is provably either one round or
  unbounded, re-encoding duplicate axioms each time. Fix: compare
  `submittedClauses()` across the round, or memoise emitted pairs in
  `applyAxiomsToSolver`.
- **F22 --- DEFERRED, deliberately.** in a session alternating extensionality and ordinary array rounds, a
  SYMBOL-rooted read is abstracted twice (`@ext_read_k<A>_k<i>` and
  `@array_A_k<i>`) sharing nothing. Fix: one deterministic name keyed on
  `(array, index)` in both routes; the ext spelling generalises.
- **F23 --- DECLINED, measured; comment corrected.** `fragment()` runs a full `FpTotalise::topLevel` solely to derive the
  `f.arrays` boolean, and the justifying comment is wrong: `FpTotalise` has no
  root-level input→output memo. Fix: decide `f.arrays` syntactically
  (`FP_TO_UBV`/`FP_TO_SBV` or an FP-indexed array access), and give `FpTotalise` a
  root-level memo.
- **F26 --- FIXED (`bac4c110`).** `exactStackCheckSat`'s array-equality return bypasses the sole
  `retireStaleActivation()` call, so hint aging never runs in an all-ext session.
  Fix: move the call to just after `decideBVA`, which both routes pass.
- **F38 --- FIXED (`bac4c110`).** drop the unnecessary `declareNewVariables()` from
  `Cadical::suggestPhase`; the early return already guards undeclared variables,
  and the call can leave CaDiCaL's SATISFIED state under `--cadical-factor`.


#### Why three were declined

**F10 (adoption's shrink gate ignores its pinning facts).** Implemented and
reverted. Weighing the facts' DAG mass in the gate refused an adoption that
`cbp-overlapping-protection-roots.smt2` pins, and that refusal was wrong: a
fact's cone is a shared subgraph referenced by identity, and the work on D8
established that re-emitting such a cone costs no clauses, because the
equations are interned and the AIG is strashed. DAG size is simply not a proxy
for encoding cost here. The finding's own verification had already narrowed
the consequence to "a small constant overhead"; the corrected gate over-counts
it. Discharging facts into each other and stopping the walk at an emitted
domain remain available as tidiness, with no measured return.

**F22 (two deterministic names for the same read).** Not attempted. Unifying
them means making the ordinary route key on the array NODE and share the
extensionality route's spelling, so the two routes produce the same
abstraction variable. That is sound in principle -- both stand for the same
read -- but it entangles a solve-local extensionality registry with the
persistent lazy one and with the permanent congruence axioms over it, and the
`--ackermanize` path takes a different `.symbol` again. The payoff is sharing
in a session that interleaves equality and ordinary array rounds. That is not
a change to make without the array-equality corpus to run it against; it is
recorded for whoever has one.

**F23 (`fragment()` totalises a whole level to compute a boolean).** The
fix with no semantic risk -- a root-level memo in `FpTotalise` -- was built and
measured neutral on a 200-conjunct floating-point session (23.6 s against
23.6 s, interleaved), because SAT time dominates anything it could save. It
was dropped rather than carry a per-root cache holding a copy of each call's
array-equality rewrites for no return. Deciding `f.arrays` syntactically
instead would remove the totalisation altogether, but that is the judgement
the current code exists to get right -- classify on the raw conjunct and a
read introduced by totalisation reaches the blaster with refinement skipped --
so it is not worth risking for a cost that does not show. The misleading
comment claiming the second call is a cache hit is corrected in place.

---

# APPENDIX C — REPRODUCTION COMMAND REFERENCE

Binaries used: `build/stp` (Release + assertions) and `bd-dbg/stp`
(RelWithDebInfo + assertions). `libstp.so` is linked **dynamically** --- a saved
binary alone is not an A/B arm; use a separate worktree build.

```sh
# --- D1: privacy over the raw stack -------------------------------------
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2 --incremental-auto-engage-at 0 w6.smt2   # unsat  (correct)
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2 --incremental                   w6.smt2   # sat    (WRONG)
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2                                 w7.smt2   # sat    (WRONG, default flags)
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2 --incremental-auto-engage-at 0 w7.smt2   # unsat  (correct)
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2 --incremental --check-sanity    w6.smt2   # STP Error: model does not satisfy an asserted formula

# --- D2: promotion pins an unvalidated prepared form ---------------------
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2                                  repro3.smt2  # sat   (WRONG, default flags)
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2 --no-incremental-promote-units   repro3.smt2  # unsat (correct)
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2 --incremental-auto-engage-at 0   repro3.smt2  # unsat (correct)
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2 --check-sanity                   repro3.smt2  # STP Error
# second witness, isolates the CBP masking
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2 --incremental --disable-cbitp    promote7.smt2 # sat   (WRONG)
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2 --incremental --disable-cbitp \
                                    --no-incremental-promote-units             promote7.smt2 # unsat (correct)

# --- Which mechanism is masking a defect? --------------------------------
#   --disable-cbitp                    removes constant-bit propagation
#   --no-incremental-promote-units     removes promotion
#   --incremental-auto-engage-at 0     batch reference (ground truth)
#   --check-sanity                     validates the model against raw assertions

# --- D4 / cost profiling -------------------------------------------------
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2 --incremental --incremental-profile FILE 2>&1 \
  | grep '^Incremental profile total'
#   read: total-us, semantic-us, prepare-us, sat-us, prepare-hits, stable-prefix

# --- Driver engagement / policy tracing ---------------------------------
LD_LIBRARY_PATH=build/lib build/stp --SMTLIB2 --incremental -s FILE 2>&1 \
  | grep -E 'promoted|trail reuse|inprobing|cbp retired|re-encoded'
```

**Traps** (carried from the branch protocol --- all still current):

- zsh does **not** word-split unquoted `$VAR`; inline flags explicitly.
- Sequential timings swing ±30--50 % with load and thermals. Only interleaved
  quiet-box A/B counts --- and your own parallel jobs are the load.
- The newton/sine/square QF_BVFP family flips 0.98 s ↔ timeout on identical code.
  Never diagnose from it.
- CaDiCaL `set()` after the first clause is a fatal abort; configuration-window
  options only at construction or rebuild.
- `grep -c` exits 1 on zero matches, breaking `&&` chains after successful builds.
- The Bash tool's cwd sticks across calls: always `make -C <dir>`.

---

# APPENDIX D — HISTORICAL EVIDENCE (2026-08-07/08 closeout)

*(Retained verbatim in substance. All of it predates the discovery of D1 and D2
and must be read with that in mind: the campaign compared answer streams only,
which is precisely why both defects survived it.)*

## Frozen closeout reconciliation

Master `34f69be1989910fd053008715de4b65c095fd770` vs candidate
`e5a26c30f83b2cd9cc0ccb274b62f210865023cd` (the `ee8685bb` implementation plus
documentation). Frozen Release builds, CaDiCaL 3.0.1, FP, shared libraries,
system allocator, `--array-equality` on both arms.

| | |
|---|---|
| master exe SHA-256 | `6f03a9edbbbfe6db2918ca9a36e6f2fd3903f5061e6a520db0c489f19212517a` |
| candidate exe SHA-256 | `2c9186d98aa55df055d751e3ea3b40d7f3d13f248b19789fea1ab57d2bbdb8ce` |
| master `libstp` | `0f063a88125c10070b403e2d107e25b9b0cb9177c8aa22b95decff6bc4553a6b` |
| candidate `libstp` | `84a36b4f447ab47ca97f2ea60b03cfe5628a65cef9f722b4d2a9bef7ab17e03f` |
| corpus | 22,999 unique files, 20,308,257,767 bytes |
| corpus manifest SHA-256 | `cd1310ebac50f4d35c837df0a01e6f8ffe020c3e6df1a8f8b03d13a9bbf784d7` |
| content ledger SHA-256 | `7c0fca20fc75e5cd7506b0e225621d17aa20dc98e087b28f159f0dd40f4d98db` |

One run per file at 30 s; 518 files selected for an authoritative 120 s rerun.
Coverage exact: all 22,999 `(file, run)` pairs and all 518 reruns present. **No
`DISAGREEMENT` observed in either phase.** After replacement, 22,765 `FULL_OK`
and 234 `PREFIX_ONLY_INCONCLUSIVE` (21 shared `exit-11`, 155 shared timeouts, 17
master-ok/candidate-timeout, 41 master-timeout/candidate-ok). Effective streams
retained 607,747 master and 607,180 candidate answers of the structural 621,942
per arm.

> The 234 incomplete rows are **not** agreements. Only the prefixes both
> processes produced agreed.

`QF_FP/schanda/spark/precise.smt2` --- the oracle that exposed the
CBP/private-definition bug in the *first* campaign attempt --- was clean in the
frozen campaign (both arms `unsat` in all four scopes).

Configured suites at `ee8685bb`: CaDiCaL + FP 116/116; MiniSat + FP 115/115;
MiniSat without FP 87/87.

## Historical performance figures (contextual only)

22,999 files: 7,520 wins ≥2×, 258 losses ≥5×, median 0.086 s vs master 0.164 s.
Industrial_Control_C specimen ≥90 s → 2.6 s (master 1.5 s), 164/164 answers agree;
Automotive stragglers ~12--18 s → ~0.8 s.

Measurements that shaped the design: full active-read table rebuild was 42 % of a
1000-query KLEE session before differential seeding; a repeated capped DAG-size
walk was 30 % of the post-CBP specimen before per-node memoisation; fresh-per-call
CBP took 9.7 s on the Industrial specimen against 2.6 s with prefix persistence;
engaging on the second solve made two-check files the loss tail, and the third
restored parity.

## Invariants established by the development history

Assumption literals must pass through any SAT-backend variable translation. A
definition or CBP-fed assertion must never erase its own constraint. A
transformation based on scoped facts must retain an asserted justification. Every
symbol in a CBP fact appended after preparation must participate in
definition-privacy analysis *before* that preparation. Memoized raw-content
screening is not a durable privacy proof --- a prepared cache hit must revalidate
against the live stack. A cached encoding is permanent, but the assertion
selecting it is scoped. Array abstractions may be structurally permanent while
their participation in model/refinement state is scoped. Every active array user
must carry its row's index binding. Stale model substitutions and popped rows must
be withdrawn. Conflicting CBP feeds must participate in prefix divergence. A
refinement round rejecting a model without a new lemma indicates an
encoding/model inconsistency. Generated extensionality names keyed by nodes
require the node spine kept alive. Semantic caches may survive a SAT rebuild; SAT
literals may not.

> **This review adds one more:** *a predicate that governs what is encoded must be
> computed over the representation that is encoded.* D1 and D2 are the two places
> that invariant is currently violated.

## Prior roadmap status (Phase 0--2 complete; unchanged)

1. ✅ Active-read state across rebuild and eager cache hits (`9eb8e407`, `02607540`)
2. ✅ Retained/live/peak clause accounting incl. extensionality (`db4aab0a`,
   `c604e923`, `45fe552b`, `8e421b89`, `9cb7b34b`)
3. ✅ Master integrated through `34f69be1` (`4b60b401`)
4. ✅ Documentation reconciled (`30680576`, `40acb2c4`, `239c4402`, `f1e55c2c`)
5. ✅ CBP-fact/private-definition ordering + stale prepared-cache privacy
   (`56de220c`, `ee8685bb`)
6. ✅ Frozen 22,999-file reconciliation
7. ⏸ Three-run timing campaign --- **moot until D1/D2 land**

Phase 1 (instrumentation, `ded8d07e`) and Phase 2 (CBP undo trail, `8f37f17b`,
`842b03ef`) are complete. Phases 3--6 (journal, cursors, preprocessing state,
array liveness, whole-query procedures) are superseded in sequencing by
[Part V](#part-v--work-queue) items 4 and 8, which capture most of the value at a
fraction of the cost.

## Why the CBP undo trail preceded the journal (retained rationale)

The journal would say which levels are new or popped but would not restore the
engine's `FixedBits`. Implementing it first would have been a broad refactor
leaving the one measured reconstruction bottleneck intact. The implemented trail
uses the existing LCP synchronization: begin a level transaction before feeding,
commit only after feed/rewrite/memo/fact writes and `cbpFinishLevel()`; on
divergence roll back to the LCP; feed only the changed suffix; later replace LCP
polling with journal notifications without changing the engine contract.

⚠ **Do not resurrect the old prototype unchanged.** Commit `d61d2c04` contains an
earlier CBP undo-log experiment; `8a0d4a30` removed its integration after real
answer disagreements. The root cause was circular preprocessing (assuming
individual pieces, simplifying them under their own truth, losing the original
constraint), not that rollback is impossible. Use it as a catalogue of mechanics,
not as an implementation.

---

# APPENDIX E — DOCUMENT HISTORY

| Date | Author/commit | Change |
|---|---|---|
| 2026-08-07 | review of branch `0ff90033` vs master `fa211128` | Original architecture review: reference-solver study, state-lifetime audit, scoped-state design, phased roadmap |
| 2026-08-08 | closeout update at `f1e55c2c` (solver tip `ee8685bb`) | Instrumentation and CBP-rollback results; accounting/privacy repairs; frozen 22,999-file reconciliation |
| **2026-08-11** | **second review at tip `278552ce`** | **Restructured. Added: two reproduced soundness defects (D1, D2) with witnesses and fixes; ten further tracked defects; a verified-correct / do-not-re-chase register; the 44-finding ledger; cost measurements; a re-ordered work queue. Prior content retained in Parts VI--X and Appendix D.** |
| **2026-08-11** (same day, later) | **master `d47f6b57` rebuilt at the merge base** | **Added [Validation against master](#validation-against-master): all four witnesses answer `unsat` on master; per-defect master-exposure analysis; D10 reproduced as a divergence from master; D9 source-verified; D8/D5 shown to depend on branch-only persistence; 72-file corpus differential (71 identical, 1 = a feature master lacks). Status board gained an "In master?" column.** |
| **2026-08-11** (reassessment) | after `00ea5c1e` | Added [D13](#d13--conservatism-d1s-fix-refuses-eliminations-the-context-re-join-would-have-covered), the measured conservatism D1's fix introduced (4 of 93 eliminations corpus-wide, 2 genuine, in one file), with the single-transaction fix and an explicit warning against the two-site prediction that caused D1. Work queue re-ordered into tiers: the ordering principle changed once no known soundness defect remained, from "fix the wrong answers" to "find the next one, then pay down cost". |
| **2026-08-11** (fixes) | `e1229764`, `926bf48f`, and the regression/harness commit | **D1 and D2 fixed**; four regressions landed, each verified to fail against the pre-fix source before being kept; paired campaign mode now validates the candidate's models by default. Status board, work queue and Appendix A updated. No known soundness defect remains. |
| **2026-08-11** (same day, later still) | **cross-checked with Bitwuzla, cvc5 and Z3** | **The four witnesses' expected answers no longer rest on STP alone: Bitwuzla `0.9.1-dev`, cvc5 `1.3.5.dev` and Z3 `5.0.0` agree with STP master on all 64 answers across the four files; the branch matches 60/64 and diverges on the final check of each. Recorded in Validation §1.** |

| **2026-08-11** (untracked-findings pass) | `cd34049d`, `bac4c110`, `96f14b16`, `933a3b4b` | The seven ledger rows that were recorded and never tracked are closed: F16, F26, F38 and F9 fixed; F10 (adoption shrink gate) and F23 (`FpTotalise` root memo) built, measured and reverted --- the first because counting a pinning fact's DAG mass over-counts shared interned cones and refused an adoption the corpus pins, the second because it measured neutral; F22 deferred with its reason. |
| **2026-08-11** (cross-check) | audit of this document against the tree | Found that two rows marked FIXED were fixed only at their headline, and that three ledger rows pointed at a "Part V.9" that does not exist. Added D7b/D8b tracking, [Tier 4.6](#46-findings-the-sweep-recorded-and-never-queued) to own the eight items that had no home, and corrected the status-board paragraph, nine stale work-queue headings, the Tier 4.4 test-suite figures and an `F36` cited as `D36`. |
| **2026-08-11** (D7b/D8b) | `e438bbba`, `95014cd7` | **D7b fixed**: the CBP feed cap is charged what a level adds rather than the sum of level DAG sizes, the retention invariant is asserted, and a capacity refusal is released when the stack falls back below it; two regressions, both confirmed to fail against the old accounting, plus corrected counters in `incremental-profile.smt2`. **D8b closed, declined with measurement**: reproduced as one spurious relief rebuild and 646 of 6800 lemmas re-derived, with no time difference, at a valve setting 125x tighter than the default; the available remedy is the extreme the design rejected, and the right one would recreate D6. |

| **2026-08-11** (work-queue sweep) | `60e83767`, `4ce441a1`, `0e12ca21`, `9872ba2c`, `497bb966`, `11c2f65d`, `5c050d99`, `13565d23` | Tier 1.2 seam landed and the ordinal re-measured (unchanged, deliberately --- the synthetic sweep says session SHAPE, not length, is the discriminator). D3's relief-path residue budgeted. Tier 4.4 done: automatic-engagement coverage 9 -> 43 files, `--check-sanity` 23 -> 33. Backend configuration window made a checked invariant; the thrice-written inprobing predicate consolidated; the `SessionShape` and `BackendEpoch` value types declined with reasons. Four Tier 4.6 orphans closed (F36, F44, F24, F7). |
| **2026-08-11** (D14) | `87a77ac2` | **A third soundness defect**, found by adversarially challenging the F43 *tidiness* row rather than by looking for one. The relief rebuild keeps a definition for an untouchable variable while dropping the last constraint on a variable that definition mentions, producing a base strictly weaker than the one it replaces. Reproduced identically at `933a3b4b`, so pre-existing rather than introduced by the sweep above. Fixed by closing the untouchable set under the substitution map's right-hand sides; regression landed on both engagement paths and verified to fail without it. The status board's "no known soundness defect remains" has now been wrong once, and says so. |

**Working-tree note at time of writing:** the branch tip is local and unpushed.
Untracked in the worktree: `HANDOVER.md`, `NEXT-SESSION-PROMPT.md`, build
directories `bd-dbg/`, `bd-mid/`, `bd-pretoday/`, and scratch queries
`moo.smt2`, `fp_soundness_bug.smt2`, `reduced-Problem101.smt2`. `lib/extlib-abc`
shows as modified.
