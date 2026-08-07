# Incremental solving in STP: architecture review and roadmap

Status: 2026-08-07. The architectural comparison originally read STP branch
`incremental-solving` at `0ff900332698c36f206476abfaf4f79d4678325a`, local
`master` at `fa211128a39c9412baf7dcde4e85f367ab7b687a`, and the following
reference checkouts. The implementation and closeout status is updated through
branch `9cb7b34bd0a83713a3a01f8be9e964f59d983df1`, which contains the merge of
`master` at `34f69be1989910fd053008715de4b65c095fd770`.

| Solver | Revision read |
|---|---|
| Bitwuzla | `e92a4c517bc4aa9c65551947f7bffe9a57236151` |
| cvc5 | `e8c0387caeceaf631e0d3b114373b1bc7942334b` |
| Z3 | `4af3410d104ad291437275ad1553d2b82b152727` |

Reference-solver paths and line numbers, and STP passages explicitly labelled
as the original review, refer to those original revisions; implementation
status without that qualification refers to `9cb7b34b`. Line numbers may have
drifted as the branch was closed out. This is a maintainer-facing design
record. `docs/incremental-solving.rst` remains the user-facing description of
the implemented feature.

## Executive conclusions

The branch has already implemented the most important low-level incremental
solver architecture correctly:

- one normally persistent SAT solver, bit-blaster, AIG, and definitional CNF
  encoding, with explicit backend rebuild epochs;
- frontend-appropriate permanent or retractable roots supplied through units,
  activations, and SAT assumptions;
- learned-clause and structural-encoding reuse across checks and pops;
- persistent, canonical theory encodings for arrays and floating point;
- model, failed-assumption, C API, and whole-array-equality support;
- a relief valve for accumulated dead encoding.

That is the durable core of the branch and should not be replaced.

The main architectural difference from Bitwuzla, cvc5, and Z3 is now above the
SAT boundary. All three reference solvers have first-class scoped semantic
state and explicit frontiers between raw and processed assertions. Bitwuzla
exposes separate stage-ordered consumer views; Z3 uses `qhead`/formula-head
boundaries at its wrapper and simplifier-state layers; cvc5 advances a
context-dependent driver frontier after committing a delta through its
pipeline. STP instead receives the whole active assertion stack as one
conjunction per level. It reconstructs much of its live preprocessing state on
each check. Content caches make the expensive transformations reusable, but the
driver still rebuilds definition contexts, active preparation records, roots,
read ownership, stack summaries, and related bookkeeping.

This explains an apparent contradiction in the branch:

- its permanent SAT/AIG design is close to Bitwuzla and is already highly
  effective;
- its word-level incremental machinery increasingly maintains local substitutes
  for a missing common scoped-state architecture: CBP prefix memos, active-read
  reference counts, promotion stability, elimination invalidation, model-seed
  withdrawal, and rebuild repair.

The major long-term gap is therefore not another SAT trick. It is the absence
of a first-class scoped semantic-state architecture and per-stage assertion
cursors. The unused `include/stp/Incremental/Backtrack.h`, repeated
reconstruction of active state, and later additions such as prefix CBP,
active-read refcounts, promotion state, and rebuild repair logic are symptoms
of that choice.

That does **not** make a general scoped-state refactor the immediate next patch.
The active-read rebuild risk has been fixed, semantic reconstruction has been
instrumented, the measured CBP whole-prefix re-feed has been replaced by a
differential-tested rollback trail, retained/extensionality clause accounting
has been repaired, and current master has been merged (see the implementation
updates below). The remaining branch-close gate is the owed quiet-box full
campaign. After that, introduce a versioned assertion journal and independent
cursors only when profiles or recurring lifetime bugs justify the migration of
another semantic consumer.

The remaining RTOS small-file loss class appears to be engagement/cold-start
overhead. Scoped semantic state is not presently supported as its remedy.

## Implementation update: instrumentation and CBP rollback

The recommendation to instrument first and then implement a narrow CBP trail
has now been carried out:

- `ded8d07e` added the opt-in per-check/session profiler, including stable
  prefixes, fresh and re-fed CBP work, semantic construction, preparation,
  encoding, array/refinement work, and SAT time;
- `8f37f17b` added first-write engine checkpoints for fixed-bit state,
  conflicts, multiplication state, and dependency-graph additions;
- `842b03ef` added matching caller checkpoints for substitutions, fed
  conjuncts, emitted facts, feed mass, array presence, and conflict state,
  and changed divergence handling to roll back to the existing LCP and feed
  only the replacement suffix;
- `--incremental-cbp-reset` preserves the old reset-and-prefix-re-feed path as
  a differential oracle and conservative fallback; and
- rewrite memos now record a pinning fact's substitution-domain node
  explicitly. The old attempt to recover it from the assertion shape was
  ambiguous for a positive Boolean fact whose node was itself an equality.

The implementation deliberately leaves the successful persistent SAT/AIG
architecture and the LCP-based stack interface intact. It is a narrow scoped
state transaction around the one measured reconstruction bottleneck, not the
general assertion-journal refactor.

### Measured result

Release measurements compared the default rollback path with the forced-reset
oracle in the same binary. The runs used `--incremental`; profile runs also
used `--incremental-profile`. The Release build enabled CaDiCaL, floating
point, and mimalloc and did not enable LibBF. Wall values are alternating-order
means of four pairs for Industrial, `1ccb771c`, and RTOS, ten for `f84c6e97`,
and three for each Automotive file. Answer streams matched in every pair.

| Workload | Checks | Default rollback wall time | Forced reset wall time | Result |
|---|---:|---:|---:|---|
| Industrial `d58a9331` | 164 | 2.120 s | 2.728 s | 22% faster; mean RSS 29.6 vs 33.1 MB |
| Robotics `f84c6e97` | 20 | 0.081 s | 0.083 s | neutral |
| Aerospace `1ccb771c` | 118 | 1.810 s | 1.843 s | 2% faster |
| RTOS `80f6692b` | 27 | 1.002 s | 1.005 s | neutral, as predicted |
| Automotive `8c5a7a8f` | 42 | 0.750 s | 0.767 s | neutral-to-positive |
| Automotive `7256a4bd` | 42 | 0.750 s | 0.760 s | neutral |
| Automotive `115a02fc` | 42 | 0.727 s | 0.730 s | neutral |

The single-check `Problem18_label55` canary has no divergence and showed parity,
as expected: the rollback path is inert there.

The Industrial profile explains the wall-time result. Nineteen rollbacks took
0.211 ms in total and removed all 1,989 surviving-prefix re-feeds (1,455,220
bounded DAG nodes). CBP time fell from 829.0 ms to 228.5 ms. On `1ccb771c`, 218
re-fed levels disappeared and CBP time fell from 161.2 ms to 88.6 ms. RTOS had
only 86 re-fed nodes under the oracle, so removing them could not materially
change its roughly one-second run time.

Correctness validation for the CBP rollback checkpoint included four engine
unit tests; the complete configured suite at that checkpoint; all 49
then-existing incremental SMT-LIB regression files;
trail-versus-reset answer comparison both normally and under `--check-sanity`;
conflict/pop/replacement, multi-level rollback, caller-substitution retraction,
and cross-level array-fold regressions; and the Industrial specimen's
164-answer stream. The broader campaign remains a branch-close obligation.

The result supports keeping the trail. The next architectural step remains an
assertion journal with independent consumer cursors, but it is now a
maintainability/lifetime project that should proceed only after the remaining
branch-close work and further profiling. It should not be presented as an RTOS
cold-start optimization.

## Implementation update: integration, accounting, model repair, and harness

The other concrete closeout work is now implemented through `9cb7b34b`:

- merge `4b60b401` integrates `master` through `34f69be1`, including the
  backend-neutral SAT literal/factory work and optional-MiniSat build shape;
- `db4aab0a` makes clause submission a non-virtual `SATSolver` facade operation
  and counts every submission before delegating to a backend, so generic theory
  code cannot bypass the count;
- `c604e923` replaces the relief valve's partial structural proxy with exact
  current-epoch retained submissions plus explicit live ownership, and gives
  the profile separate lifetime, refinement, retained, live, and peak-live
  views;
- `45fe552b` adds forced extensionality churn and monotonic-live regressions;
- `02607540` restores active eager-Ackermann read observations before a model
  can be constructed on an all-cache-hit round, with deferred-model and sanity
  regressions;
- `8e421b89` checks the absence of a spurious extensionality rebuild at every
  live-growth round, rather than only at the first one;
- `9cb7b34b` extends lazy exact live-cone repair to the union of all ordinary
  and extensionality roots, with an ordinary shared-cone regression; and
- `30680576` repairs the paired campaign harness and adds fake-solver tests for
  its sequence, timeout, order, resume, provenance, and revalidation behavior.

### Retained total versus lifetime submissions

`SATSolver::submittedClauses()` is the exact number of input-clause submissions
to the current backend instance. It counts at the common interface boundary,
including a submission that discovers an already-inconsistent formula, rather
than relying on backend statistics that may omit simplified clauses or not
exist. This is the relief valve's retained total for the current backend epoch.

Before a backend rebuild, the driver adds that epoch's count to
`retiredClauseSubmissions`. The profile's historical `driver-clauses` name now
means all clause submissions during the current check, and the session record
is their driver-lifetime cumulative total across rebuilds. The separately
reported `refinement-clauses` is a subset of that total: clauses emitted by
lazy-array or extensionality checking/refinement. It must not be added to
`driver-clauses` again. `retained-clauses`, by contrast, resets with the backend
and reports only the current epoch.

### Live and peak ownership

The retained total is exact; live mass is a policy ownership model used as the
relief ratio's denominator. Its inexpensive value is provisional, while a lazy
exact structural-union guard prevents that value from authorizing a rebuild:

- structural submission deltas are charged to the deterministic formula key
  whose encoding first emitted them, and that key also retains its actual AIG
  root for the exact union;
- base, restored-base, and promoted roots are recorded as permanent structural
  roots, with their unit clauses counted separately for the epoch;
- activation implication clauses are live only while that activation literal
  appears in the current assumptions;
- retiring an activation forgets its live ownership, while its implication
  clauses and false pin remain retained dead mass; and
- theory-valid array/refinement lemmas are owner-keyed to the deterministic
  active conjunction or extensionality block that caused them to be emitted.

Owner-keying the theory lemmas is intentional. Calling every old lemma live
would hide refinement-heavy dead growth; calling every permanent lemma dead
would rebuild repeatedly on an unchanged live query. Every reported live value
is capped by the exact retained total, and the current value and epoch
high-water mark are exposed as `live-clauses` and `peak-live-clauses`.

A formula key's newly submitted structural delta can be much smaller than its
current live cone whenever its AIG root reuses nodes first encoded for an
earlier, now-popped key. This was first repaired for whole-array equality, but
an independent ordinary-path regression then demonstrated the same failure: a
composite ordinary root owned only nine newly submitted clauses while retaining
roughly 2,900 clauses of multiplier cones introduced by prior roots. The cheap
denominator could therefore authorize a false rebuild even though the whole
cone remained live.

Commit `9cb7b34b` records the actual AIG root for every encoded formula key.
The exact structural measurement is the unique union reachable from the
backend epoch's permanent roots and the current ordinary roots, or the current
extensionality-block root: three clauses per AND plus one unit if the union
reaches the shared true node. Permanent root units, active activation
implications, and owner-keyed refinement mass are exact non-structural terms
added separately. Taking a union both preserves sharing and prevents shared
clauses from being counted twice.

The normal path avoids this walk until it can affect policy. Below the
re-encoding variable floor it neither collects an ordinary root vector nor
walks a cone. Above the floor, each solve coalesces the previous state into one
latest pending snapshot: normalized current roots, the permanent-root prefix
length, and non-structural mass. Only if the cheap retained/peak ratio would
otherwise authorize relief does the next check pay for one exact union walk,
repair the historical peak, and test the ratio again. Retaining only the newest
snapshot avoids quadratic memory on a growing stack, while popped historical
stacks intentionally cease to protect dead clauses. Opt-in profiling computes
the exact current union on every solve instead.

The forced-churn regression proves extensionality-only dead growth can fire the
valve and remain sound across the rebuild. The strengthened monotonic-live
regression checks every extensionality growth round for a false rebuild, and
the ordinary shared-cone regression covers the analogous non-array case.
Profile coverage also checks that extensionality and refinement submissions
appear in the total, that refinement is a subset, and that the current live
estimate does not exceed the retained total.

Two accounting limitations are deliberate or theoretical. Refinement clauses
are charged to the deterministic owner that emitted them; a lemma useful to a
different live owner can therefore be omitted from live mass and cause an
unnecessary rebuild, but rebuilding merely re-derives any needed theory facts
and does not change satisfiability. The common exact-submission counter is a
plain `uint64_t` increment and would wrap after `2^64` submissions; the derived
mass additions saturate, but a session that reaches the interface-counter limit
is outside any practical workload.

### Eager-Ackermann model state on cache hits

`Cpp_interface::resetSolver()` clears the batch `ArrayTransformer` tables before
every solve. Lazy-array refinement calls `seedActiveReads()`, but eager
Ackermannisation has no refinement loop that would do so. Consequently, an
unchanged second solve could reuse every correct SAT encoding while leaving no
active rows from which deferred `get-model`/`get-value` or immediate sanity
checking could reconstruct the source array; the reported array cells could be
missing or arbitrary despite a correct SAT answer.

Commit `02607540` rematerializes the active read observations after a
satisfiable eager-array solve whenever a model can be observed. This is model
state only: it neither emits clauses nor redoes Ackermannisation. The new
`ackermanize-model-cache.smt2` requests both models around an entirely
cache-backed second solve, while `ackermanize-rounds.smt2` now also runs under
`--check-sanity`.

### Repaired campaign harness

Paired mode now takes explicit solver A and B paths and records every
`sat`/`unsat`/`unknown` answer, including the answer prefix available when a
process times out. Its verdicts have narrow meanings:

- `FULL_OK`: both arms completed successfully with identical full sequences;
- `PREFIX_ONLY_INCONCLUSIVE`: the common prefix agrees but at least one arm did
  not complete successfully, which is not a correctness success; and
- `DISAGREEMENT`: an answer in the common prefix differs, or two completed arms
  produced sequences of different lengths.

Execution order is deterministically balanced AB/BA by file and run. Complete
pairs are flushed as they finish; `--resume` accepts them only when the
sidecar manifest and identity metadata still match. Sorted manifests and
deterministic `--shard-index`/`--shard-count` selection make independent chunks
reproducible. Each arm's metadata includes its binary SHA-256, arguments,
embedded STP SHA and compilation options, `ldd` output, and hashes of linked
`libstp` libraries; the harness also checks that the arm did not change during
the run. Non-full results, timeouts, and large timing ratios are selected for a
longer revalidation phase, which may be explicitly deferred.

The harness is ready; no new whole-corpus result is claimed in this document.
The full quiet-machine campaign remains outstanding.

## Scope and evidence

The original review compared branch `0ff90033` and then-local master from merge
base `f66852e1fe950e66acd50fb7b3ae12b0023a82ad`. Current branch `9cb7b34b`
contains master `34f69be1` through merge `4b60b401`; there is no unmerged
master-side delta in this reviewed snapshot. Historical file/line/count claims
from the initial audit should not be projected onto the larger current
implementation.

The recorded performance figures in this document come from `HANDOVER.md` and
the branch history. Neither the initial architecture review nor this
documentation update repeated the 22,999-file campaign against the current
tip. Focused and configured-suite checks at the implementation checkpoints do
not replace that campaign.

At the `9cb7b34b` closeout tip, the complete configured RelWithDebInfo suites
passed with CaDiCaL plus floating point (115/115), MiniSat plus floating point
(114/114), and MiniSat without floating point (86/86). These backend/build
matrices validate the merged implementation and regressions; they are not a
substitute for the external 22,999-file paired campaign.

The original pre-implementation investigation is preserved in commit
`f5235e54` (`Incremental solving: architecture review and phased plan`). It was
removed after its initial phases were implemented by `5244299a`. This document
is a post-implementation review: it records where the implementation followed
that design, where it deliberately diverged, and what the resulting next steps
are.

## Master baseline

Master is level-aware only at the frontend.

- `STPMgr::_asserts` stores one `ASTVec` per push level
  (`include/stp/STPManager/STPManager.h:158-166`).
- `Cpp_interface` keeps declaration frames and a result-cache entry at the same
  depth (`lib/Interface/cpp_interface.cpp:43-46`).
- The result cache implements useful monotonicity: UNSAT survives pushes, SAT
  propagates to shallower levels, and an unchanged stack can sometimes be
  answered without another solve.

For an uncached check, master is deliberately single-shot:

- each level is collapsed to a conjunction and the active levels are conjoined;
- `TopLevelSTP` creates a fresh floating-point context and SAT solver;
- the complete whole-formula simplification, array, bit-blast, CNF, and
  refinement pipeline runs;
- the SAT solver and query-local encoding machinery are discarded.

The batch pipeline consequently gets its full global preprocessing power, but
it retains no preprocessing products, structural encodings, theory lemmas, SAT
trail, or learned clauses across real checks. Master re-establishes pop
soundness by retaining almost nothing.

This baseline is still useful. A single large all-new query can profit more
from whole-formula preprocessing than from persistence that has not yet had a
chance to reuse anything. The branch's two-driver policy exists to preserve
that property.

## What this branch implemented

### Driver selection

The branch adds a persistent driver beside the batch path. Absent explicit
`--incremental` forcing, an SMT-LIB session without an explicit or internal
push remains entirely on the batch path;
`check-sat-assuming` creates an internal temporary scope and therefore counts as
a push for this purpose. By default, a pushed session runs its first two real
solves through the batch pipeline and engages the incremental driver on the
third; `--incremental` forces engagement from the first solve
(`lib/Interface/cpp_interface.cpp:636-649,702-716`). The same solve threshold
is applied by the C API after `vc_push` enables incremental mode.

This is a performance policy, not an incremental-semantics requirement. Moving
engagement from the second to the third solve in `cf911af5` removed two-check
sessions from the measured loss tail: the last solve in such a session cannot
repay the cost of constructing a persistent encoding.

One remaining detail deserves an explicit decision: the counter counts real
checks made before the first push. Two pre-push checks can therefore cause the
first post-push check to engage immediately. That is not exactly the stated
"two batch warm-ups in the incremental session" policy.

### Persistent encoding and retraction

`IncrementalSolver::Impl` owns, for the session
(`lib/Incremental/IncrementalSolver.cpp:181-269`):

- one SAT backend;
- one AIG manager and bit-blaster;
- an AIG-node-to-SAT-variable table for the current backend epoch;
- a formula-to-root-literal cache for the current SAT-backend epoch;
- session-owned fragment, symbol, DAG-size, and explicitly invalidatable
  preparation caches;
- persistent lazy-array and eager-Ackermann registries;
- one session-long floating-point encoding context;
- activation-literal, model-replay, and clause-mass bookkeeping.

`ensureEncoded()` emits only Tseitin definitions
(`IncrementalSolver.cpp:1381-1449`). These clauses are conservative extensions
and remain valid in every assertion context. Retraction is separated from
encoding:

- on the ordinary SMT-LIB path, a level-zero root becomes a permanent unit
  clause;
- a pushed level is represented by a root literal, or by one cached activation
  literal implying all roots in that level;
- every check supplies the currently active retractable literals as SAT
  assumptions;
- pop performs no SAT-side deletion: the next check simply omits the popped
  assumption.

There are intentional exceptions to the simple level-zero rule. The C API
prepends a synthetic `TRUE` base and treats every real assertion level as
retractable, because the API's query bracket and model lifetime differ from
SMT-LIB. Whole-array equality assumes one root for the complete active stack.
Long-stable pushed SMT-LIB prefixes may be promoted to permanent units, with a
backend rebuild as the only sound way to retract them later.

The solver's learned clauses remain valid because persistent clauses are
definitions, permanent base facts, theory-valid lemmas, or lifecycle clauses
over private activation variables (activation implications and pins for
retired activations). This is the same core invariant used by Bitwuzla's
bit-vector SAT layer and cvc5's dedicated bit-blasting solver.

### Word-level preprocessing

The incremental driver does not run master's whole-stack destructive pipeline
on every engaged check. It instead combines context-free rewrites, content
caches, and carefully constrained prefix-sensitive transformations.

Base definitions are monotone. They may be used as permanent substitutions
because level zero cannot be popped without destroying the driver, while the
defining assertion remains a permanent fact.

Pushed definitions are rebuilt into a query-local context in stack order
(`IncrementalSolver.cpp:3269-3519`). A definition at level `L` rewrites its own
level and deeper levels, never a shallower level. A defining assertion is not
rewritten under its own entry. This prefix rule prevents deeper stack growth
from changing the encoded form of an already prepared shallow assertion.

Preparation runs over either the whole level or its individual conjuncts,
depending on size. It applies substitutions, floating-point totalisation where
needed, equality propagation, simplification, and guarded variable elimination.
The result is cached by the rewritten formula, not merely by the raw assertion.

A definition can be removed only while its variable is private: it must not be
used by the base, another live level, another conjunct in the same level, or an
already bit-blasted encoding (`IncrementalSolver.cpp:964-986`). Eliminated
definitions are replayed into models. Newly seen content is screened against
eliminated variables; if a later assertion makes a variable shared, the cached
preparation is invalidated and its equation returns
(`IncrementalSolver.cpp:894-962`).

These rules are sound, but they are more dynamic than the strictly
forward-only policies in the reference solvers. They are also the reason a
single monotone "preparation cursor" would be insufficient: future content can
invalidate a still-live earlier preparation.

### Cross-level constant-bit propagation

`0ff90033` adds word-level CBP over the assertion prefix. Raw level
conjunctions are fed in order; facts discovered at level `L` may rewrite level
`L` and deeper content, with slot protection and pinning facts preventing
circular "assume it, simplify it to true" reasoning. Rewrites happen before
piece preparation, cache keying, and array transformation.

At the original review baseline, the engine persisted only while the stack
extended its previously fed prefix. A pop, changed level, or base growth reset
the engine and re-fed the surviving prefix. Per-level rewrite/fact memos
survived when their own prefix remained valid. This design fixed the
Industrial_Control_C family but made reset-and-re-feed the leading measured
scoped-state cost. The implementation update above records the subsequent
engine/caller rollback trail that removed that cost.

At the reviewed revision, the source comments in `IncrementalCBP.h` and the
beginning of the CBP field block still described a per-call engine. They
predated the cross-call persistence added at the branch tip; the documentation
changes accompanying this review correct them.

### Arrays, floating point, and extensionality

Lazy arrays use a persistent canonical row for each `(array,index)` pair.
Congruence lemmas over those canonical abstractions are theory-valid and can
remain permanent. The batch model/refinement table must nevertheless contain
only rows owned by the active encodings; a row from a popped assertion can have
floating SAT anchors and make model checking or refinement fail.

The branch records rows per encoded key and maintains active row-key reference
counts (`IncrementalSolver.cpp:1822-1958`). The table is materialized from fresh
registry values before refinement because refinement mutates the batch table in
place. Eager Ackermannisation instead keeps its per-array read history
monotonically: the newer read's ITE covers its relationships to older reads.

Floating-point operations are totalised and lowered through a session-long
context. The structural caches persist; assertion-specific side conditions
travel with the formula root and retract with it. Substitution is refused when
it would manufacture a novel variant of an already shared symfpu circuit rather
than genuinely collapse one.

Whole-array equality remains a whole-query operation. The complete active stack
is lowered, prepared, transformed, and assumed through one block root
(`IncrementalSolver.cpp:2508-2728`). The extensionality procedure's graph and
witness records are solve-local, while deterministic names, the root cache, and
the session AIG caches let an identical block reuse its encoding. At the reviewed
revision, an implementation comment incorrectly said block roots were not
cached even though the code at `IncrementalSolver.cpp:2614-2634` caches them;
the accompanying comment change corrects it.

### Models, assumptions, and API lifetimes

Models are built lazily. Definitions eliminated from the active stack are
seeded into the legacy model-evaluation channel for the current solved state,
and all entries seeded by the previous solve are withdrawn first
(`IncrementalSolver.cpp:2352-2405`). Array refinement receives a freshly
materialized active row table.

On the ordinary incremental path, `check-sat-assuming` uses a temporary
assertion frame, flattens its conjunction back to individual root literals, and
maps failed literals to the original assumption terms. Batch warm-ups and the
whole-array-equality block cannot provide that internal granularity and
conservatively report the full assumption list. The frontend frame is popped
after the check, but the solved model/core state deliberately remains readable
until the next state-changing operation
(`lib/Interface/cpp_interface.cpp:623-660,1007-1030`).

Ordinary SMT-LIB stack mutation invalidates a model. The C API has a different,
historical contract: a counterexample belongs to the last `vc_query` and remains
readable after the usual push/query/pop bracket. Any future eager semantic pop
hook must preserve both contracts.

### Solver growth and policy adaptations

The permanent encoding accumulates dead cones after pops. The relief valve
rebuilds a fresh SAT backend from live content once the solver is large and
the exact current-epoch submitted-clause total substantially exceeds the peak
owned by a live working set. Formula-key submission deltas provide a cheap
structural estimate. Before that estimate may authorize a rebuild, one lazy
exact walk repairs the peak from the unique AIG-cone union of the permanent and
latest current roots, whether the solve took the ordinary or extensionality
path. Permanent units, active activation implications, and owner-keyed theory
lemmas supply the non-structural share; retired activation lifecycle clauses
remain retained but dead. The AIG and semantic registries survive, but SAT
variables, root literals, learned clauses, and refinement lemmas are
rematerialized or re-derived.

The branch also contains measured policies for persistent-solver workloads:

- prefix-stable assumption-trail reuse, retired for large/FP sessions;
- retirement of recurring CaDiCaL inprobing, elimination, and shrinking;
- disabled lucky-phase probes;
- phase hints away from retracted roots;
- retirement of stale activation literals;
- promotion of long-stable prefix levels to permanent units, with a solver
  rebuild if a promoted level is later retracted.

These are not substitutes for semantic scoping, but several maintain their own
stack identity, liveness, or repair records because no common scoped substrate
exists.

## Results and established invariants

The historical campaign recorded in `HANDOVER.md` covered 22,999 files and
reported 7,520 wins of at least 2x, 258 losses of at least 5x, median runtime
0.086s versus master's 0.164s, and no disagreement under that harness's
comparison. It predates the latest tip and the repaired paired harness. In
particular, it should not be promoted to a current all-answer-sequence claim;
the quiet-machine rerun described below is still owed.

At an earlier implementation checkpoint, the recorded Industrial_Control_C
specimen improved from at least 90 seconds to 2.6 seconds, versus master at 1.5
seconds, with 164/164 answers agreeing. A 31-file family sample agreed fully.
The same CBP work took three Automotive stragglers from roughly 12--18 seconds
to roughly 0.8 seconds. The later rollback-versus-reset measurements above are
more specific to the retained CBP trail; neither set substitutes for a current
full campaign.

Other measurements materially shaped the design:

- rebuilding the full active read table consumed 42% of a thousand-query
  KLEE-style session before differential row seeding;
- a repeated capped DAG-size walk consumed 30% of the post-CBP specimen before
  per-node memoisation;
- the full Industrial specimen with fresh-per-call CBP took 9.7 seconds;
  prefix persistence reduced the run to 2.6 seconds;
- the remaining specimen gap is approximately 1.1 seconds of driver work,
  chiefly 31 pop-triggered prefix re-feeds, plus raw model validation at roughly
  13%;
- activating the driver on the second solve made two-check files the loss tail;
  engaging on the third restored batch parity for that class.

The development history established several load-bearing invariants:

- assumption literals must pass through any SAT-backend variable translation;
- a definition or CBP-fed assertion must never erase its own constraint;
- a transformation based on scoped facts must retain an asserted justification;
- a cached encoding is permanent, but the assertion selecting it is scoped;
- array abstractions may be structurally permanent while their participation in
  model/refinement state is scoped;
- every active array user must carry its row's index binding;
- stale model substitutions and popped rows must be withdrawn;
- conflicting CBP feeds must participate in prefix divergence;
- a refinement round rejecting a model without producing a new lemma indicates
  an encoding/model inconsistency, not useful progress;
- generated extensionality names keyed by nodes require the relevant node spine
  to be kept alive;
- semantic caches may survive a SAT rebuild, but SAT literals may not.

## Reference solver investigations

The reference solvers use different internal machinery, but converge on the
same separation of concerns:

1. a scoped assertion source or working stream;
2. an explicit frontier for each independently advancing pipeline, or an
   atomic commit boundary across stages;
3. scoped preprocessing facts and model reconstruction;
4. permanent structural encoding where sound;
5. explicit query/assumption-result lifetimes;
6. hard gates or repair rules for transformations that are not naturally
   incremental.

### Bitwuzla: the closest end-to-end model

Bitwuzla has one scoped `AssertionStack`, a solver-wide backtrack manager, a
preprocessor, and a solver engine (`src/solving_context.h:159-180`). Each
assertion is appended together with its current scope level
(`src/backtrack/assertion_stack.cpp:24-34`). Push records an assertion-count
watermark; pop truncates the stack and clamps all registered consumers
(`assertion_stack.cpp:126-157`).

This stack is a mutable working stream, not an immutable raw-input journal.
Preprocessing can replace its entries and insert derived assertions through an
`AssertionVector`; Bitwuzla retains original user assertions separately
(`src/solving_context.cpp:112-123,245-248`;
`src/backtrack/assertion_stack.cpp:37-78`). STP's recommended immutable raw
journal plus derived per-stage records is therefore a synthesis, not a literal
copy of this container.

#### Independent assertion views

An `AssertionView` contains its own `d_index` and exposes only unseen
assertions (`src/backtrack/assertion_stack.h:24-104`). The preprocessor and
solver engine own separately tracked views, so advancing one does not claim
work for the other:

- preprocessor construction and consumption:
  `src/preprocess/preprocessor.cpp:42-60,70-118`;
- solver-engine construction and consumption:
  `src/solver/solver_engine.cpp:32-54,457-494`.

Pending assertions carry their insertion level. Each consumer can therefore
defer work across pushes and later synchronize its local backtrack manager to
the stamped level. Empty levels do not force every subsystem to do work. The
views are not freely reorderable, however: the solving context always invokes
preprocessing before the solver-engine view consumes its output
(`src/solving_context.cpp:52-70`).

`AssertionVector` exposes the assertions of one level and allows passes to
replace them or insert derived assertions at that same level
(`src/preprocess/assertion_vector.h:25-95`). The preprocessor operates to a
fixed point over this window; lower levels are never reopened. Short-lived
rewrite/pass caches are cleared after the window, while true semantic state is
backtracked (`src/preprocess/preprocessor.cpp:124-133,234-383`).

#### Substitution safety

Bitwuzla explicitly handles the core incremental-elimination hazard. Suppose a
previous batch already encoded `F(b)`, and a later batch discovers `b = s`.
The later equality may simplify new formulas, but it cannot be replaced by
`true`: the old `F(b)` was never rewritten. Bitwuzla retains the defining
equality unless the variable first appeared in the current batch
(`src/preprocess/pass/variable_substitution.cpp:751-803,820-827`).

This is a deliberately conservative forward-only policy. It avoids the need to
invalidate or reprocess earlier levels. It may lose an elimination that STP's
current privacy analysis can recover, but its lifetime invariant is much
simpler.

#### Permanent encoding and active roots

The default bit-vector engine keeps its bit-blaster, AIG-to-CNF encoder, and SAT
backend alive. New top-level assertions are encoded with their roots asserted;
retractable assertions are definitionally encoded without a unit and their
roots are supplied as SAT assumptions on every solve
(`src/solver/bv/bv_bitblast_solver.cpp:154-187,225-256`). Its term-to-AIG and
AIG-to-CNF maps are permanent; its active root/assumption vectors are scoped.
Normal bit-vector push/pop does not touch the SAT clause database.

There are deliberate mode-specific exceptions. With unsat-core production,
all non-lemma user assertions, including level zero, travel as assumptions so
their provenance remains visible. Interpolation mode schedules SAT/CNF
reconstruction after pop (`bv_bitblast_solver.cpp:225-243,318-325,364-392`).
The persistent design described here is the default path, not a claim that
every Bitwuzla mode has identical lifetime rules.

The result is almost exactly STP's successful low-level design. Reasserting
popped content reuses the old circuit and clauses while restoring only its
active root.

Bitwuzla registers generated theory lemmas at top level. Correctness therefore
requires the lemma formula itself to be valid independently of the current user
assertions—for example, a guarded array congruence implication. This is a
producer invariant, not a generic enforcement mechanism. Its FP solver also
separates a permanent word-blast cache from backtrackable records saying that
the associated validity constraints are active in the current scope
(`src/solver/fp/fp_solver.cpp:64-109`; `src/solver/fp/word_blaster.h:162-166`).
STP's array-row and FP-side-condition designs must continue to observe the same
content-cache/active-side-condition rule.

#### Models and temporary assumptions

`check_sat(assumptions)` pushes a temporary context, appends the assumptions as
ordinary formulas, solves, and delays the pop so values and cores still observe
the solved state (`src/api/cpp/bitwuzla.cpp:1609-1643`). The next mutating API
call realizes the pending pop and invalidates the result
(`bitwuzla.cpp:1808-1819`). Model lookup applies the active preprocessing
substitutions before reading the solver model.

#### What to borrow

STP should borrow Bitwuzla's level-stamped working stream, separate preservation
of original inputs, independently tracked stage views, deferred processing, and
distinction between permanent content encoding and scoped activation. STP
should not blindly copy every backtrackable container or preprocessing pass.
Its current prefix rewriting is more aggressive and needs either
dependency-aware rewind or a deliberate move to Bitwuzla's simpler
forward-only rule.

### cvc5: context-dependent state and explicit flush boundaries

cvc5 stores assertions in a user-context `CDList`
(`src/smt/assertions.cpp:36-40`). `SolverEngine::assertFormula()` appends raw
assertions; preprocessing and SAT assertion are deferred. A
user-context-dependent `CDO<size_t>` is the frontier into that list
(`src/smt/smt_driver.cpp:151-155,204-215`). Only `[frontier,end)` is copied into
the preprocessing pipeline.

#### Context-dependent containers

cvc5's context library trails the first mutation to context-dependent objects.
It provides several cost models rather than one universal map:

- `CDO<T>` for a scoped scalar such as the assertion frontier;
- `CDList` for append/truncate sequences;
- insert-only maps and sets that trail inserted keys;
- fully mutable context-dependent maps for the smaller number of places that
  require overwrite restoration;
- notification objects for ordinary caches that are cheapest to invalidate
  wholesale on pop.

It also distinguishes the user assertion context from the SAT/theory decision
context. Preprocessing and input assertion state follow user push/pop; theory
fact queues and search state can follow the finer SAT context.

#### Flush before push

cvc5's raw assertions are not individually stamped for deferred processing.
It therefore enforces a different clean invariant: before a user push, flush
all pending assertions through preprocessing and into the propositional engine
(`src/smt/smt_driver.cpp:119-147`; `src/smt/context_manager.cpp:142-187`). Then
push both contexts. Pop reverses the dependency order.

This shows two sound alternatives:

- Bitwuzla: stamp each pending assertion and let each stage synchronize lazily;
- cvc5: make raw-to-internal processing atomic and flush it before establishing
  the next scope.

STP should choose explicitly. It should not let a single cursor imply that
several independently fallible stages have all completed unless their
transaction boundary really is atomic.

#### Incremental preprocessing

cvc5's assertion pipeline processes only the supplied delta. If preprocessing
finds `x = t` after `x` has already appeared in materialized formulas, it keeps
the equality as a real assertion while using the substitution on subsequent
inputs (`src/preprocessing/passes/non_clausal_simp.cpp:316-346`). Already
materialized symbols and substitutions are user-context dependent.

This is the same semantic rule as Bitwuzla expressed through different data
structures: never make an old encoded occurrence unconstrained merely because
a later definition was discovered.

#### SAT lifetime choices

cvc5's default Minisat-derived CDCL(T) backend tags variables and clauses with
assertion dependency levels. Pop can physically remove clauses, learned clauses,
and variables above a saved level while preserving lower-level learning. Its
main CDCL(T) CaDiCaL path uses activation literals through the attached
propagator; not every internal CaDiCaL instance has that lifetime. Its dedicated
BV bit-blasting solver instead resembles STP/Bitwuzla: the bit-blaster and CNF
stream live in persistent/null-context storage, while active facts, assumptions,
and fact-to-literal provenance remain context dependent.

STP should not copy cvc5's clause-level deletion machinery. It depends on
owning the SAT solver's variable, clause, and resolution-dependency internals.
For STP's external backends, permanent definitional CNF plus assumptions is the
more portable design and is already implemented.

#### Models, assumptions, and reset

Generic `check-sat-assuming` opens a temporary context and inserts assumptions
through the ordinary assertion pipeline (`src/smt/assertions.cpp:59-69`;
`src/smt/context_manager.cpp:51-68`). Pending post-solve cleanup is delayed so
model, proof, and core queries still see the exact solved context. Model lookup
applies preprocessing substitutions. Model access is modal—available only
immediately after an appropriate SAT/UNKNOWN result—and the theory model is
deliberately independent of the SAT context
(`src/smt/solver_engine.cpp:663-700`).

cvc5 also has distinct SAT-assumption mechanisms beneath this API behavior.
Assumption-based unsat-core mode passes input roots directly as SAT assumptions;
the dedicated BV bit-blaster solves under scoped fact literals. These should not
be conflated with generic `check-sat-assuming`, which uses the ordinary temporary
assertion context (`src/prop/prop_engine.cpp:265-309,452-495`;
`src/theory/bv/bv_solver_bitblast.cpp:187-216`).

`reset-assertions` unwinds user assertions and reconstructs the main
propositional engine, SAT solver, and CNF stream while retaining the theory
engine (`src/smt/smt_solver.cpp:102-117`). It discards assertions rather than
replaying a live stack. cvc5's deep-restart driver does replay saved preprocessed
assertions while recreating more of the engine, but is not supported in
incremental mode. STP's live-journal replay across a fresh backend is therefore
a stronger, branch-specific rebuild contract.

#### What to borrow

STP should borrow the explicit raw-to-internal frontier, flush/commit boundary,
context-sensitive substitution/provenance discipline, and fresh
main-propositional-backend escape hatch. It should not copy cvc5's full region
allocator, dual-context framework, proof pipeline, or clause dependency
deletion merely to obtain assertion cursors.

### Z3: cursor-based rewriting with replay and repair

Z3 supplies two relevant examples: the general SMT context and the QF_BV-oriented
incremental SAT solver.

#### Hybrid driver selection

The default strategic solver wraps a tactic/from-scratch child and an
incremental child in `combined_solver`
(`src/tactic/portfolio/smt_strategic_solver.cpp:153-188`). Both children receive
each raw assertion. A push, pop, assumptions, or an assertion after a completed
check selects the incremental child (`src/solver/combined_solver.cpp:162-220`).

Z3 deliberately duplicates frontend state rather than translating optimized
batch state into incremental state at the switch. STP chose a related but
cheaper policy: preserve its batch path, then let the incremental driver build
from the raw active stack when engagement occurs.

#### Assertion cursor and scoped simplifier state

Z3's newer simplifier framework stores dependent formulas in a scoped vector
with append-only assertion ingestion and a mutable unprocessed suffix. Passes
may replace suffix entries in place, and `flatten_suffix()` may compact it;
`qhead` still marks the committed prefix
(`src/ast/simplifiers/dependent_expr_state.h:45-88,119-185`). Simplifiers
iterate only `[qhead,qtail)` (`dependent_expr_state.h:203-223`). Push trails the
cursor and frozen-symbol state; pop restores them. After a successful flush,
`advance_qhead()` freezes the processed prefix and moves the cursor to the end.

`simplifier_solver::flush()` first replays prior model-reconstruction records
against the new suffix and assumptions, runs the incremental simplifier, commits
the cursor, and then sends the resulting processed range beginning at the saved
old `qhead` to the child solver (`src/solver/simplifier_solver.cpp:129-150`).

The classic SMT `asserted_formulas` path has the same underlying discipline:
every preprocessing pass sees its uncommitted suffix; push is lazy, but forcing
it first reduces and commits pending formulas, then saves formula, substitution,
definition, macro, and cursor limits. Pop restores those watermarks and clears
rewrite caches (`src/solver/assertions/asserted_formulas.cpp:190-242,266-307,
491-537`).

#### Freeze, replay, and repair

Once a prefix is handed to the backend, Z3 freezes the symbols it contains
(`src/ast/simplifiers/dependent_expr_state.cpp:92-100`). Incremental passes skip
unsafe elimination targets from that prefix.

Z3 also supports a more aggressive repair mechanism. The model-reconstruction
trail distinguishes equivalence-preserving definitions/substitutions from
loose substitutions, loose constraints, hidden terms, and related records that
must be disabled or replayed when later formulas intersect them
(`src/ast/simplifiers/model_reconstruction_trail.h:38-88`). Before simplifying
a new suffix, it checks whether its symbols intersect an older transformation:

- stable definitions may rewrite the new suffix;
- a loose substitution is disabled and its equality is reasserted;
- a loose removed constraint is replayed;
- the same records reconstruct eliminated values in the model.

See `src/ast/simplifiers/model_reconstruction_trail.cpp:39-195`. The taxonomy is
powerful, but incorrectly classifying a loose transformation as
equivalence-preserving is a direct soundness risk. STP's private-elimination
screening is a specialized form of the same repair idea, currently without a
first-class level record to rewind.

#### Three distinct lifetimes

The classic SMT context coordinates:

- user assertion scopes;
- temporary query/assumption/search scopes;
- SAT decision/theory scopes.

Each subsystem either trails its mutations or exposes a saved watermark/pop
hook. Arbitrary Boolean assumptions are represented by temporary proxies in a
query scope. UNSAT cores are copied through the proxy mapping before that scope
is removed; a SAT query scope remains alive long enough for lazy model creation.
The next check or mutation removes it (`src/smt/smt_context.h:677-727`;
`src/smt/smt_context.cpp:3122-3155,3330-3583,3801-3829,4865-4936`).

This is the central lifetime lesson for STP: assertion state, last-result state,
and SAT search state are related but not interchangeable depths.

#### Incremental SAT mode

`inc_sat_solver` is especially close to an STP target. It owns a formula log,
`m_fmls_head`, per-scope formula/head/assumption limits, scoped atom and model
converter state, one bit-blaster, and one persistent SAT solver
(`src/sat/sat_solver/inc_sat_solver.cpp:50-82`). It internalizes exactly
`[m_fmls_head,end)` and then advances the head (`inc_sat_solver.cpp:1094-1115`).
Push flushes pending formulas and records all component watermarks; pop restores
them (`inc_sat_solver.cpp:272-318`).

At the SAT layer, user scopes are marker literals. New clauses are augmented
with active markers; checks assume the markers' negations; pop drops markers and
garbage-collects clauses mentioning popped variables while retaining learning
over survivors (`src/sat/sat_solver.cpp:351-373,1887-1912,3765-3800`;
`src/sat/sat_gc.cpp:403-461`). SAT simplification explicitly disables unsafe
variable/clause elimination in incremental mode.

This differs from Z3's classic SMT user pop, which truncates learned state to a
saved lemma watermark and may save/re-internalize AST atoms from search scopes.
The marker-based incremental SAT path is the closer analogue to STP because it
can retain survivor-only learning.

STP should borrow the formula-head/watermark organization and preprocessing
gates, not Z3's physical E-graph/Boolean deletion and reinternalization.

### Convergence and important differences

| Question | Bitwuzla | cvc5 | Z3 | STP branch |
|---|---|---|---|---|
| Assertion source/working stream | Scoped original-input list plus level-stamped mutable stack | User-context raw `CDList` | Scoped dependent-formula vector with mutable suffix | Per-level raw `ASTVec`, destructively conjoined for solving |
| Unprocessed work | Separately tracked, stage-ordered assertion views | One context-dependent transaction frontier | `qhead` per simplifier/state | Recomputed whole-stack loops plus subsystem-specific memos |
| Pop of semantic state | Backtracked containers and clamped views | Context-dependent objects | Trails and watermarks | Mostly reconstruct next check; manual subsystem repair |
| Preprocess old levels again | No | No | No, unless replay/repair invalidates a transformation | Metadata/context rebuilt; heavy transformations usually cache-hit |
| Structural BV encoding | Permanent in the default path | Persistent/null-context maps in BV solver; scoped in general CDCL(T) | Persistent in incremental SAT mode | Session AIG/cache plus backend-epoch CNF/root map |
| Retractable SAT assertions | Assumed roots | Assumptions, clause levels, or activations depending on backend | Marker/assumption scopes | Root or per-level activation assumptions |
| Late variable definition | Keep equality unless safe in current batch | Reassert definition if symbol already materialized | Freeze or replay/repair | Dynamic privacy test plus future-content invalidation |
| Temporary assumptions | Delayed-pop assertion scope | Delayed cleanup of temporary context | Query scope/proxies | Temporary frontend level, solved state retained |
| Batch path | Same engine with gated passes | Same driver with option gates | Separate tactic child | Separate batch driver, delayed engagement |

No solver provides a zero-cost universal answer. Bitwuzla's variable-
substitution pass copies its full map and apply cache when its local manager
pushes so processing remains valid after pop; cvc5 pays for context-dependent
objects and clause provenance; Z3 pays for duplicate drivers, trails, and repair
classification. The shared lesson is not a particular container. It is that
state lifetime is explicit and local rather than inferred by reconstructing the
whole active query.

## State-lifetime audit of the STP branch

The current implementation already has several distinct lifetimes. They are
real, but they are expressed through container choice, cache keys, and repair
code rather than through a common scoped-state interface.

| Lifetime | Representative state | Current mechanism |
|---|---|---|
| Session-owned semantic content | fragment, symbol, DAG-size, generated-name, array-read, eager-Ackermann, and FP caches; retired-epoch clause-submission accumulator | Content-keyed maps and lifetime totals generally retained for the `IncrementalSolver` lifetime |
| Explicitly invalidatable semantic caches | prepared pieces, elimination users, screened content | Retained until dependency invalidation or backend-repair logic drops/clears them |
| SAT-backend epoch | SAT variables, AIG-to-variable map, root literals, activation literals, learned clauses, refinement lemmas, exact retained-submission counter, root/ownership maps, permanent-root/unit mass, one pending live-cone snapshot, and current/peak live mass | Retained until a relief/policy rebuild; explicitly cleared or rematerialized by `rebuildEncodings()` |
| Permanent base semantics | `level0Asserted`, `sigma0`, restored base eliminations | Monotone sets/maps on the SMT-LIB path because reset destroys the driver |
| Active user scopes | raw frontend `ASTVec` levels | Supplied again as a complete snapshot at each check |
| Subsystem views of active scopes | CBP fed prefix/memos, promotion stability, active read-key refcounts, current eliminated definitions | Independently maintained ad hoc, usually by longest-common-prefix or set-difference logic |
| One query/refinement round | assumptions, active roots, pushed definition context, batch array table, extensionality records | Rebuilt for the current snapshot and discarded or overwritten |
| Last result | model-pending state, failed literals, assumption-to-level map, eliminated-definition model seeds | Retained after solve under API-specific invalidation rules |

This table also explains why the existing `Backtrack.h` is not yet the missing
architecture. It supplies tested append-only and insert-only backtrackable
containers, but production solver state does not use it. More importantly,
several important states overwrite existing values: CBP tightens `FixedBits`,
preparations can be invalidated, active-row reference counts rise and fall, and
SAT literals are replaced wholesale at a rebuild. Insert-only containers cannot
express those lifetimes without an additional mutation trail or a different
record structure.

### What is reconstructed on an ordinary check

Even when no new formula is encoded, `checkSatOnCurrentStack()` currently does
work proportional to some or all of the active stack:

- compares saved level conjunctions to the current stack for promotion and CBP
  prefix stability;
- scans levels for floating-point, array-equality, and array fragments (the
  fragment analysis itself is cached);
- screens newly observed raw content against prior private eliminations;
- splits each live level and re-harvests pushed definitions into `ctx`,
  `ctxSources`, and `ctxHasFp` in prefix order;
- reconstructs per-level symbol counts and the current list of eliminated
  definitions, while usually hitting the expensive preparation caches;
- reconstructs roots, activation assumptions, failed-core provenance, active
  encoding keys, and live clause mass;
- computes the active read-key difference and materializes fresh batch array
  rows for refinement;
- when CBP has diverged, rolls its scoped engine/caller state back to the LCP
  and feeds only the replacement suffix (the diagnostic oracle instead resets
  and re-feeds the surviving prefix);
- when a model is materialized, seeds current reconstruction definitions; when
  counterexample checking or array refinement requires validation, it also
  checks a candidate against the relevant raw/semantic active formula.

The main loop and context reconstruction are visible at
`IncrementalSolver.cpp:3183-3643`; active-row seeding is at
`IncrementalSolver.cpp:1893-1958`. Caches change much of this from repeated
transformation into repeated traversal and collection, which is why the branch
can still win substantially without cursors.

Some whole-query work is irreducible under the present semantics:

- SAT assumptions must describe every active retractable root unless stable
  prefixes are made permanent or represented by a hierarchical activation
  scheme;
- requested counterexample validation must establish that the candidate
  satisfies the current query;
- ordinary array refinement needs a fresh table containing all live rows;
- whole-array equality deliberately reasons about the complete active graph;
- a SAT-backend rebuild must rematerialize every live semantic root in the new
  literal epoch.

The objective of scoped state is therefore not “make every check O(delta).” It
is to stop rediscovering semantic facts that already have a precise scope and
to make pop correctness local and auditable.

### Why one monotone preparation cursor would be unsound

A cursor is safe only if processing an assertion is final until that assertion
is popped. That is not true for all of STP's current preprocessing:

1. More assertions can be appended to an existing top level without a push.
   The conjunction node and level revision then change at the same depth.
2. A later assertion can mention a variable privately eliminated from an
   earlier live piece. `screenNewContent()` must invalidate that earlier
   preparation and restore its defining equation.
3. A deeper definition may rewrite deeper assertions but must never change an
   already materialized shallower assertion. Cursor movement must preserve this
   prefix rule.
4. Whole-array equality routes all levels through a different, whole-query
   pipeline. A level that has passed the ordinary encoder has not thereby
   passed the extensionality pipeline.
5. A SAT rebuild invalidates every literal cursor without invalidating the
   semantic preparation cache that produced the formulas.
6. `check-sat-assuming` needs individual assumption provenance and a result
   lifetime that extends beyond removal of its temporary assertion frame.
7. Reusing stack depth as identity is ambiguous: after pop and push, a new
   level at the same depth is a different scope even if its conjunction happens
   to be structurally equal.

Consequently, the target is an assertion journal with versioned scope identity,
independent stage cursors, and explicit invalidation—not one global “processed
up to here” index.

## Immediate risks and closeout work

These items must be closed before a broad semantic-state migration. Items 1--3
are implemented through `9cb7b34b`, item 4 is completed by the accompanying
documentation commits, and item 5, the full campaign, remains outstanding.

### 1. Active-read state across rebuilds and eager cache hits (complete)

`seedActiveReads()` maintains pushed read ownership by taking a set difference
between `lastSeededKeys` and the current active keys. It keeps the resulting
row reference counts in `seededRowRef`, with each key's contribution recorded
in `foldedRowsOf` (`IncrementalSolver.cpp:1834-1958`).

`rebuildEncodings()` clears `lastSeededKeys` at line 2111 but retains
`seededRowRef` and `foldedRowsOf`. If the live array cone differs between the
last refinement round and the first refinement round after a rebuild, the
forgotten old-key set can no longer drive `unfoldKeyReads()`. A stale popped
row can consequently remain materialized, while an apparently new key that is
still in `foldedRowsOf` will not be folded again.

Follow-up confirmed reachability. A permanent read initially encoded at
`A[i+1]`, followed by the permanent definition `i = 0` and enough dead pushed
circuits to trigger the valve, re-encoded the same base key at `A[1]`. The stale
folding state then seeded `A[i+1]` and omitted the replacement, causing the
refinement no-progress guard to abort. Commit `9eb8e407` adds the forced-valve
regression and fixes the rebuild by clearing `lastSeededKeys`, `seededRowRef`
and `foldedRowsOf` together, clearing the materialized batch tables, and
re-queuing every permanent key. The canonical `myReads` registry remains
session-owned.

A second reachable problem affected eager Ackermannisation without changing
the SAT answer. The frontend clears the batch transformer before every solve,
and an all-cache-hit eager round had no refinement stage that would seed its
active reads again. Commit `02607540` now rematerializes those observations
after SAT whenever a model may be read, covering deferred model construction
and immediate sanity checking without re-encoding the constraints.

### 2. Retained-clause accounting and extensionality (complete)

The original inspection found that the ordinary path counted only structural
encoding deltas, while direct theory clauses, extensionality blocks,
activation lifecycle clauses, and permanent units could bypass either the
retained total or its live ownership model. `db4aab0a` and `c604e923` close
those blind spots: the common SAT facade supplies the exact current-epoch
submission total, the driver separately preserves lifetime submissions across
backend rebuilds, and theory-refinement submissions are a reported subset.

Live/peak ownership now covers actual structural AIG roots,
base/restored/promoted units, currently assumed activation implications, and
owner-keyed theory lemmas. Retired implications and their false pins stay
retained but dead. `9cb7b34b` replaced the extensionality-only repair with one
exact unique-cone union for both ordinary and extensionality paths. Normal
solving retains only the latest snapshot above the variable floor and walks it
only if the cheap ratio would rebuild; profiling measures the exact union on
every solve. The forced-churn and monotonic-live tests in `45fe552b`, repaired
per-round negative checks in `8e421b89`, and ordinary shared-cone regression in
`9cb7b34b` cover the policy.

### 3. Integrate current master before structural work (complete)

Merge `4b60b401` integrates master through `34f69be1`, including the earlier
`d272dc2a` difficulty/FP work and `fa211128` fixed-width types, plus the later
SAT-backend factory, backend-neutral literal, and optional-MiniSat changes. The
incremental code was adapted to that backend construction and build matrix
before any assertion-journal work.

### 4. Keep the corrected documentation with the branch (complete)

The user guide, source comments, and this review now describe third-solve
automatic engagement, persistent CBP rollback, extensionality block reuse,
unified live-cone accounting, eager-array model rematerialization, exact
retained versus lifetime clause counters, and the repaired campaign
verdict/provenance rules. These are soundness and measurement contracts, not
implementation trivia, and belong with the branch.

### 5. Rerun the full campaign (outstanding)

The 22,999-file result predates the latest tip and used the predecessor
comparison behavior. Before upstreaming, run the repaired paired harness on an
otherwise idle machine, compare every answer sequence with master, and
reclassify the performance tail. A timeout with a matching prefix is
`PREFIX_ONLY_INCONCLUSIVE`, not agreement; only identical streams from two
successfully completed arms are `FULL_OK`. Preserve the manifests, shard
identity, arm fingerprints, main CSVs, and longer revalidation results.
Sequential spot timings on the known thermally sensitive FP families are not
evidence.

### 6. Treat the RTOS tail as engagement overhead until measured otherwise

The remaining recorded loss class is about 1.3 seconds on inputs master solves
in roughly 0.02 seconds. There is no evidence that semantic stack
reconstruction dominates that delta. It is more consistent with constructing
and warming a second solver path, backend startup, or another fixed engagement
cost. Measure it separately; do not use it as justification for scoped state.

Two narrower policy questions can be settled at the same time:

- should automatic engagement count checks before the first push, as it does
  now, or checks within the pushed phase only;
- should the all-ever-rows walk in `totalizeRegistrySymbols()`
  (`IncrementalSolver.cpp:1960-1977`) become a touched/live-row delta if it is
  material on long lazy-array sessions.

## Instrumentation before refactoring

The instrumentation phase made semantic reconstruction visible. The older
statistics reported newly encoded conjuncts, clauses, assumptions,
substitutions, CBP rewrites, and refinement rounds, but did not partition the
driver time well enough to decide which scoped state would pay.

The per-check and session-aggregate profiler reports:

- stack snapshot/LCP synchronization and promotion repair;
- new-content screening and preparation invalidations;
- pushed-definition harvest, context replay, and context size by level;
- preparation attempts, cache hits/misses, and accepted/rejected trials;
- CBP prefix comparison, divergence, rollback/reset count and work, re-fed
  levels/nodes, fresh feeds, propagation, harvest, adoption, and memo replay;
- root/activation lookup, assumption construction, active key count, lifetime
  clause submissions, refinement submissions, exact current-epoch retained
  submissions, and current/peak live ownership;
- active-read fold/unfold deltas, live-row materialization, and all-registry
  totalization;
- extensionality lowering, preparation, encoding, totalization, checking, and
  refinement;
- model-seed withdrawal/install, model construction, and—when enabled or
  required by refinement—raw/semantic formula validation;
- time inside SAT, split by the initial solve and refinement re-solves.

The output distinguishes cache-hit traversal from genuinely new semantic work
and includes counts as well as time. A timer saying “context: 20 ms” is hard to
interpret; “130 levels replayed, 4 new assertions, 0 preparation misses”
identifies the missing cursor directly. It uses a dedicated
`--incremental-profile` switch rather than `-s`, whose verbose pass diagnostics
would distort the measured scopes. Ordinary output and benchmark parsers
therefore remain unchanged.

Measure at least these workload shapes:

- the Industrial Control specimen and family, especially its 31 pop-triggered
  CBP re-feeds;
- RTOS small files, to isolate fixed engagement cost;
- KLEE `b64`, for pop-per-query behavior and read/table costs;
- `f84c6e97` and `1ccb771c`, for stable-prefix and solver-policy behavior;
- the Automotive family and the seven former FP-substitution timeouts;
- forced-rebuild lazy-array and extensionality cases;
- representative QF_BV, QF_BVFP, and QF_ABVFP samples from the full campaign.

The measurements did confirm CBP re-feed as the leading narrow candidate and
the implementation result is recorded above. Further cursor work should still
be decided from cross-workload aggregates, not from the one Industrial
specimen. If future profiles show context reconstruction, active-root assembly,
or row materialization dominating important workloads, move that consumer
forward in the cursor roadmap. If reconstruction stays small, scoped state
remains a maintainability investment and should be paced accordingly.

## Recommended scoped-state architecture

This should be introduced narrowly. STP does not need cvc5's complete context
framework or Z3's E-graph scope machinery to obtain the useful invariant.

### 1. A versioned assertion journal

Replace “one newly collapsed conjunction per current depth” as the driver's
semantic input with a lightweight canonical journal. A suitable logical model
is:

```text
AssertionEntry = { assertion_id, scope_id, level, raw_formula }
ScopeRecord    = { scope_id, kind, revision, begin, end, cached_conjunction }
Journal        = { epoch, entries, scope_watermarks, next_unique_id }
```

- `assertion_id` and `scope_id` are monotone unique identities, never reused
  merely because a depth is reused after pop;
- appending at the current level adds an entry and increments that scope's
  revision;
- push records the current journal length and creates a new scope ID;
- pop truncates to the saved watermark and reports the removed scope IDs;
- reset increments the journal epoch, invalidating every external cursor;
- the per-level conjunction is a cached view, not the canonical data.

`kind` must encode frontend semantics, for example `permanent_user`,
`retractable_user`, or `query_overlay`; depth zero alone does not imply
permanence. The C API prepends a synthetic `TRUE`, treats every real assertion
level as retractable, and appends `NOT query` only to the local solve vector—not
to `STPMgr::_asserts` (`lib/Interface/c_interface.cpp:817-830`). The journal API
therefore needs an explicit query-local overlay or a frontend-specific view.

The existing `STPMgr::_asserts` is the frontend source of individual assertions
and scopes, but its current `getVectorOfAsserts()` destructively replaces each
level's entries with one conjunction (`STPManager.cpp:860-883`). Batch warm-ups
can therefore erase assertion boundaries before delayed driver engagement.
Either make that accessor non-mutating or make the journal canonical from
session start at `AddAssert`/push/pop time. A driver created later treats all
currently active journal entries as initially unprocessed; it must not attempt
to recover identities from already collapsed conjunctions.

### 2. Independent stage cursors

Each consumer owns a cursor and its own scoped watermarks:

```text
StageCursor = { journal_epoch, next_entry, per_scope_limits, reset_epoch }
```

Consumers advance only after their outputs have been committed. If processing
throws, times out, routes to another pipeline, or triggers a SAT rebuild, no
unrelated cursor is advanced implicitly. Pop clamps each cursor and rolls back
that stage's scoped outputs; it does not pretend that another stage completed.
Whenever the API says a result outlives the removed scope, result-dependent
substitutions, provenance, and extensionality state must first be snapshotted or
pinned, or cleanup must be deferred until the next operation that invalidates
the result.

Initial low-risk consumers are:

- assertion/scope metadata and cached conjunction views;
- statistics about new assertions and scope shape;
- pure symbol-set and DAG-size memoization;
- frontend-aware base-symbol discovery.

`screenNewContent()` should migrate with processed-level dependency state, not
in this first group. It can invalidate older preparations, call `rootLit()`, and
add permanent units while restoring a base elimination; its seen-content memo
is also cleared at a backend rebuild. It therefore needs a semantic/rebuild
generation and a transactional ordering rule that finishes screening all new
content before any stale prepared entry can be reused.

The initial consumers exercise journal identity and pop/reset handling without
changing formula semantics.

### 3. Versioned processed-level records

Context-sensitive preprocessing needs more than a cursor. Give each scope a
processed record, conceptually:

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

A record is reusable only when its scope revision, relevant prefix generation,
mode, and semantic-cache epoch match. Later content mentioning a previously
eliminated variable marks the owning record dirty and invalidates the earliest
dependent suffix; it does not merely move a global cursor forward. This is the
first-class form of the repair already implemented by `eliminationUsers` and
`dropPreparedLevel()`.

Context maps should be represented as per-level deltas plus watermarks or a
persistent overlay, not copied wholesale for every check. Replaying a prefix
then means installing its recorded deltas in order. A conservative first
version can retain STP's current prefix rules exactly; adopting Bitwuzla's
forward-only elimination policy is a separate performance/complexity choice,
not a prerequisite for the journal.

### 4. Separate semantic-cache and SAT epochs

Every record that contains SAT literals must carry a backend epoch. A rebuild
increments that epoch and invalidates literal/activation views while preserving
AST-level preparation, canonical array rows, FP circuits, and other semantic
caches. Live records are then replayed into the fresh backend. This makes the
existing rebuild contract explicit and prevents a journal cursor from
accidentally treating old literals as processed in a new solver.

### 5. Keep result lifetime separate from assertion lifetime

Do not make model/core state an ordinary user-scope container. A temporary
assumption scope can disappear from the active journal while the last result
still needs its substitutions, assumption provenance, extensionality records,
and solved SAT assignment. Either retain a result snapshot or use a delayed
query-scope cleanup, as all three reference solvers do.

The ordering invariant is: first snapshot or pin everything needed to interpret
the result, then clamp assertion cursors, and only later destroy the snapshot on
the next invalidating operation. Immediate semantic rollback without that first
step is not safe merely because the raw scope has been removed.

The C API needs an additional explicit rule: the model of `asserts AND NOT
query` survives the conventional `vc_push`/`vc_query`/`vc_pop` bracket until
the next invalidating API operation. A generic pop broadcast that clears all
scoped state would regress that contract.

## Why the CBP undo trail should precede the journal

The assertion journal would tell CBP exactly which levels are new or popped,
but it would not restore the engine's old `FixedBits`. At the review baseline,
the engine tightened multiple `FixedBits` objects through bidirectional
transfer functions, latched conflict, grew auxiliary multiplication state, and
maintained a caller-side substitution/fact overlay without an undo mechanism.
It therefore had to reset and re-feed the surviving prefix after every pop.
Thus implementing the journal first would have been a broad refactor that left
the one measured reconstruction bottleneck intact.

The implemented narrow CBP change uses the existing longest-common-prefix
synchronization:

1. begin a level transaction before feeding it and commit only after feed,
   rewrite/adoption, memo and pinning-fact writes, and `cbpFinishLevel()` have
   all completed;
2. on divergence, roll back directly to the LCP rather than destroying the
   engine;
3. feed only the changed suffix;
4. leave the existing per-level rewrite/fact memo and adoption policy in place;
5. later replace LCP polling with journal push/pop notifications without
   changing the engine contract.

### Required rollback state

The trail must cover all semantic mutation, not just newly inserted map keys:

- the first pre-level value of every existing `FixedBits` object changed by a
  transfer function, plus keys created in the level;
- the previous conflict state, including a feed that ends in conflict;
- caller-side `callCbpConflict` and `callCbpOff`, which a conflicting feed
  latches and a rollback below that level must clear/restore;
- mutable multiplication-transfer auxiliary state, either by trailing it or by
  conservatively clearing/rederiving it on rollback;
- insertions, overwrites, erasures, and restores in the accumulated constant
  substitution, recording the previous binding rather than only inserted keys;
- deferred intra-level fixings;
- fed-conjunct and emitted-pinning-fact membership;
- feed mass/cap and array-presence summaries;
- the active fed-level and memo watermarks.

The implementation records each mutable object at most once per level (a
first-write trail), even if the worklist visits it repeatedly, and restores
entries in reverse order. `newlyFixed` deliberately remains populated as the
successful feed's output until the next feed; rollback clears it. Conflict
paths clear both work queues and the output immediately, and rollback clears
all transient scratch defensively before restoring state.

Session policy is a different lifetime. `cbpSessionRetired`, `cbpEverFixed`,
and the retirement evidence counters describe observed workload behavior and
normally should not roll back with assertions. Preserve reset/re-feed as both a
differential oracle and a fallback if trail memory/growth becomes more
expensive than rebuilding.

The implementation trails exact parent-graph and visited-DAG additions. This
keeps later replacement feeds from retaining dependency edges introduced only
by a popped suffix and permits the caller's array-presence summary to roll back
to the same boundary.

`Backtrack.h` can supply the manager/watermark shape and insert-only pieces, but
cannot trail in-place `FixedBits` mutations as written. Extend it with a
purpose-built value undo trail or keep that trail local to `IncrementalCBP`;
do not force the engine into an insert-only abstraction.

### Do not resurrect the old prototype unchanged

Commit `d61d2c04` contains an earlier CBP undo-log experiment, and commit
`8a0d4a30` removed its integration after real answer disagreements. The
recorded root cause was circular preprocessing—assuming individual pieces,
simplifying them under their own truth, and then losing the original
constraint—not evidence that rollback is impossible. The current word-level
engine has since acquired the necessary level feed, slot protection, pinning
facts, conflict recording, cross-level adoption, and prefix memo semantics.

The old code is useful as a catalogue of mechanics, but it also had incomplete
dependency growth and recorded snapshots before mutations without a
first-write discipline. Port the rollback idea into the current engine and
re-prove the current invariants; do not cherry-pick it as an implementation.

### Validation mode for the trail

The reset/re-feed behavior is available as `--incremental-cbp-reset`. Separate
trail and oracle runs compare:

- conflict status;
- the set and value of harvested total fixings;
- rewritten conjuncts and emitted pinning facts at every level;
- final answer sequence and, for SAT, raw-formula model validation.

Include conflict/pop/re-push, appending to the current top level, empty scopes,
base growth, feed-cap retirement, symbol definer preservation, array-containing
nodes, and repeated rollback to several different depths. The Industrial
specimen is the performance acceptance test, not the soundness test.

## Phased roadmap

### Phase 0 (four of five complete): close the current branch

1. **Complete:** resolve active-read state across a lazy-array rebuild and an
   all-cache-hit eager-Ackermann model (`9eb8e407`, `02607540`).
2. **Complete:** define exact retained and guarded live/peak clause accounting,
   cover extensionality and refinement, and protect both extensionality and
   ordinary shared live cones (`db4aab0a`, `c604e923`, `45fe552b`, `8e421b89`,
   `9cb7b34b`).
3. **Complete:** integrate master through `34f69be1` and resolve the backend
   construction/type overlap deliberately (`4b60b401`).
4. **Complete:** reconcile the user guide, this review, source comments, and
   campaign-harness contract.
5. **Outstanding:** run the full quiet-machine paired campaign and preserve the
   manifests, fingerprints, full answer streams, timeout prefixes, and
   revalidation results as the new baseline.

A confirmed correctness issue preempts performance work. The tests and audits
can be prepared alongside instrumentation, but no broad state migration should
land on top of an ambiguous rebuild invariant.

The implementation and documentation prerequisites are closed. The repaired
harness is tested, but no current-tip whole-corpus result has yet replaced the
historical campaign. That campaign remains the final Phase 0 gate.

### Phase 1 (complete): instrument semantic reconstruction

Land counters/timers without changing solver policy. Re-run the representative
workloads and quantify both absolute cost and percentage of driver time. Record
the result in this document or a checked-in benchmark ledger.

### Phase 2 (complete): add the narrow CBP undo trail

Checkpoint/rollback now covers the engine and caller overlay while retaining
LCP-based stack synchronization, with reset/re-feed as the oracle. It met the
acceptance condition: Industrial pop cost fell without answer changes or a
material canary regression. The measurements above support keeping the trail.

### Phase 3: introduce the journal and safe cursors

Add stable assertion/scope identity and independent views. First migrate
journal observability and pure metadata; then migrate frontend-aware fragment
and base discovery. Keep screening with dependency-aware `LevelState` work.
Keep the public solver behavior and persistent SAT/AIG design unchanged.

### Phase 4: migrate preprocessing state where justified

Add `LevelState` records and scoped context deltas. Replace whole-stack
definition re-harvest and active-elimination reconstruction only after
dependency invalidation tests are in place. Preserve the current prefix
semantics first; consider a simpler forward-only substitution rule only as a
separate measured change.

### Phase 5: migrate array liveness and other aggregates

Express active read ownership, live clause mass, promotion stability, and
similar stack aggregates as consumers of the same scope identities. Preserve
fresh row materialization before refinement. Optimize all-ever-row
totalization only if instrumentation identifies it.

### Phase 6: reconsider whole-query procedures

Extensionality is deliberately whole-graph and should be migrated last, if at
all. Reusing its deterministic encoded block may remain the right design even
after ordinary assertions become cursor-driven.

At every phase, stop if the measured benefit is absent. The journal still has
maintainability value if repeated lifetime bugs continue, but it should not be
sold as a demonstrated RTOS performance fix.

## Test matrix for scoped state

The architecture needs tests below the SMT-LIB answer level as well as the
existing differential suite.

Journal/view unit tests should cover:

- independent consumers advancing at different rates;
- append at the current level and revision invalidation;
- empty push/pop and multi-level pop;
- cursor clamping and reset epochs;
- pop followed by a new scope at the same depth;
- identical re-pushed content receiving new scope identity while still hitting
  content caches;
- a consumer failing before commit and retrying the same delta.

Solver tests should cover:

- repeated unchanged checks and extension-only stacks;
- append, pop, alternate re-push, and identical re-push;
- same-level late definitions and deeper definitions that may not rewrite a
  shallow prepared root;
- later content invalidating private elimination and restoring the equation;
- content seen before a pop, a later elimination, and an identical re-push that
  must be screened under the new semantic/rebuild generation;
- base growth after engagement and after a SAT rebuild;
- `check-sat-assuming` models and failed-assumption granularity;
- SMT-LIB model invalidation versus the C API's post-pop model lifetime;
- the C API's synthetic base and query-local `NOT query` overlay;
- lazy arrays across forced rebuild, active-row withdrawal, and refinement;
- eager Ackermannization, floating-point side conditions, and array equality;
- SAT-backend epoch changes, promotion repair, and re-materialized roots.

Every semantic phase should retain batch-versus-incremental answer-sequence
differential testing. The final gate remains the full campaign, not only unit
tests and selected performance specimens.

## Approaches not recommended

- Do not replace permanent definitional CNF plus assumptions with SAT-clause
  deletion. STP's multiple external backends make cvc5/Z3-style clause
  provenance a poor fit.
- Do not introduce cvc5's complete dual-context/region/proof infrastructure to
  obtain assertion cursors.
- Do not copy Z3's E-graph deletion and re-internalization machinery into this
  bit-vector-focused driver.
- Do not backtrack canonical structural encodings merely because their current
  activation is scoped. Preserve the content/activation separation.
- Do not equate a cache with liveness. Canonical array rows, FP rewrites, and
  root encodings may persist while their participation in the current model or
  query must be explicitly scoped.
- Do not promise O(delta) checks where the API/configuration requires all active
  assumptions, a whole-query model check, live-row materialization, or
  extensionality over the complete graph.

## Final recommendation

The branch's persistent SAT/AIG architecture is sound in shape, portable across
its backends, and responsible for the measured wins. Keep it.

Instrumentation and the narrowly designed CBP first-write undo trail are now
implemented. They directly removed the measured pop-triggered whole-prefix
re-feed, and the cross-workload results support retaining the change.

The assertion journal with independent stage cursors remains the right
architectural foundation after that. It should be introduced incrementally to
make semantic lifetime explicit, remove repeated whole-stack bookkeeping, and
reduce the likelihood of further manual cache/refcount/rebuild bugs. It is not
the next automatic performance patch: integration, accounting, and
documentation are now closed, so first complete the repaired-harness full
campaign and then use the profiler to establish another material target or a
recurring lifetime problem. The journal does not address the likely fixed
engagement cost in the RTOS tail.
