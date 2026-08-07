Incremental solving
===================

STP solves incremental SMT-LIB2 sessions -- ``push``, ``pop``, repeated
``(check-sat)``, ``(check-sat-assuming ...)`` -- by normally keeping one SAT
solver and one bit-blasted encoding alive across checks, instead of
re-solving the conjoined assertion stack from scratch at every check. The
structural circuit encoding is a conservative extension (fresh Tseitin
variables and definitional clauses), so it is retained; what normally changes
between checks is which root literals are asserted. On the SMT-LIB path a
base-level assertion becomes a permanent unit clause; an assertion at a pushed
level has its root literal *assumed* per check-sat, so a pop retracts it by
simply no longer assuming it. Learned clauses therefore survive check-sats and
pops by construction, until an explicit relief/policy rebuild starts a fresh
backend epoch.

Usage
-----

Nothing needs to be enabled. Unless explicitly forced with ``--incremental``, a
session becomes incremental at its first explicit or internal assertion scope:
normally ``(push ...)``, while ``check-sat-assuming`` creates a temporary scope
itself. Ordinary sessions that create neither are entirely untouched and take
the classic single-shot pipeline. Two refinements to know about:

- The incremental driver engages from the *third* real solve of a
  session. The first two solves use the batch pipeline: two-check sessions
  cannot repay the cost of constructing a persistent encoding, while longer
  sessions can reuse it after engagement. ``check-sat`` calls made before the
  first explicit/internal scope still count toward this threshold.
  ``--incremental`` on the command line engages the driver from the first
  solve instead.
- Independent of the driver, the frontend keeps a per-level verdict
  cache with sound monotonicity shortcuts: pushing under a known-unsat
  level inherits unsat, a sat answer marks the levels beneath it sat, and
  a repeated check with an unchanged stack and no model demanded is not
  re-solved at all.

``(check-sat-assuming (l1 ... ln))`` is supported and implemented as an
internal assertion level holding the assumptions; the model it produces
remains readable by ``get-value``/``get-model`` afterwards, and the
assertion stack is left untouched. Per SMT-LIB, a model is invalidated by
``assert``, ``push``, ``pop`` and reset commands, and the model commands
refuse (``unsupported``) rather than answer from a stack that no longer
exists.

The C API takes the same route: a session becomes incremental at its
first ``vc_push`` (or from the first query with ``vc_setFlags(vc, 'i')``),
and from the third solve on, ``vc_query`` runs on the persistent driver.
``vc_query`` decides *asserts AND NOT query*, and the negated query is
appended as one more retractable level -- an assumption for exactly that
call, retracted by construction. The API's historical model contract is
untouched: the counterexample belongs to the last ``vc_query`` and
deliberately survives the idiomatic push/query/pop bracket (see the
documentation at those declarations); the driver fills the same
counterexample tables the batch path does. The Python bindings sit on the
C API and inherit all of this.

The whole input language is covered. Plain bit-vector assertions take the
lean path described below; arrays, ``--ackermanize``, floating point and
``--array-equality`` each add machinery of their own, also described
below.

The driver, in one page
-----------------------

The driver (``lib/Incremental/IncrementalSolver.cpp``) has no single
first-class record for a level and receives no direct ``push``/``pop``
notification. Each check-sat receives the assertion stack as one conjunction
per level; each level is split into its top-level conjuncts, and the active
preprocessing context and assumption set are reconstructed against permanent
caches. A few targeted structures now track level prefixes or liveness across
calls -- notably constant-bit propagation memos, promotion stability, and
active array-read reference counts -- but each manages its own lifetime.

The persistent encoding state includes:

- conjunct -> root literal (a conjunct is bit-blasted and Tseitin-encoded at
  most once per SAT-backend epoch),
- the session-long bit-blaster term memo and AIG manager,
- AIG node -> CNF variable for the current SAT-backend epoch.

A relief-valve or policy rebuild starts a new backend epoch: SAT variables and
root literals are rematerialized, while the semantic and AIG caches survive.

Reconstructing from the current snapshot is what lets ``push``/``pop`` need no
driver hooks: the parser's assertion stack is the source of truth, and a
popped assertion vanishes by not being present the next time. State that does
track a level compares the current conjunction with its saved prefix and
repairs or resets on divergence. The conjunction can also change when an
assertion is appended at the current depth, so depth alone is never a stable
identity.

Each check-sat runs on a worker thread with a large explicit stack.
Several passes walk formulas by recursion -- the per-conjunct
simplifier, substitution replace, the bit-blaster -- and parse-time
inlining of chained ``define-fun``\ s builds nodes tens of thousands of
levels deep out of flat input, deeper than a default-sized stack can
walk. The worker inherits the process's thread-local solver state
explicitly: it boots CONSTANTBV for itself and continues (then hands
back) the node uid counter, which caches keyed on node numbers rely
on.

Word-level rewriting is kept sound under retraction by construction
rather than by backtracking:

- Node-construction rewrites (the simplifying node factory) and constant
  evaluation are context-free and always on.
- Each new conjunct is simplified *on its own* (a fresh Simplifier whose
  substitution map is empty, so everything it does is a plain
  equivalence) before encoding.
- Substitutions are harvested from defining equations (``x = t`` with an
  occurs-check, unit booleans as true/false). **Base-level** definitions
  go into a persistent store: the base level only grows -- reset
  destroys the driver -- so that store is monotone and needs no
  backtracking; the defining equation itself stays asserted.
- **Pushed** definitions accumulate into a per-solve context BY LEVEL
  PREFIX: before a level is prepared, its own raw definitions join the
  map, so level L is substituted uniformly under the definitions of
  levels 1..L -- shared subterms keep rewriting identically, and a
  definition reaches its same-level uses -- but never under deeper
  levels' definitions. That last part keeps a conjunct's substituted
  form STABLE as the stack grows underneath it; a whole-stack map
  changed shallow conjuncts on every deepening, so one semantic array
  read took a fresh syntactic index per query and the refinement loop
  drowned in aliased read pairs. Floating-point definition bodies are
  allowed in (they are how FP-computed array indices ever fold), array
  content is refused, and a conjunct that DEFINES an entry is never
  rewritten under it: substituting ``x -> t`` into ``(= x t)`` yields
  TRUE and the constraint would silently vanish.
- Each substituted piece -- a moderate level as one formula, a huge
  level (the deep define-fun families) per conjunct, so pushed variants
  reuse every already-prepared sibling -- is totalised if it touches
  floating point and run through the batch equality-propagation and
  simplification passes as a TRIAL: the combination can explode the
  shared DAG on deep-chain families, so the result only replaces the
  piece if it stays within a size budget, and definitions too big to
  inline are never chained (the equation stays asserted and keeps its
  sharing). A level retracts atomically, so cross-conjunct rewriting
  inside it carries no retraction hazard. The preparation is cached
  keyed by the substituted piece; the base store is applied INSIDE the
  cache, where its permanence makes an older entry sound forever.
- Definitions the preparation harvests split two ways. A variable
  PRIVATE to its piece -- mentioned by no base conjunct, no other live
  level, at most one conjunct of its own level, and never bit-blasted --
  is genuinely **eliminated**: its equation leaves the formula, and its
  model value is produced by evaluating the recorded definition whenever
  a model is built while the level is live (the definitions are seeded
  into the model channel per solve, withdrawing the previous solve's
  seeds -- a stale seeding from a popped branch would shadow the live
  one and make every refinement candidate look bogus). Every other
  definition is re-conjoined and stays a real constraint: a variable
  whose bits already live in the solver keeps its equation (otherwise
  the existing bits would silently lose it -- sat where unsat lies that
  way), and so does anything shared between levels. The elimination is
  guarded against the future by screening: before anything is prepared
  or encoded, never-seen content has its symbols checked against the
  live eliminations, and a mention invalidates the cached preparation --
  it re-prepares with the variable now shared and the equation kept.

Cross-level constant-bit propagation
------------------------------------

The definition context only propagates equations of recognised forms. A
separate word-level constant-bit engine is fed the raw level conjunctions in
prefix order and can discover fixed Boolean/bit-vector symbols and interior
nodes across levels. Those fixings rewrite a level before preparation, cache
keying, and array transformation, so fixed array indices can collapse long
read-over-write chains before they are encoded.

The engine, its caller-side substitution/fact overlay, and its per-level
rewrite/fact memos persist across checks. A pop, changed level, or base growth
rolls the engine and caller overlay back to the longest common prefix, then
feeds only the replacement suffix; matching memo entries replay the rewritten
outputs produced under their original prefix. A fixing is never allowed to
erase the assertion from which it was derived: a level's own fixings are
deferred until deeper levels, and other adopted fixings bring an equivalent
pinning fact asserted at the adopting level. Conflicts are recorded as part of
the fed prefix so popping a contradictory level removes their effect.

``--incremental-cbp-reset`` retains the previous reset-and-prefix-re-feed
behavior as a diagnostic oracle. It is intended for differential validation,
not normal solving.

A pushed level holding many conjuncts is assumed through one *activation
literal* -- a fresh variable implying each conjunct's root -- so a level
costs one assumption however many assertions it carries, which keeps the
per-check assumption set (and the backend's assumption-analysis work)
proportional to the number of levels. The literal is cached on the
level's sorted root-literal set, not its formula: pushed-level
substitutions can make the same formula encode to different roots under
different live definitions, and the roots are what the literal must
imply. Its implication clauses count as live only while that activation
literal is assumed. If the activation is retired, both its implications and
the unit that pins it false remain in the backend, but are classified as dead
mass that a relief rebuild may reclaim.

Arrays
------

Array reads are abstracted through the batch ``ArrayTransformer`` with
its read registry seeded from a persistent copy, so every
``(array, index)`` pair keeps one canonical abstraction variable for the
session. That canonicity is what lets refinement work incrementally: the
lazy CEGAR loop is the batch pipeline's own (driven through a small
``ToSATBase`` adapter that re-solves under the check-sat's assumptions),
and the congruence axioms it learns are added as *permanent* clauses --
they are tautologies of the canonical abstraction, valid whichever levels
are live. For growth accounting they are nevertheless charged to the
deterministic active conjunction that caused them to be emitted. That owner
classification keeps a repeated live query from triggering rebuilds while
allowing lemmas associated only with popped query shapes to become reclaimable
mass. The driver's loop also carries a guard the batch pipeline never
needed: a round that rejects the candidate model while finding no
congruence axiom to add cannot be repaired by refinement -- it means the
encoding and the word-level evaluation disagree somewhere -- and dies as
a ``FatalError`` naming that, where a silent loop would spin at full
speed forever. A popped read's registry entry stays behind as an unconstrained
observation of the array, which restricts nothing: an array maps every
index to some value.

Under ``--ackermanize`` arrays are compiled away eagerly instead: each
new read becomes a nested if-then-else over the reads already seen. That
new-versus-existing shape is naturally monotone, so persisting the
per-array read lists keeps pair coverage across check-sats, and there is
nothing left to refine. The frontend does clear the batch array-transformer
tables before every solve, however. After a satisfiable eager round in which a
model can be observed, the driver therefore rematerializes the active read rows
even when every encoding was a cache hit. This restores the source-level read
observations needed by deferred ``get-model``/``get-value`` construction and
``--check-sanity``; it does not add constraints or repeat Ackermannisation.

Floating point
--------------

Floating-point conjuncts are totalised and lowered through one
session-long encoding context, so symfpu circuits for terms the rounds
share are built once. Per-conjunct preparation is sound because the
totaliser re-collects every side condition -- rounding-mode pinning in
particular -- from each call's own output and conjoins it onto that
result: a conjunct's lowered form carries its own conditions and retracts
with its level, while the persistent caches hold only term rewrites.

Whole-array equality
--------------------

``--array-equality`` rounds run as one *extensionality block* per
check-sat: the whole active stack is lowered, prepared and transformed on
a fresh registry -- the extensionality procedure reasons about the
complete array graph of a solve, and its records are solve-local by
design -- then encoded and assumed as a single root literal on the
persistent solver, with the consistency checker's lemmas encoded into the
live solver mid-round.

Even these per-round blocks cache: every variable a round generates
(equality proxies, witness indices and values, scalar names, read
abstractions) is named deterministically by *what it stands for* (its key
nodes) rather than by a counter, so an identical re-pushed stack lowers
to the identical node and reuses the previous round's encoding outright,
while a changed stack still shares every unchanged subcircuit. One
subtlety makes this work: STP garbage-collects unreferenced interior
nodes and re-mints their numbers, and the deterministic names are keyed
on node numbers -- so the driver pins each round's node spine, and in
general any cache in STP that keys on nodes must *hold* them.

The deterministic block node participates in the same live-cone accounting as
ordinary formula roots. Extensionality still differs semantically -- its block
represents the complete active array graph -- but it does not have a separate
relief-valve approximation.

Live-cone accounting
--------------------

A newly submitted clause delta for one formula key is an inexpensive live-size
estimate, but it is not exact. A current root -- ordinary or extensionality --
can reuse most of an AIG cone first encoded for an earlier, now-popped key. The
driver therefore records the actual AIG root for every encoded formula and can
count the unique structural union reachable from all permanent roots and the
current assumed roots. The exact non-structural share is added separately:
permanent root units, currently assumed activation implications, and
owner-keyed theory-refinement clauses.

Normal solving does not collect an ordinary root vector or walk a cone below
the configured re-encoding variable floor. Once that floor is crossed, each
solve replaces one pending snapshot with its latest normalized current roots,
the permanent-root prefix, and the non-structural mass. If the cheap
retained/peak ratio would authorize relief before the next solve, one exact
union walk first repairs the epoch's peak live mass and the ratio is tested
again. Retaining only the latest snapshot avoids quadratic root-vector history;
popped historical stacks are deliberately allowed to become reclaimable.
``--incremental-profile`` instead opts into the exact union measurement on
every solve.

Theory-lemma ownership remains an intentional policy approximation: a lemma is
charged to the deterministic query that emitted it even though it may later
help a different live query. Missing that cross-owner usefulness can cause an
unnecessary rebuild, but cannot change an answer. Clause counters are 64-bit;
the common submission counter would wrap after ``2^64`` submissions, which is
a theoretical rather than practical session limit.

SAT backends
------------

The normal retraction mechanism is solving under assumptions, which every
wrapped backend except the simplifying MiniSat supports natively; that
one is substituted with plain MiniSat under incremental use, since its
variable elimination cannot accept later clauses over eliminated
variables (the same gate cvc5 applies to SatELite). CryptoMiniSat and
CaDiCaL eliminate variables internally but restore them the moment a new
clause mentions them, which is what makes adding refinement lemmas
between solves safe. When CaDiCaL is compiled in it is the default
backend.

CaDiCaL's bounded variable addition (``--cadical-factor``) follows the
batch pipeline's policy on the persistent solver too: an explicit ON
always asks, AUTO asks for array sessions, and the decision has to land
in the backend's configuration window, which closes at its first clause
-- the start of the first engaged check-sat, and again right after a
relief-valve rebuild, whose fresh solver reopens the window. With factor
on, clause literals, *assumption literals* and model lookups all travel
through the wrapper's declared-variable translation table; assumptions
are how every retractable formula is asserted here, so a literal that
skipped the translation would silently constrain nothing. The
``query-files-cadical-factor`` suite sweep re-runs every behavioural
test, the incremental ones included, with factor forced on.

CaDiCaL's probe-based inprocessing re-runs over the whole persistent
encoding at every solve, so on many-solve sessions its recurring cost
can dominate what it earns (measured at half the total runtime on
generated variant-push floating-point corpora), while a session that is
one or two big searches genuinely profits from it.
``--incremental-inprobing`` controls the driver's policy: ``auto`` (the
default) retires it once a session has both shed trail reuse -- the
still-riding-the-trail shape is the many-small-queries workload whose
accumulated search state a restart would waste on a technique that
measures neutral there -- and run enough solves, via one bounded rebuild
onto a fresh solver configured without it (the option, like factor and
trail reuse, only takes inside the backend's configuration window);
``off`` retires from the first driver solve; ``on`` never retires.
Backends without the option simply never retire.

Resource budgets are re-armed per check-sat rather than measured from the
persistent solver's birth. The time deadline spans all refinement solves in
that check. Conflict-budget sharing is backend-dependent: CryptoMiniSat and
the MiniSat-style counters can account for what earlier refinement calls used;
CaDiCaL exposes no cumulative consumed-conflict count, so each internal
``solve`` receives the configured conflict limit again.

Testing and measurement
-----------------------

``tests/query-files/incremental-tests/`` holds the behavioural tests:
push/pop rounds, models under retraction, substitution soundness (the
freeze rule has a dedicated test that fails as sat-on-unsat without it),
arrays with refinement across rounds, eager Ackermannisation, floating
point, the extensionality block and its cache, and the driver's own
reuse counters (run with ``-s``, the driver reports how much each check
encoded -- a repeat check must report zero). Eager-array coverage includes an
all-cache-hit second model and sanity checking. The relief-valve cases include
forced extensionality churn that must rebuild soundly, negative checks on every
round of a monotonically growing live extensionality stack, and an ordinary
root built mostly from AIG cones first introduced by popped formulas. Neither
live shape may be mistaken for dead churn.

At implementation closeout through ``9cb7b34b``, the complete configured
RelWithDebInfo suites passed with CaDiCaL and floating point (115/115), MiniSat
and floating point (114/114), and MiniSat without floating point (86/86). These
configured-suite results do not replace the outstanding external-corpus
campaign.

``--incremental-profile`` enables a lower-noise profile for each invocation of
the incremental driver. Pair it with ``--incremental`` to route the first
check through that driver; the profile flag observes incremental work but does
not itself change solver engagement. This is currently a command-line
diagnostic rather than a C API option. Each invocation writes four keyed
records to stderr (the per-check phase, work, and CBP/backend records followed
by additive session totals), while SMT-LIB answers remain on stdout.

The profile reports stack and cache work, including CBP divergences,
rollbacks, discarded levels and state entries, fresh and re-fed levels, their
bounded DAG-node mass, reset-oracle/fallback rebuilds, rewrite replay, and
adoption attempts. It also covers semantic construction, preparation, actual
bit-blast/CNF encoding, active-read seeding, backend rebuilds, initial and
refinement SAT calls, and rolling session totals. Durations accumulate at
nanosecond precision and are emitted as whole microseconds, so repeated short
operations are retained in the cumulative values. It is deliberately separate
from ``-s``: verbose diagnostics from individual passes would otherwise
distort the phases being measured. Deterministic work counters are suitable
for regression tests; elapsed values are measurements, not test expectations.

The named sub-phase timings overlap their enclosing phase. On the ordinary
equality-free route, ``semantic-us`` includes CBP synchronization, rollback,
fresh and reset-mode re-fed CBP work, preparation and encoding; the
whole-array-equality route is
instead enclosed by ``extensionality-us``. ``refinement-us`` includes its SAT
re-solves. ``rebuild-reset-us`` measures backend replacement and base
re-simplification; the subsequent live-stack re-encoding is reported under
``encode-us``. ``total-us`` begins immediately before the driver's large-stack
worker is launched, but does not include frontend assertion snapshot
construction, checks answered from the frontend cache or batch path, or a
model materialized lazily after the solve.

Clause counters have deliberately different lifetimes and meanings:

- ``driver-clauses`` is the number of clauses submitted through STP's
  backend-neutral SAT interface: the current check's delta on a per-check
  record, and the cumulative driver-lifetime total on the session record. It
  includes structural, activation, unit, extensionality and theory-refinement
  submissions. The lifetime total is carried across backend rebuilds.
- ``refinement-clauses`` is the subset of ``driver-clauses`` emitted by lazy
  array or extensionality checking/refinement. It is a classification, not an
  additional total.
- ``retained-clauses`` is the exact number submitted to the *current* SAT
  backend epoch. It comes from the common ``SATSolver`` facade, so theory code
  that only holds a generic solver reference cannot bypass it. It can fall
  when a rebuild replaces the backend and does not try to mirror clauses a
  backend has internally simplified away.
- ``live-clauses`` is the current solve's ownership estimate and
  ``peak-live-clauses`` is its high-water mark in the current backend epoch.
  The inexpensive normal-path value uses formula-key submission deltas; the
  profiler measures the exact live AIG union, and the relief valve performs the
  same exact walk on its latest pending snapshot before a cheap estimate may
  authorize rebuilding. Permanent units, active activation implications, and
  owner-keyed theory lemmas are added separately. Retired activation
  implications and pins remain retained but dead. All live values are capped
  by the retained total.

``scripts/incremental-bench.py`` retains its legacy single-solver mode, but a
closeout campaign should use paired ``--solver-a``/``--solver-b`` mode. It
records every ``sat``, ``unsat`` and ``unknown`` answer, including the answer
prefix produced before a timeout, and gives each pair one of three verdicts:

- ``FULL_OK``: both processes completed successfully with identical complete
  answer sequences;
- ``PREFIX_ONLY_INCONCLUSIVE``: their common prefix agrees, but at least one
  process did not complete successfully; this is not a correctness success;
- ``DISAGREEMENT``: the common prefix differs, or two completed processes
  produced different sequence lengths.

The harness deterministically balances AB/BA execution order by file and run,
flushes each complete pair, and supports identity-checked ``--resume`` plus
reproducible manifests and shards. Sidecar metadata fingerprints each solver's
binary hash, arguments, embedded revision and build options, dynamic-library
listing, and linked ``libstp`` hash; it also refuses to resume against changed
identity or finish after an arm changes underneath the run. Outliers,
timeouts, and non-``FULL_OK`` results receive a longer revalidation run unless
that phase is explicitly deferred. The main soundness instrument during
development remains answer-sequence differential testing between the batch
and incremental engines: they must agree on every answer they both produce,
and only complete identical streams count as a full success.

``scripts/incremental-bench-report.py`` validates and combines the resulting
shards. For example::

  scripts/incremental-bench-report.py \
    --main '/results/final/main-shard-*.csv' \
    --revalidation '/results/final/revalidation-shard-*.csv' \
    --expected-manifest /results/corpus.manifest --expected-runs 3 \
    --expected-answers 1865826 \
    --output-prefix /results/final/report --require-full-ok

The reporter checks the schema, sidecar manifests, solver identities, and
unique ``(file, run)`` keys. A revalidation manifest replaces every main row
for each selected file, so an interrupted revalidation is reported as missing
rather than falling back to a shorter run. Any disagreement ever observed is
kept as a sticky failure and retained with its complete answer streams in the
``.disagreements.csv`` evidence file. The other outputs contain the effective
combined rows, per-file median timing classifications, correctness and process
status counts, answer totals, and logic/family breakdowns.

``--expected-answers`` requires an exact total for each arm, making answer
prefixes lost to common timeouts or crashes visible even when both processes
stopped at the same point.

Limitations
-----------

- The persistent encoding grows monotonically, and the relief valve is
  coarse: once the solver's variable count passes
  ``--incremental-reencode-limit`` (default one million; 0 disables) and
  the current backend's retained clause submissions substantially exceed the
  peak owned by a live working set, the solver is rebuilt from the live stack.
  Formula-key deltas provide the cheap structural estimate; before that
  estimate may trigger relief, the lazy guard repairs it from the unique union
  of permanent and current AIG cones for both ordinary and extensionality
  paths. Base/promoted units are permanently live for the epoch, activation
  implications are live only while assumed, and theory lemmas are charged to
  their originating active conjunction.
  Semantic stores survive and active content re-encodes through the bit-blast
  memo, but learned clauses and refinement axioms start over. The rebuild
  boundary is also the one
  place a GLOBAL simplification pass over the base is both sound and
  free -- everything re-encodes anyway, and the base never retracts --
  so the driver runs the batch equality-propagation, simplification and
  unconstrained-variable passes over the whole base conjunction there
  (symbols of live pushed levels held untouchable, arrays excluded).
  Definitions it eliminates are permanent, replay into models by
  evaluation, and are restored as permanent units the moment later
  content mentions their variable: an implied equation returns as
  itself, while a variable dropped as unconstrained gets its ORIGINAL
  conjuncts back -- its recorded definition is only a witness the model
  replay uses, and asserting it would wrongly pin the variable. The finer-grained alternative (pinning
  popped variables away from the decision heuristics, as cvc5's CaDiCaL
  propagator integration does) requires the propagator interface and is
  not portable across our backends.
- Extensionality rounds rebuild the procedure's solve-local records each
  check-sat; reuse for them is at the encoding level (cached blocks and
  shared subcircuits), not at the record level.
- Forcing the driver from the first solve (``--incremental``) on a large
  all-new formula deliberately trades the batch pipeline's global
  simplification for encoding reuse that cannot pay off yet; the default
  engagement policy exists precisely because of this.

Maintainer architecture review
------------------------------

``INCREMENTAL-SOLVING-REVIEW.md`` records the branch-versus-master review,
comparisons with Bitwuzla, cvc5, and Z3, the state-lifetime audit, open risks,
and the recommended instrumentation/CBP-undo/assertion-journal roadmap.
