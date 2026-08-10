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

- Automatic engagement is theory-specific. Pure ``QF_BV`` and ``QF_ABV``
  sessions engage the incremental driver from their *32nd* real solve; a
  targeted sweep found that their early checks benefit more from the batch
  pipeline's whole-formula simplification. Floating-point and other or
  unknown logics retain engagement from the *third* real solve. ``check-sat``
  calls made before the first explicit/internal scope still count toward the
  threshold. ``--incremental`` engages the driver from the first solve.
  ``--incremental-auto-engage-at=N`` is a diagnostic override: ``-1`` selects
  the theory policy, ``1`` engages on the first real solve, positive values
  name the solve ordinal, and ``0`` prevents automatic driver engagement
  while leaving the frontend verdict cache active. Explicit ``--incremental``
  takes precedence.
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
and from the third solve on, ``vc_query`` runs on the persistent driver. The
native API has no SMT-LIB2 ``set-logic`` declaration, so it retains that
theory-neutral threshold.
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

Those pinning facts also participate in private-definition liveness. CBP can
replace an opaque Boolean shell while retaining that shell as a fact; a symbol
used by the fact must therefore keep its defining equation in the SAT formula.
Symbols in replayed facts, newly emitted facts, and domains eligible to emit a
fact are protected before private-definition elimination. If a cached prepared
piece eliminated a symbol that has since become protected, the entry is
invalidated and prepared again. Protecting eligible domains up front covers a
fact discovered by a later piece in the same level.

Cache hits revalidate every eliminated definition against the complete live
scope, not only against CBP facts. Raw nodes are screened once when first seen,
so an elimination cache entry can be created after a conflicting node was
popped and screened; re-pushing that node must still retire the now-non-private
entry.

``--incremental-cbp-reset`` retains the previous reset-and-prefix-re-feed
behavior as a diagnostic oracle. It is intended for differential validation,
not normal solving.

When ``--incremental`` explicitly engages the driver on the first real solve,
there is not yet a CBP prefix to reuse. If the sum of the assertion-level DAGs
exceeds ``--incremental-cbp-bootstrap-limit`` (100,000 nodes by default), that
first solve skips only this cross-level prepass. A later real solve builds CBP
from the complete then-live stack in the normal way, so no persistent fact or
future reuse is lost. Automatic sessions do not take this path: their first two
solves use the batch pipeline and CBP starts normally when the driver engages
on the third. Set the limit to 0 to disable the deferral.

Explicit first engagement also recovers one cheap, high-yield part of batch
preprocessing for a base-only, array/FP-free formula: before emitting any
permanent clauses, it runs pure-literal elimination over the complete base.
The selected Boolean values are model witnesses rather than logical
consequences. They replay into a model while unused; if later content mentions
one of those symbols, the driver restores the original base conjuncts as
permanent units and lets the new constraints choose the value. Shared witness
conjuncts are restored only once per backend epoch. This deliberately does not
repeat after the first solve and does not rewrite pushed levels: it targets the
large first-check Boolean-clause families without reviving recurring global
base preprocessing, which previously forfeited persistent roots and regressed
changing-stack sessions. Automatic third-solve engagement has already run two
whole-formula batch passes and therefore does not take this special path.

A multi-level, plain-BV first stack gets a separate guarded opportunity to
recover cross-level batch simplification. The complete active stack is run
through the same constant-bit/equality/unconstrained/pure-literal prefix used
by exact-stack array-equality rounds. The result is adopted only if the input
has at least 128 DAG nodes and the trial at least halves it; then the reduced
formula rides as one assumption-scoped block, including the base, so a deeper
fact may safely collapse a shallow root without leaking through a later pop.
A rejected trial commits neither clauses nor model definitions and execution
continues through the ordinary per-level driver. The next changed check also
uses that ordinary path and materializes the raw base normally; the provisional
block remains retracted. Once an array-free block is encoded, it is solved
directly under that assumption: no refinement adapter or eager counterexample
is needed, and a requested model is materialized by its first reader just as it
is on the ordinary plain-BV path. Array-equality blocks retain the candidate-
model/refinement route. ``check-sat-assuming`` retains its individual roots for
unsat-assumption reporting, arrays and floating point retain their own routes,
and an explicitly aggressive ``--incremental-reencode-limit`` below the default
one million disables the provisional block so relief ownership is available
from the outset (zero, which disables relief, still permits it). Automatic
third-solve engagement again does not need this first-check escape.

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

Under automatic engagement, the first distinct persistent exact-stack block
keeps its raw word-level shape: that session has already received two batch
solves, and the raw shape can be a useful search strategy on write-heavy array
graphs. A session explicitly forced incremental from its first solve has no
batch preprocessing to fall back on, so its first block -- and every genuinely
new later stack in either mode -- receives the high-yield prefix of the batch
size-reducing pipeline (constant-bit propagation, equality propagation,
unconstrained elimination and pure literals) before array transformation.
This is safe here because the result and every definition it eliminates have
exactly the assumption lifetime of the complete-stack block; ordinary
per-level roots still never see facts from deeper scopes. The choice is cached
per raw active conjunction, so repeating or re-pushing a stack recreates the
same transformed root and reuses its encoding and lemmas instead of
alternating between raw and simplified forms. If a scoped elimination reuses
a symbol whose bits were created by an older block, model construction
withdraws those inactive SAT bits and evaluates the current definition.

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
measures neutral there -- run enough solves, and kept its permanent base
fixed throughout that window. A base which is still growing gives
inprocessing new clauses to simplify and is not a recurring-rescan workload.
Retirement uses one bounded rebuild onto a fresh solver configured without
it (the option, like factor and trail reuse, only takes inside the backend's
configuration window);
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

At implementation closeout through ``ee8685bb``, the complete configured
RelWithDebInfo suites passed with CaDiCaL and floating point (116/116), MiniSat
and floating point (115/115), and MiniSat without floating point (87/87). These
configured-suite results are complemented by the frozen external-corpus
reconciliation below.

The initial closeout reconnaissance invalidated its frozen ``9cb7b34b``
candidate and was stopped at the first answer disagreement. On
``QF_FP/schanda/spark/precise.smt2``, master answered unsat in all four scopes,
while the candidate answered sat in the third; ``--check-sanity`` confirmed
that its model violated the asserted result equality. The cause was the CBP
fact/private-definition interaction described above: preparation eliminated
``result`` from its defining equation before a later pinning fact made the
symbol live, leaving the fact disconnected from the floating-point operation.
The narrow protection and cache-invalidation fix is covered by
``cbp-fact-private-definition.smt2`` in default, forced-incremental,
reset-oracle, and memo-replay modes. The stopped campaign's partial rows are
diagnostic evidence only. They were discarded and the campaign was restarted
with a freshly frozen candidate containing both privacy fixes.

Frozen closeout reconciliation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The restarted closeout campaign compared master
``34f69be1989910fd053008715de4b65c095fd770`` with candidate
``e5a26c30f83b2cd9cc0ccb274b62f210865023cd``. The latter is the
``ee8685bb`` implementation plus documentation only. Both were frozen Release
builds using CaDiCaL 3.0.1, floating-point support, shared libraries, and the
system allocator. The master and candidate executable SHA-256 values were,
respectively, ``6f03a9edbbbfe6db2918ca9a36e6f2fd3903f5061e6a520db0c489f19212517a``
and ``2c9186d98aa55df055d751e3ea3b40d7f3d13f248b19789fea1ab57d2bbdb8ce``;
their linked ``libstp`` hashes were
``0f063a88125c10070b403e2d107e25b9b0cb9177c8aa22b95decff6bc4553a6b``
and ``84a36b4f447ab47ca97f2ea60b03cfe5628a65cef9f722b4d2a9bef7ab17e03f``.

The corpus contained 22,999 sorted, unique files totalling 20,308,257,767
bytes. Every file was checked against a content ledger. The corpus-manifest
SHA-256 was
``cd1310ebac50f4d35c837df0a01e6f8ffe020c3e6df1a8f8b03d13a9bbf784d7``
and the content-ledger SHA-256 was
``7c0fca20fc75e5cd7506b0e225621d17aa20dc98e087b28f159f0dd40f4d98db``.
A 36-pair smoke phase and its nine selected longer reruns were all
``FULL_OK`` before the full pass began.

The reconciliation ran each file once with a 30-second limit. It selected 518
files for an authoritative 120-second rerun. Coverage was exact: all 22,999
effective ``(file, run)`` pairs and all 518 selected reruns were present, and
no disagreement was observed in either phase. After replacement by the longer
rows, 22,765 files were ``FULL_OK`` and 234 were
``PREFIX_ONLY_INCONCLUSIVE``. The latter comprised 21 shared ``exit-11``
rows, 155 shared timeouts, 17 master-``ok``/candidate-timeout rows, and 41
master-timeout/candidate-``ok`` rows. Their answer prefixes agreed, but they
remain inconclusive rather than correctness successes. The effective streams
retained 607,747 master and 607,180 candidate answers out of the structural
621,942 per arm; the incomplete rows account for the shortfall.

The original ``precise.smt2`` oracle was also clean in the frozen campaign:
both master and candidate completed with ``unsat`` in all four scopes. Thus
the restarted corpus reconciliation found no recurrence of the CBP/private-
definition soundness bug. A separate three-run performance campaign is in
progress; the one-run reconciliation is correctness evidence and should not
be used for quantitative timing conclusions.

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
adoption attempts. ``ext-preprocesses`` and ``ext-eliminations`` identify
exact-stack blocks which took the scoped batch-prefix pass and the model
definitions it produced; ``base-preprocesses`` and ``base-eliminations``
identify the explicitly forced, base-only pure-literal pass and its model
witnesses. ``first-stack-preprocesses`` and ``first-stack-eliminations``
identify an adopted multi-level BV block, while ``first-stack-rejected``
records a trial which fell back without committing it. The profile also covers semantic construction,
preparation, actual bit-blast/CNF encoding, active-read seeding, backend
rebuilds, initial and refinement SAT calls, and rolling session totals.
Durations accumulate at nanosecond precision and are emitted as whole
microseconds, so repeated short operations are retained in the cumulative
values. It is deliberately separate from ``-s``: verbose diagnostics from
individual passes would otherwise
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
closeout campaign uses paired ``--solver-a``/``--solver-b`` mode. It
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
    --main '/results/final/main-shard-[0-9][0-9].csv' \
    --revalidation '/results/final/main-shard-[0-9][0-9].revalidation.csv' \
    --expected-manifest /results/corpus.manifest --expected-runs 3 \
    --expected-answers 1865826 \
    --output-prefix /results/final/report --require-full-ok

The reporter checks the schema, sidecar manifests, solver identities, phase
provenance, and unique ``(file, run)`` keys. The main phase's
``.revalidate.manifest`` artifacts select replacement files independently of
whether their revalidation CSVs were created. Every main row for those files
is removed, so an interrupted revalidation is reported as missing rather than
falling back to a shorter run. Any disagreement ever observed is kept as a
sticky failure and retained with its complete answer streams in the
``.disagreements.csv`` evidence file. The other outputs contain the effective
combined rows, per-file median timing classifications, correctness and process
status counts, answer totals, and logic/family breakdowns.

``--expected-answers`` requires an exact total for each arm, making answer
prefixes lost to common timeouts or crashes visible even when both processes
stopped at the same point. ``--require-full-ok`` is appropriate for a strict
all-complete campaign. Omit it when intentionally retaining shared failures
or timeouts for classification; expected-answer shortfalls will still make the
reporter return failure after it writes the evidence files. Keep main and
revalidation globs phase-specific: a broad ``main-shard-*.csv`` also matches
``.revalidation.csv`` files in this layout and is rejected as a phase mismatch.

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
  simplification for encoding reuse that cannot pay off yet. The large-CBP
  bootstrap deferral removes one measured prepass cost, and the base-only
  pure-literal pass recovers Boolean-clause collapses. The guarded plain-BV
  exact-stack path additionally recovers large cross-level collapses, but only
  when the complete trial at least halves: arrays, FP, modest rewrites and
  subsequent changing stacks still cannot reproduce the whole batch pipeline
  without forfeiting the persistent per-level roots. The default engagement
  policy remains the general answer to that structural difference.

Maintainer architecture review
------------------------------

``INCREMENTAL-SOLVING-REVIEW.md`` records the branch-versus-master review,
comparisons with Bitwuzla, cvc5, and Z3, the state-lifetime audit, open risks,
and the recommended instrumentation/CBP-undo/assertion-journal roadmap.
