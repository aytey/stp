Incremental solving
===================

STP solves incremental SMT-LIB2 sessions -- ``push``, ``pop``, repeated
``(check-sat)``, ``(check-sat-assuming ...)`` -- by keeping one SAT solver
and one bit-blasted encoding alive for the whole session, instead of
re-solving the conjoined assertion stack from scratch at every check.
Everything that is encoded is a conservative extension (fresh Tseitin
variables and definitional clauses), so it is never retracted; what changes
between checks is only which root literals are asserted. A base-level
assertion becomes a permanent unit clause; an assertion at a pushed level
has its root literal *assumed* per check-sat, so a pop retracts it by
simply no longer assuming it. Learned clauses therefore survive both
check-sats and pops by construction.

Usage
-----

Nothing needs to be enabled. A session becomes incremental at its first
``(push ...)``; sessions that never push are entirely untouched and take
the classic single-shot pipeline. Two refinements to know about:

- The incremental driver engages from the *second* real solve of a
  session. The first solve carries the largest all-new formula -- for
  single-check-sat files that happen to use ``push``, the only formula --
  and the batch pipeline's whole-formula simplification earns its keep
  there; encoding reuse can only pay off once a second solve exists.
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
and from the second solve on, ``vc_query`` runs on the persistent driver.
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

The driver (``lib/Incremental/IncrementalSolver.cpp``) holds **no
per-level state**. Each check-sat receives the assertion stack as one
conjunction per level; each level is split into its top-level conjuncts,
and the assumption set is recomputed from scratch against permanent
caches:

- conjunct -> root literal (the encoding cache; a conjunct is bit-blasted
  and Tseitin-encoded at most once per session),
- the bit-blaster's term memo and one AIG manager,
- AIG node -> CNF variable.

Recomputing rather than tracking levels is what makes ``push``/``pop``
need no hooks at all: the parser's assertion stack is the single source
of truth, and a popped assertion vanishes by not being present the next
time. It also sidesteps a subtle trap: the per-level conjunction nodes
are re-collapsed and re-simplified by the node factory on every check, so
any state keyed by *level* rather than by *formula* would chase a moving
target.

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

A pushed level holding many conjuncts is assumed through one *activation
literal* -- a fresh variable implying each conjunct's root -- so a level
costs one assumption however many assertions it carries, which keeps the
per-check assumption set (and the backend's assumption-analysis work)
proportional to the number of levels. The literal is cached on the
level's sorted root-literal set, not its formula: pushed-level
substitutions can make the same formula encode to different roots under
different live definitions, and the roots are what the literal must
imply.

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
are live. The driver's loop also carries a guard the batch pipeline never
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
nothing left to refine.

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

SAT backends
------------

The one retraction mechanism is solving under assumptions, which every
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

Resource budgets are per check-sat: a conflict or time budget is re-armed
at each check, measured from the arming point, and the check's refinement
iterations share it -- on a long-lived solver, budgets measured from the
solver's birth would shrink to nothing, which is pinned by a regression
test.

Testing and measurement
-----------------------

``tests/query-files/incremental-tests/`` holds the behavioural tests:
push/pop rounds, models under retraction, substitution soundness (the
freeze rule has a dedicated test that fails as sat-on-unsat without it),
arrays with refinement across rounds, eager Ackermannisation, floating
point, the extensionality block and its cache, and the driver's own
reuse counters (run with ``-s``, the driver reports how much each check
encoded -- a repeat check must report zero).

``scripts/incremental-bench.py`` times a solver over a corpus, records
each file's answer sequence, and diffs a later run against a saved
baseline -- so a change can be checked for performance and, more
importantly, for answer agreement. The main soundness instrument during
development was differential testing between the batch and incremental
engines over SMT-LIB incremental benchmarks: the two must agree on every
answer of every file.

Limitations
-----------

- The persistent encoding grows monotonically, and the relief valve is
  coarse: once the solver's variable count passes
  ``--incremental-reencode-limit`` (default one million; 0 disables) and
  most encodings belong to popped, never-returning content, the solver is
  rebuilt from the live stack -- semantic stores survive and active
  content re-encodes through the bit-blast memo, but learned clauses and
  refinement axioms start over. The rebuild boundary is also the one
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
