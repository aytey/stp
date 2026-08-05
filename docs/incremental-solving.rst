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

Word-level rewriting is kept sound under retraction by construction
rather than by backtracking:

- Node-construction rewrites (the simplifying node factory) and constant
  evaluation are context-free and always on.
- Each new conjunct is simplified *on its own* (a fresh Simplifier whose
  substitution map is empty, so everything it does is a plain
  equivalence) before encoding.
- Substitutions are harvested from defining equations (``x = t`` with an
  occurs-check, unit booleans as true/false) at every level, but stored
  and applied differently by level. **Base-level** definitions go into a
  persistent store: the base level only grows -- reset destroys the
  driver -- so that store is monotone and needs no backtracking.
  **Pushed-level** definitions are windowed per check-sat: each call
  collects them from the levels live *that call* and rewrites deeper
  conjuncts under them, caching the rewritten conjunct's encoding (keyed
  by the rewritten node, so the same conjunct under different live
  definitions encodes separately and a re-pushed stack hits its cache).
  In both cases a defining equation may only be simplified away under its
  own substitution if the variable has never reached the SAT solver; a
  variable whose bits already live in the solver keeps its equation as a
  real constraint (otherwise the existing bits would silently lose it --
  sat where unsat lies that way). A variable eliminated before it was
  ever encoded gets its model value by evaluating its definition.

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
are live. A popped read's registry entry stays behind as an unconstrained
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
  refinement axioms start over. The finer-grained alternative (pinning
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
