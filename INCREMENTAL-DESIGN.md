# Incremental solving for STP — architecture review and plan

*Status 2026-08-04: phases 0–4 are implemented on this branch
(`incremental-solving`), one commit per phase. Phase 1 shipped the
persistent SAT solver + persistent AIG/Tseitin encoding behind assumptions,
with the driver engaging from the second solve of a session; phase 2 the
base-level substitutions (with the freeze rule and model seeding) and
per-conjunct simplification; phase 3 arrays via the seeded persistent read
registry and the batch CEGAR driven through a ToSATBase adapter; phase 4
floating point over a session-long FpEncodingContext. Two follow-on phases
closed the remaining fallbacks: --ackermanize runs in-driver (the eager
per-array read lists persist; the new-versus-existing ITE shape is
monotone), and whole-array equality runs as a per-round extensionality
block on the persistent solver -- the whole active set lowered, prepared
and assumed as one root, with checker lemmas encoded into the live solver;
its registry and witnesses stay solve-local by design, so reuse for those
rounds is at the shared-subcircuit level. Phase 5 (fuzzing, differential
campaigns, perf polish) is future work.*

*Prepared 2026-08-04 against STP master @ f9dea0cc. Comparative material from reading
cvc5 (`/home/avj/clones/cvc5/main` @ e8c0387cae), Bitwuzla (`/home/avj/clones/bitwuzla/main`
@ e92a4c51), and z3 (`/home/avj/clones/z3/master`). Background: stp/stp#483.
Benchmarks: `/home/avj/clones/stp/incremental` (QF_BV 2611, QF_ABV 1272, QF_FP 166,
QF_ABVFP 18429 files; typical file: ~200 rounds of push / assert / check-sat / pop —
BMC and k-induction workloads with a monotonically growing common prefix and a small
popped tail).*

This is a plan, not an implementation. Every STP claim below was verified against the
tree; foreign-solver claims carry file:line pointers into the respective checkouts.

---

## 0. Summary

STP's frontend is already level-aware: `Cpp_interface` keeps per-level frames for
symbols/functions/sort-aliases, a per-level result cache with sound monotonicity
shortcuts, and `STPMgr::_asserts` is a real per-level assertion stack. **The backend
then destroys all of it**: `checkSat` conjoins every level into one AND node, wipes
every derived table, runs the whole destructive simplification pipeline over the
conjunction, bit-blasts into a stack-local object, and creates *and deletes* a fresh
SAT solver per check-sat. The only work reused across check-sats today is the
sat/unsat verdict cache. This is precisely what issue #483 observed ("no performance
improvement from push/pop; are learned lemmas reused?" — answer today: no, never).

All three reference solvers converge on the same architecture, which STP can adopt
without rewriting its batch pipeline:

1. **A level-tagged, append-only assertion store consumed through monotone cursors**
   ("qhead"); pop truncates the store and rewinds cursors; lower levels are never
   re-preprocessed.
2. **A permanent/contextual split in the encoding**: term→AIG, AIG→CNF, node→SAT-var
   maps and all Tseitin/definitional clauses are conservative extensions — kept
   forever; only the *unit assertion* of each formula's root literal is
   context-dependent (level 0 ⇒ permanent unit; level>0 ⇒ SAT **assumption**).
   Learned clauses then survive push/pop for free.
3. **A rewrite-rule policy with three classes**: node-local rewrites stay on
   unconditionally; per-assertion normalization runs once per new assertion;
   cross-assertion global passes are either windowed (substitutions flow forward
   only, with a first-seen-in-this-batch elimination rule) or hard-gated off in
   incremental mode — every reference solver gates some passes rather than
   weakening them.
4. **A two-driver strategy**: the existing batch pipeline is kept intact for
   single-query use; an incremental driver is selected on first `(push)` (exactly
   z3's `combined_solver` policy). Batch/SMT-COMP performance is not put at risk.

The recommended order of work: Phase 1 (persistent SAT + persistent bit-blast/CNF +
assumptions, global simplification bypassed) already delivers the learned-lemma reuse
issue #483 asks for, on a small diff. Rewrite-rule incrementality (Phase 2) and
arrays (Phase 3) follow independently.

---

## 1. What STP does today (verified, with anchors)

### 1.1 The frontend is level-aware

- Three stacks in lockstep (`lib/Interface/cpp_interface.cpp:42-46`):
  `STPMgr::_asserts` (`include/stp/STPManager/STPManager.h:166`, push/pop at
  `lib/STPManager/STPManager.cpp:833-846`), `Cpp_interface::cache`
  (one `Entry{result, node_number}` per level, `include/stp/cpp_interface.h:108-122`),
  and `Cpp_interface::frames` (`SolverFrame` scoping symbols, `define-fun`s and sort
  aliases, `cpp_interface.h:133-167`).
- Sound verdict shortcuts (`cpp_interface.cpp:571-583, 591-649`): a push under an
  UNSAT level inherits UNSAT; a SAT answer marks all lower levels SAT; a repeated
  check-sat with an unchanged top conjunction and a known verdict skips the solve
  (unless a model is required — models are not cached).
- The parser hands `checkSat` **one conjunction per level**
  (`assert(assertionsSMT2.size() == cache.size())`, `cpp_interface.cpp:599`) — the
  level structure survives all the way to the solve boundary.

### 1.2 The backend is single-shot by construction

The level structure is destroyed *at* the solve boundary and everything derived is
rebuilt per query:

- `checkSat` calls `resetSolver()` — `bm.ClearAllTables()` +
  `GlobalSTP->ClearAllTables()` — before every real solve (`cpp_interface.cpp:624`)
  and on every `pop()` (`cpp_interface.cpp:560`). `STP::ClearAllTables`
  (`include/stp/STPManager/STP.h:141-156`) wipes the Simplifier, ArrayTransformer,
  ToSAT and CounterExample state. This wholesale discard **is** STP's pop-soundness
  mechanism today.
- The stack is conjoined into a single AND (`cpp_interface.cpp:628-633`) and handed
  to `STP::TopLevelSTP` (`lib/STPManager/STP.cpp:186`).
- `TopLevelSTP` news a SAT solver (`STP.cpp:235`) and **deletes it**
  (`STP.cpp:239`) — learned clauses live for exactly one check-sat.
- `ToSATAIG` — AIG memo, AIG manager, CNF, `nodeToSATVar` — is a stack local
  (`STP.cpp:923`); `ToSATAIG::bitblast()` builds a local `SubstitutionMap`, local
  `Simplifier`, local `BBNodeManagerAIG`, local `BitBlaster`, all destroyed on
  return (`lib/ToSat/ToSATAIG.cpp:109-135`); the AIG manager is started/stopped per
  query (`ToSATAIG.cpp:132`).
- Reuse is positively forbidden: `assert(satSolver.nVars() == 0)` at
  `ToSATAIG.cpp:60`.
- `(check-sat-assuming …)` answers `unsupported` (`lib/Parser/smt2.y:1379,1388`).
  *(Implemented in Phase 0.)*
- The C API clears derived tables on `vc_query` (`lib/Interface/c_interface.cpp:780`)
  and `vc_push` (`c_interface.cpp:835`) but not on `vc_pop`. *Phase 0 finding:
  this asymmetry is the API's contract, not a bug* — the idiomatic usage
  brackets each query in push/pop and reads the counterexample afterwards
  (`tests/api/C/stp-counterex.cpp`, and the Python bindings solve the same
  way), so the model must survive the pop; the next `vc_push`/`vc_query`
  clears it before any cleared state could be reused for solving. Now
  documented at the declarations in `include/stp/c_interface.h`.

### 1.3 The simplification pipeline is whole-formula and destructive

`TopLevelSTPAux` (`STP.cpp:343-1018`) runs, in order: extensionality lowering;
optional eager Ackermannisation when the read count is small (`STP.cpp:446-465`);
`Flatten`; `ConstantBitPropagation` (three separate instances per query:
`STP.cpp:487,690,912`); the `sizeReducing` fixed point — `PropagateEqualities`,
`RemoveUnconstrained`, `StrengthReduction`/`NodeDomainAnalysis`, `FindPureLiterals`,
`SplitExtracts`, `MergeSame`, `Flatten`, sharing-aware `Rewriting`,
`BVSolver::TopLevelBVSolve` (`STP.cpp:263-338`, comment at `STP.cpp:509-511`:
*"Currently we discards all the state each time sizeReducing is called"*); FP
lowering; a **throw-away whole-formula bit-blast** to discover constants/equivalences
(`STP.cpp:552-588`); the main simplify/solve fixed-point loop (`STP.cpp:622-685`);
`UseITEContext`; `AIGSimplifyPropositionalCore` (whole-formula AIG round-trip through
extlib-abc); `RemoveUnconstrained` again; then **difficulty reversion** — a *second*
throw-away whole-formula bit-blast purely to compare AIG sizes, after which all
simplification may be globally reverted (`STP.cpp:755-839`; comment at `STP.cpp:761`:
*"It's of course very wasteful to do this! Later I'll make it reuse the work"*).
Then the array transform, a mid-solve `ClearAllTables` (`STP.cpp:892-894`),
bit-blast, CNF (with ABC's per-query DAG-aware AIG rewriting,
`lib/ToSat/ToCNFAIG.cpp:59-122`), and SAT.

Because the conjunction happens first, **no pass in the pipeline is
assertion-local today** — even structurally per-conjunct passes (`MergeSame`,
`Flatten`'s conjunct splitting) see the whole stack. Every result — substitutions in
`SubstitutionMap::SolverMap`, "occurs once" conclusions in `RemoveUnconstrained`,
polarities in `FindPureLiterals`, intervals in `NodeDomainAnalysis`, AIG
equivalences — is a fact about the *entire current assertion set* and is unsound to
retain across a pop. STP "solves" this by retaining nothing.

### 1.4 What is already incremental-friendly

- **Hash-consing**: node unique tables are never cleared
  (`STPManager.h:672-680` clears only printer/parser scratch), so `ASTNode`
  identities and node numbers are stable across queries — caches keyed on nodes
  remain valid *keys* forever. This is the foundation everything below builds on.
- **`SimplifyingNodeFactory` is context-free**: it has no member caches at all
  (`include/stp/NodeFactory/SimplifyingNodeFactory.h:56-120`); every rewrite depends
  only on kind + children. Same for constant evaluation (`lib/Simplifier/consteval.cpp`)
  and free-variable sets (`VariablesInExpression`). These are node-local theorems —
  already incremental-safe.
- **Intra-query incremental SAT exists**: the array-refinement CEGAR loop reuses the
  same solver instance across refinement iterations, adding clauses between solves
  (`STP.cpp:973-1012`, `lib/AbsRefineCounterExample/AbstractionRefinement.cpp:225-246`),
  and the wrapper already has the variable-freeze hook this requires
  (`include/stp/Sat/SATSolver.h:179-182`, used at `ToSATAIG.cpp:166-242`).
- **All wrapped SAT backends support assumptions natively** (MiniSat, SimplifyingMinisat,
  CryptoMiniSat5, CaDiCaL, Riss); the wrapper just does not expose it
  (`SATSolver.h:60-66` — "Search without assumptions"). Dead half-plumbing exists:
  `MinisatCore::propagateWithAssumptions` / `RissCore::propagateWithAssumptions`
  have no callers.
- **Model reconstruction through substitutions already exists**:
  `CopySolverMap_To_CounterExample` (`lib/AbsRefineCounterExample/CounterExample.cpp:2086-2094`)
  gives substituted-away variables values by recursively evaluating their defining
  expressions. This is exactly the mechanism the incremental design needs — it just
  needs to become level-aware.

### 1.5 Latent hazards any incremental design must clear

- **The per-node `is_simplified` bit** (`include/stp/AST/ASTInternal.h:146`, set at
  `lib/Simplifier/Simplifier.cpp:120`, consulted at `Simplifier.cpp:73,1318`) lives
  as long as the interned node and is never reset by any `ClearAllTables`. It
  records "reached a simplifier fixed point" **under some past substitution map**;
  the staleness guard covers `SYMBOL` nodes only (`Simplifier.cpp:1322`). It is
  unproven-safe even for today's batch reuse across queries, and must be audited,
  epoch-stamped, or ignored in incremental mode.
- `Simplifier::SimplifyMap/SimplifyNegMap` results **embed substitution-map
  contents** (`Simplifier.cpp:1405-1416`) — which is why they are deleted after
  every top-level call. Never persist them across a substitution-map change.
- `UserFlags` are mutated mid-solve and partially restored (`ackermannisation`
  `STP.cpp:199/241/428/453`; `optimize_flag` `STP.cpp:838/886`;
  `construct_counterexample_flag` `STP.cpp:467-475`) — global flags acting as
  hidden per-query state.
- `STPMgr::_current_query` is not stacked (source comment calls it a bug,
  `STPManager.h:171-174`).
- ABC has process-global state (`Cnf_Man`, freed via `Cnf_ManFree`/`CNFClearMemory`;
  `Dar_LibStart` per rewrite) — a persistent AIG/CNF layer must own its lifetime
  explicitly.

---

## 2. How the reference solvers do it

Three genuinely different infrastructures, one shared architecture. Details that
matter for STP only; the full investigations are longer.

### 2.1 Bitwuzla — the closest model for STP

Same solver shape as STP (rewriting → bit-blast to AIG → CNF → SAT, lazy array
lemmas), and the most recent design ("fully incremental preprocessing", CAV'23).

- **Backtrack infrastructure**: `BacktrackManager` + saved-size-trail containers
  (`backtrack::vector/unordered_map/unordered_set/vector_map`,
  `src/backtrack/*`): O(1) push, O(delta) pop, never rescans lower levels.
  Sub-managers (preprocessor, solver engine) sync lazily — empty push levels cost
  nothing (`src/backtrack/pop_callback.h:36-44`).
- **Assertion stack**: `std::vector<pair<Node, level>>`; each consumer
  (preprocessor, solver engine) holds one monotone cursor (`AssertionView::d_index`);
  pop truncates the stack and clamps cursors (`src/backtrack/assertion_stack.cpp:149-156`).
  That single `size_t` per consumer replaces all dirty-tracking.
- **Preprocessing is forward-only and windowed**: each pass sees an
  `AssertionVector` window over exactly one level and *structurally cannot* touch a
  lower level's entries (`src/preprocess/assertion_vector.cpp:19-37`). Lower levels
  are never re-preprocessed.
- **The substitution soundness rule** (`src/preprocess/pass/variable_substitution.cpp:751-827`):
  a substitution `x = t` may *eliminate its defining equation* only if `x` first
  occurs in the current batch; otherwise the equation stays asserted (lower-level
  assertions were never rewritten with it, and everything that was rewritten lives
  at the same-or-higher level, so pop discards rewrites and definition together).
- **SAT layer**: the `SatSolver` interface has no push/pop at all. Bit-blasting
  (AIG cache) and CNF maps are permanent, never cleared; level-0 assertions become
  permanent unit clauses; level>0 assertions are bit-blasted once and **re-assumed
  each check-sat** (`src/solver/bv/bv_bitblast_solver.cpp:154-256`). CaDiCaL's
  learned clauses survive check-sats and pops for free, because every clause in the
  solver is definitional, level-0, or a T-valid lemma.
- **Lemmas**: always asserted permanently at top level regardless of the scope they
  were derived in (`src/solver/solver_engine.cpp:594-603`) — sound because every
  lemma is a *guarded tautology* (e.g. `path-conds ∧ i=j ⇒ a=b`,
  `src/solver/array/array_solver.cpp:687-702`), not a consequence of the current
  assertions. Lemma *dedup caches* are per-level so popped lemmas can be re-derived.
- **Gating**: normalization runs only on the first check-sat; skeleton
  preprocessing runs once and rebuilds its internal SAT solver on any pop; variable
  substitution is disabled under unsat-core production. Gate, don't weaken.
- **Documented bug class to design against**: permanent encoding caches + popped
  side-conditions. A term word-blasted at level 3, popped, re-encountered at level 1
  hits the permanent cache while its accompanying lemmas were popped. Fix: a second,
  *backtrackable* "active in this scope" set consulted separately
  (`src/solver/fp/fp_solver.cpp:64-116`).
- Cost consciously paid: the substitution map is copied per push (not trailed) so
  `get-value` works immediately after a pop without re-preprocessing
  (`variable_substitution.cpp:1337-1358`).

### 2.2 cvc5 — CD data structures and clause-level tagging

- **Context core** (`src/context/`): region allocator + per-scope trail of saved
  object copies. Push O(1); first write to an object per scope pays one save; reads
  free; pop is O(objects written in that scope). Container tiers matter: `CDO<T>`
  (scalar copy), `CDList` (save a size, truncate on pop), `CDInsertHashMap` (insert
  only, save a size — used for the CNF maps), `CDHashMap` (heap `ContextObj` per
  entry — expensive, used sparingly), plus `ContextNotifyObj` as the escape hatch
  ("plain cache, invalidate wholesale on pop" — used by the substitution
  apply-cache, `src/theory/substitutions.h:79-101`).
- **Two nested contexts**: user context (push/pop) and SAT context (also pushed per
  decision level). Preprocessing state, CNF stream maps, assertion lists all hang
  off the user context; theory fact queues off the SAT context.
- **Only new assertions are preprocessed**: a `CDO<size_t>` watermark into a
  `CDList<Node>` of assertions (`src/smt/smt_driver.cpp:154, 204-215`) — the index
  rewinds on pop automatically. ~5 lines; this is the entire mechanism.
- **Never retract an elimination — re-assert its definition**: substitutions live
  in a user-context map and are never unwound within a scope; if the eliminated
  variable was already shipped to the SAT layer (tracked in a user-context symbol
  set), the defining equality `x = t` is *also* pushed as a real assertion
  (`src/preprocessing/passes/non_clausal_simp.cpp:316-346`). Model queries apply
  the substitution before consulting the model (`src/theory/theory_model.cpp:137-141`).
- **Minisat clause tagging**: every clause carries the minimum assertion level its
  derivation depends on — input clauses the level they were asserted at; learned
  clauses `max(level of resolved antecedents)` (`src/prop/minisat/core/Solver.cc:405-413,
  854, 1535`). Pop deletes clauses above the popped level and physically deletes
  variables introduced above it; **learned clauses below survive**. Variable
  activity and saved phases survive pops — free cross-query learning.
- **The CaDiCaL backend uses per-level activation literals instead**: clauses are
  guarded by the level's activation literal; pop asserts its negation and lets the
  solver GC (`src/prop/cadical/cdclt_propagator.cpp:452-660`).
- **The dedicated BV bit-blasting solver is the exact template for STP**: SAT
  solver + CNF stream built over a *null context* — the clause DB is never
  backtracked; term→bits caches are plain permanent `unordered_map`s; retraction is
  purely by assumptions (`src/theory/bv/bv_solver_bitblast.cpp:113, 214-235`).
- **Hard gates under incremental mode** (`src/smt/set_defaults.cpp:611-1288`):
  Ackermannization, unconstrained simplification, sort inference, deep restarts,
  eager bitblasting outside pure QF_BV, minisat's SatELite variable elimination
  (`src/prop/minisat/minisat.cpp:128-133`) — all off or an error. One well-named
  predicate, checked everywhere.
- Notable negative result: the machinery to keep T-valid lemmas at level 0 exists
  (`LemmaProperty::REMOVABLE`) but *no call site sets it* — default-config theory
  lemmas die on pop and are re-learned via the SAT learned-clause path. Bitwuzla's
  permanent-lemma policy is the better model for STP.

### 2.3 z3 — the incremental rewriting playbook

z3's new simplifier framework (`src/ast/simplifiers/`) is the most explicit answer
to "how do rewrite pipelines survive push/pop":

- **Append-only formula vector + one `qhead` cursor**; every simplifier operates on
  `[qhead, qtail)` only; the cursor advances once per flush (at check-sat/push);
  pop truncates and rewinds — nothing is re-simplified
  (`dependent_expr_state.h:46,88,207-223`; `simplifier_solver.cpp:129-150`).
- **Freeze at the hand-off boundary**: the moment formulas ship to the backend,
  their symbols are frozen (`freeze_prefix`, `dependent_expr_state.cpp:96-100`);
  every eliminating pass carries exactly one guard — `if (frozen(v)) skip`. The
  freeze set is trailed, so pop thaws. Consequence accepted: after the first
  check-sat, later batches can only eliminate variables *they introduced*.
- **Elimination taxonomy + replay**: every elimination is logged as a *definition*
  (may be inlined into future assertions forever) or a *loose* elimination (must be
  repaired by re-asserting the removed formulas when a new assertion mentions the
  variable). The repair step (`model_reconstruction_trail::replay`,
  `model_reconstruction_trail.cpp:39-195`) runs *before* simplifying each new
  batch, guarded by a cheap symbol-intersection test. The same trail rebuilds
  models for eliminated variables. Getting the definition/loose taxonomy wrong is
  *the* unsoundness risk in incremental rewriting.
- **Not ported ⇒ not usable incrementally**: only passes rewritten as
  `dependent_expr_simplifier`s run in the incremental core; the rest (~30 tactics,
  incl. `ackermannize_bv`, `elim-small-bv`, `aig`, `ctx-solver-simplify`) exist only
  in the from-scratch tactic path.
- **Two-driver switching** (`src/solver/combined_solver.cpp:69-71, 176-188`): a
  non-incremental tactic solver and an incremental core run side by side; every
  assertion is forwarded to both; the first `push()` (or an assert after a
  check-sat) flips to the incremental core **unconditionally**. No preprocessing
  state is migrated at the switch — duplication is deliberately preferred over
  state translation. z3's own legacy SMT core discards learned clauses on user pop;
  make push lazy so empty scopes are free (`asserted_formulas.cpp:190-217`).

### 2.4 Convergence table

| Question | cvc5 | Bitwuzla | z3 (new core) |
|---|---|---|---|
| Retraction infrastructure | CD containers on user context (saved-copy trail, region alloc) | Backtrackable containers (saved-size trail) + per-subsystem managers | One trail stack + scope watermarks |
| "What still needs processing" | `CDO<size_t>` watermark into `CDList` | Per-consumer cursor into level-tagged stack | `qhead` into append-only vector |
| Re-preprocess lower levels on pop? | Never (watermark rewinds) | Never (cursor clamps) | Never (truncate only) |
| Bit-blast / CNF caches | Permanent (null context / plain maps) | Permanent (never cleared) | n/a (SAT core internal) |
| SAT retraction | Clause level-tags (minisat) or activation literals (CaDiCaL); BV solver: assumptions | Assumptions only; interface has no push/pop | Scoped clause deletion (legacy core) |
| Learned clauses across pop | Survive if derivation level allows | Survive always (everything permanent is valid) | Lost on user pop (legacy core) |
| Variable elimination under pop | Never retract; re-assert `x = t` if `x` already shipped | Eliminate only if var first seen in current batch | Freeze shipped symbols; replay/repair on demand + def/loose taxonomy |
| Non-incremental passes | Hard-gated by one predicate | Gated (first-batch-only / rebuild-on-pop) | Exist only in the from-scratch driver |
| Theory lemmas | Level-tagged (die on pop in default config) | Permanent guarded tautologies + per-level dedup caches | n/a here |
| Batch path preserved? | Same driver, options differ | Same driver | Separate driver, switch on first push |

---

## 3. Why STP's architecture resists incrementality — the specific blockers

1. **The AND at the boundary** (`cpp_interface.cpp:628-633`): level structure is
   erased before the backend sees the formula; every pass becomes cross-assertion
   by construction. `STPMgr::getVectorOfAsserts` even collapses levels destructively
   *inside the stack* (`STPManager.cpp:862-884`).
2. **Solver-per-query** (`STP.cpp:235/239`) plus `assert(nVars()==0)`
   (`ToSATAIG.cpp:60`): the SAT solver cannot outlive a check-sat.
3. **Encoding state is stack-local** (`STP.cpp:923`, `ToSATAIG.cpp:109-135`): AIG
   manager, term→AIG memo, AIG→CNF, node→SAT-var maps all die per query, so even
   *unchanged* assertions are re-simplified, re-blasted, re-CNF'd every round.
4. **Global destructive simplification with a single shared substitution map**:
   `SolverMap` entries are consequences of the whole assertion set; the simplifier
   memo embeds them; `RemoveUnconstrained` ("occurs once in the entire formula"),
   `FindPureLiterals` (whole-formula polarity), `NodeDomainAnalysis` (bounds from
   the asserted conjunction), CBP, `UseITEContext`, `AIGSimplifyPropositionalCore` —
   all whole-formula facts, none level-attributable today.
5. **Whole-formula accept/reject decisions**: difficulty reversion
   (`STP.cpp:755-839`) and the two throw-away bit-blasts are global greedy choices
   that have no incremental meaning.
6. **Per-solve theory contexts**: `FpEncodingContext` is rebuilt each solve
   (`STP.cpp:193-195`); `ExtensionalityContext::beginSolve` wipes ~25 containers per
   solve; `ArrayTransformer` read maps and refinement lemmas are cleared per query,
   so array axioms — which are guarded tautologies and could persist — are
   re-derived from zero every check-sat.
7. **Hidden global mutable state**: `UserFlags` mutated mid-solve, the `is_simplified`
   node bit, `_current_query`, ABC globals (§1.5).

None of these is accidental: each is the simplest correct design for a single-shot
solver. The point of §2 is that the fixes are all known, and STP's hash-consing +
existing frame stack + existing CEGAR-style solver reuse mean the distance is
smaller than it looks.

---

## 4. Target architecture

### 4.1 Strategy: two drivers, switch on first push

Keep `TopLevelSTP`/`TopLevelSTPAux` exactly as they are for single-query solving.
Add an **incremental driver** beside it, selected when the session becomes
incremental (first `(push)`, or `--incremental`). This is z3's `combined_solver`
policy and it is the single most important de-risking decision:

- batch/SMT-COMP performance is untouched;
- the incremental driver can start minimal (Phase 1) and grow passes over time;
- there is never a moment where preprocessed state must be migrated between modes —
  on the switch, the incremental driver starts from the (unpreprocessed, level-
  tagged) assertion stack it already has.

The level-0 batch — in BMC workloads by far the largest formula — can still be
given the full batch treatment *inside* the incremental driver (bitwuzla's
"initial assertions only" gates), so the batch pipeline's value is retained where
it matters most.

### 4.2 New infrastructure: backtrackable containers

Port the bitwuzla pattern (not the code): a `BacktrackManager` plus
`backtrack::vector` / `backtrack::unordered_map` / `backtrack::unordered_set`
with saved-size/insertion-trail semantics — O(1) push, O(delta) pop. This is
~300–500 LOC of self-contained header code (`include/stp/Support/Backtrack.h`),
needs no allocator surgery (unlike cvc5's region allocator), and covers every store
the plan needs. Rules of use:

- prefer insert-only maps (pop = truncate a key trail);
- copy-per-level only where a post-pop query must work without recomputation
  (bitwuzla pays this exactly once, for the substitution map; STP can avoid it —
  see 4.6);
- one manager for the solver context initially; lazy per-subsystem managers only if
  profiling ever shows empty pushes mattering.

### 4.3 The assertion store and cursors

`STPMgr::_asserts` is already the right shape. Changes:

- stop collapsing it (`getVectorOfAsserts`), stop conjoining it (`checkSat`);
  represent each assertion individually, tagged with its level;
- give each consumer (preprocessor, encoder) a monotone cursor; pop truncates the
  store and clamps cursors;
- `Cpp_interface::checkSat` passes the store, not an AND, to the incremental
  driver; the existing verdict cache and its monotonicity shortcuts stay exactly
  as they are (they are correct and useful).

### 4.4 The persistent encode/solve context (Phase 1 core)

A new object — `IncrementalContext`, owned by `STP` (or `STPMgr`), lifetime = the
incremental session:

- **one `SATSolver`** created at first incremental check-sat, kept until
  `(reset)`/`(reset-assertions)`/driver teardown;
- **persistent bit-blast state**: `BBNodeManagerAIG` + its AIG manager +
  `BitBlaster` memos + AIG→CNF map + `nodeToSATVar`, hoisted out of
  `ToSATAIG`'s stack frame. Hash-consing makes `ASTNode` keys stable, so these
  caches are sound forever — they are conservative extensions (fresh Tseitin
  variables, definitional clauses), the same argument bitwuzla and cvc5 rely on;
- **the permanent/contextual split**: for each assertion, bit-blast + CNF once;
  clauses emitted are definitional and permanent. Then:
  - level-0 assertion ⇒ assert its root literal as a **permanent unit clause**;
  - level>0 assertion ⇒ record its root literal in a per-level
    `backtrack::vector`; every `solve()` call **assumes** all active recorded
    literals (bitwuzla's scheme). Pop truncates the vector — no SAT-side work at
    all. (Alternative: one activation literal per level guarding that level's
    units, cvc5-CaDiCaL style, with `¬activation` asserted on pop so the solver
    can GC. Start with root-literal assumptions — simpler, no clause rewriting,
    and it gives failed-assumption information for free; add activation literals
    later only if assumption-set size shows up in profiles.)
- **wrapper API**: extend `SATSolver` with `solve(const vec_literals& assumptions,
  bool& timeout_expired)` and ensure `setFrozen` covers assumption variables.
  All five backends support this natively. `SimplifyingMinisat`'s variable
  elimination must freeze assumption/root variables (it already freezes
  refinement variables) — or SatELite-style simplification is disabled in
  incremental mode, cvc5's choice.
- **what is *not* run in incremental mode at the SAT layer**: ABC's whole-CNF
  DAG-aware rewriting (`ToCNFAIG::dag_aware_aig_rewrite`) — it rewrites the global
  AIG per query and is meaningless against a persistent, incrementally-grown AIG.
  Gate it (batch driver keeps it).

Learned clauses now survive across check-sats and pops *by construction*: every
clause in the solver is definitional, a level-0 unit, or a T-valid lemma (4.7),
and context-dependence lives only in the assumption set. This alone is the answer
to issue #483.

### 4.5 Rewrite-rule policy (see §5 for the full pass table)

Three classes, echoing all three reference solvers:

- **Class A — node-local, context-free** (`SimplifyingNodeFactory`, constant
  evaluation, free-variable sets): always on, caches persistent. Nothing to do.
- **Class B — assertion-local**: run once per *new* assertion when it enters the
  incremental driver ("at flush", before encoding): conjunct splitting/flattening
  within the assertion, ITE-lifting-style local normalization, `MergeSame` within
  the new batch. Results are final; lower levels are never revisited.
- **Class C — cross-assertion/global**: in incremental mode, each pass is either
  **windowed** (runs over the new batch only, under explicit soundness rules) or
  **gated off**. Phase 1 gates *all* of them (correctness first — precedent: this
  is close to `-w` plus more, and cvc5/z3 ship exactly such gates); Phase 2 brings
  back the highest-value ones windowed:
  - `PropagateEqualities` / `BVSolver` variable elimination — windowed, with the
    **first-seen rule** (bitwuzla): an equation `x = t` in the new batch may
    eliminate `x` (and delete itself) only if `x` first occurs in this batch;
    otherwise the substitution may simplify *this and future* batches but the
    equation stays asserted. Equivalently z3's freeze rule: symbols already
    encoded to SAT are frozen as elimination targets. Substitutions are recorded
    in a **leveled SolverMap** (backtrack map + per-entry level); pop truncates.
    Nothing below the window is ever rewritten, so popping a level discards both
    the substitutions discovered there and every formula they touched.
  - `ConstantBitPropagation`, `NodeDomainAnalysis`/`StrengthReduction` — windowed
    variant is sound only if facts derived from the batch are not propagated into
    lower-level formulas; run them *per-assertion* (root-local) initially, or gate.
  - `RemoveUnconstrained`, `FindPureLiterals`, `UseITEContext`,
    `AIGSimplifyPropositionalCore`, sharing-aware `Rewriting`/`Flatten` across
    assertions, speculative bit-blast constant discovery, difficulty reversion,
    eager Ackermannisation (read-count heuristic `STP.cpp:446-465`) — **gated off
    in incremental mode, permanently**. Every reference solver gates this family
    (cvc5 errors on Ackermann + unconstrained-simp under incremental; z3 leaves
    them in the from-scratch driver only; bitwuzla runs normalize once). The
    level-0 initial batch still gets them via the batch-style first flush.
- **Simplifier memo hygiene**: in the incremental driver, `SimplifyMap`-style
  memos are per-flush (discard after each batch — bitwuzla clears its rewrite
  cache per preprocess call; cheap and removes the contamination problem). The
  `is_simplified` node bit is not consulted in incremental mode until the audit
  (§1.5) proves it safe or converts it to an epoch stamp.

### 4.6 Models and `get-value`

- Model construction already reads `SolverMap` + `nodeToSATVar` +
  `arrayToIndexToRead`; with the leveled SolverMap and persistent encode maps this
  keeps working unchanged — values of eliminated variables are reconstructed by
  evaluating their defining terms (existing `CopySolverMap_To_CounterExample`
  path).
- SMT-LIB only requires models to survive until the next `assert`/`push`/`pop`, so
  STP may invalidate the model on pop (as `Cpp_interface::pop` effectively does
  today) and **avoid** bitwuzla's copy-the-substitution-map-per-push cost
  entirely. Keep the existing "re-solve if a model is demanded and only a verdict
  was cached" behavior.

### 4.7 Arrays (Phase 3)

- `ArrayTransformer::arrayToIndexToRead` becomes a backtrack map: reads registered
  at the level their assertion entered; pop truncates. The transform runs per
  batch (new reads only); read-over-write ITE forms are per-node and cacheable.
- **Refinement lemmas become permanent**: STP's read-refinement axioms (Ackermann
  congruence over read abstraction variables, read-over-write instances) are
  guarded tautologies over the terms they mention — adopt bitwuzla's rule: assert
  them as permanent clauses regardless of current level, keep the *dedup* caches
  leveled so popped-and-reasserted structure can re-derive them. If a lemma
  mentions variables introduced at level L, its clause is implicitly inert once
  those assumptions are retracted — correct, merely dead weight until GC.
  (cvc5's tighter alternative — tag each lemma clause with the max intro level of
  its variables — is the upgrade path if dead clauses ever measure.)
- The CEGAR loop already adds axioms incrementally to the live solver within one
  query; with the persistent solver this loop simply continues to work across
  queries.
- **Design against the bitwuzla FP-word-blast bug class** (permanent encoding +
  popped side conditions): any encoding step that emits side constraints (array
  read axioms during transform, RM one-hot constraints, FP totalisation
  witnesses) needs *two* caches — the permanent structural one and a
  backtrackable "side conditions active at this level" one, checked separately.
- Extensionality (`ARRAY_EQ`): its context is rebuilt per solve by design
  (fresh witness symbols per solve). Initially: **queries with active array
  equality fall back to batch-style solving within the incremental driver**
  (fresh encode context for that check-sat). Making EXTSTP level-aware is its own
  later project; the fallback keeps it correct meanwhile.

### 4.8 FP (Phase 4)

`FpEncodingContext` is rebuilt per solve today; its lowering caches
(`FpTotalise::persistent_cache`, `FloatBlast::terminal_cache`) are per-context.
To coexist with a persistent SAT encoding, the context must become session-long
with monotone caches, and totalisation/canonicalisation witness introduction must
be deterministic per node (introduced symbols keyed by the node they witness, so
re-lowering yields identical terms). Until then, the same fallback as
extensionality: FP-bearing incremental sessions solve batch-style per check-sat
(still benefiting from frontend caching). The FP/RM array registries are already
frame-scoped on the frontend side.

---

## 5. Pass-by-pass disposition

| Pass (call site in `TopLevelSTPAux`) | Class | Incremental driver disposition |
|---|---|---|
| `SimplifyingNodeFactory` (node creation) | A | on, unconditionally |
| `BVConstEvaluator` / consteval | A | on |
| `VariablesInExpression` (free vars) | A | on; cache persistent (memory-only clears allowed) |
| `Flatten` — conjunct splitting (`STP.cpp:477`) | B | per new assertion |
| `MergeSame` (`STP.cpp:310`) | B | within new batch only |
| `SplitExtracts` (`STP.cpp:303`) | B/C | audit: if extract-split substitutions are definitional per symbol, windowed with first-seen rule; else gate |
| `PropagateEqualities` (`STP.cpp:272,633`) | C | **windowed** + first-seen rule + leveled SolverMap (Phase 2) |
| `BVSolver::TopLevelBVSolve` (`STP.cpp:333,681`) | C | **windowed** + first-seen rule (Phase 2) |
| `Simplifier::SimplifyFormula_TopLevel` (`STP.cpp:675`) | C | per-batch, memo discarded per flush (Phase 2) |
| `ConstantBitPropagation` ×3 (`STP.cpp:487,690,912`) | C | per-assertion/root-local variant or gate; encoder-side CBP (the third instance) may stay per-batch |
| `NodeDomainAnalysis` + `StrengthReduction` (`STP.cpp:285,703`) | C | per-assertion variant or gate |
| `FindPureLiterals` (`STP.cpp:295,715`) | C | **gate** (whole-formula polarity; classic pop-unsound) |
| `RemoveUnconstrained` (`STP.cpp:278,746`) | C | **gate** (occurs-once over whole formula; cvc5 gates the analogue) |
| `UseITEContext` (`STP.cpp:729`) | C | **gate** |
| `AIGSimplifyPropositionalCore` (`STP.cpp:736`) | C | **gate** |
| Sharing-aware `Rewriting` (`STP.cpp:325`) | C | **gate** (share counts are whole-DAG) |
| Speculative bit-blast const/equiv discovery (`STP.cpp:552-588`) | C | **gate** (also: not recorded in SolverMap — unsound for models) |
| Difficulty reversion + 2nd throw-away bit-blast (`STP.cpp:755-839`) | C | **gate** (no incremental meaning) |
| Eager Ackermannisation, read-count heuristic (`STP.cpp:446-465`) | C | **gate** (cvc5 hard-errors on Ackermann + incremental) |
| ABC DAG-aware AIG rewriting (`ToCNFAIG.cpp:59-122`) | C | **gate** (global AIG optimization vs persistent AIG) |
| Array transform (`STP.cpp:876`) | C→B | per new batch over leveled read registry (Phase 3) |
| FP totalise + lower (`STP.cpp:229-233,534-543`) | C→B | per new assertion once `FpEncodingContext` is session-long (Phase 4); until then batch fallback |
| Extensionality lowering/prepare | C | batch fallback (Phase 4+) |

All Class-C gates apply to batches *after the first flush*; the level-0 initial
flush may run the full batch pipeline (§4.1). Every gate is one predicate:
`UserFlags.incremental_mode` (set on first push or `--incremental`), validated
centrally at driver selection — cvc5's `SetDefaults` lesson: one well-named
predicate, hard errors for explicitly-requested incompatible options.

---

## 6. Phased plan

### Phase 0 — Semantics, baseline, measurement (small)
1. Define and document the C-API pop/model contract. *(Done — turned out the
   `vc_pop` asymmetry is the contract, not a bug: the counterexample belongs
   to the last `vc_query` and must survive the push/query/pop bracket. It is
   now documented in `c_interface.h` and pinned by
   `tests/api/C/push-pop-model.cpp`; the SMT-LIB frontend, by contrast, gets
   SMT-LIB model-invalidation semantics via `Cpp_interface::model_valid`.)*
2. Implement `(check-sat-assuming …)` as sugar: internal push / assert / check-sat
   / deferred pop (cvc5's exact scheme, including the deferred pop so `get-value`
   works). Extends the testable surface for everything below.
3. Build the benchmark harness over `/home/avj/clones/stp/incremental`: per-check-sat
   wall time, and a phase breakdown (parse / simplify / transform / BB+CNF / SAT)
   on representative QF_BV and QF_ABV incremental files. This sizes the win and
   creates the regression yardstick.
4. Audit the `is_simplified` node bit (§1.5) — independent soundness question, and
   incremental mode must know the answer.
5. Decide and document push/pop/query semantics for the C API (`vc_query` is
   validity-flavored; `_current_query` is un-stacked) — write the contract before
   building on it.

*Exit: incremental corpus runs green under current (re-solve) semantics with the
harness capturing timings.*

### Phase 1 — Persistent SAT + persistent encoding, assumptions (the big win)
1. `include/stp/Support/Backtrack.h`: manager + vector/map/set (§4.2), unit tests.
2. `SATSolver::solve(assumptions)` wrapper API + per-backend implementations;
   freeze discipline for assumption variables; decide SimplifyingMinisat policy
   (freeze vs gate).
3. `IncrementalContext` (§4.4): persistent solver + hoisted `ToSATAIG` state
   (delete the `nVars()==0` assert and the `first` latch in favor of cursor
   logic); level-0 units vs assumed root literals; pop = truncate.
4. Incremental driver v1: Class A rewrites only; per-assertion encode; no global
   simplification; scope = QF_BV (fall back to batch-style solve inside the
   driver for arrays/FP/ext queries).
5. Driver switch on first push / `--incremental`; batch path untouched; option
   validation predicate.

*Exit: on QF_BV incremental benchmarks, unchanged-prefix assertions are not
re-encoded (assert via counters) and per-round SAT time shows learned-clause
retention; solve-vs-batch-oracle testing green (§7). This closes the substance of
issue #483.*

### Phase 2 — Incremental rewriting (the "rewrite rules" phase)
1. Leveled `SolverMap` (backtrack map, per-entry level); model path reads it
   unchanged.
2. Windowed `PropagateEqualities`/`BVSolver` with the first-seen elimination rule
   (§4.5); first-occurrence-level tracking per symbol (one backtrack map).
3. Per-flush Simplifier memos; per-assertion Class B normalization; level-0 first
   flush runs the batch pipeline.
4. Gates for the rest of Class C wired to the predicate; document each (§5 table
   is the spec).
5. Optional, later: z3-style replay/repair (definition vs loose taxonomy) to
   re-enable more aggressive elimination — only if profiling shows the first-seen
   rule leaving real performance on the table.

*Exit: incremental QF_BV results identical to batch-oracle on the corpus with
simplification enabled; measurable end-to-end win over Phase 1 on
simplification-heavy files.*

### Phase 3 — Incremental arrays
1. Leveled `arrayToIndexToRead` (+ `ack_pair`); per-batch transform of new reads.
2. Permanent refinement lemmas + leveled dedup caches; CEGAR across check-sats on
   the persistent solver; two-cache pattern for side conditions (§4.7).
3. Retire the batch fallback for pure QF_ABV.

*Exit: QF_ABV incremental corpus green vs oracle; refinement-axiom re-derivation
count across rounds drops to ~0 for stable prefixes.*

### Phase 4 — FP and extensionality
1. Session-long `FpEncodingContext` with deterministic, node-keyed witness
   introduction; per-batch lowering; retire FP batch fallback (QF_BVFP/QF_ABVFP
   corpus — the largest, 18k files).
2. Extensionality: either level-aware EXTSTP records or a documented permanent
   batch fallback for ARRAY_EQ-bearing sessions.

### Phase 5 — Hardening and performance
1. Fuzzing: murxla incremental campaigns (STP alone first, per prior campaign
   experience); delta-debugged trace corpus.
2. Differential testing vs cvc5/bitwuzla/z3 over the incremental corpus.
3. Clause-DB / assumption-set growth heuristics: periodic re-encode from the live
   persistent AIG (cheap, since the AIG survives) — the standard mitigation for
   long sessions with many pops; statistics (`--stats` for reuse counters).
4. Docs: SMT-LIB incremental support statement, C-API semantics, option reference.

Dependencies: P1 → P2 → {P3, P4} (P3 and P4 independent of each other); P0 first;
P5 continuous from P1 on.

---

## 7. Testing strategy

- **Batch-oracle equivalence (the workhorse)**: for any incremental trace, each
  check-sat's verdict must equal a fresh-process batch solve of the active
  assertion set at that point. Automatable over the whole corpus; run it per
  phase. (Verdicts only; models checked by evaluation, not comparison.)
- **Model checking**: for sat answers with models requested, evaluate the active
  assertions under the returned model (`--check-counterexample` machinery already
  exists and runs under `!NDEBUG`).
- **Backtrack-container unit tests** (push/pop/clear/insert-at-level semantics,
  including the pop-clamps-cursor edge cases).
- **Reuse counters as regression tests**: "assertions encoded", "AIG nodes
  created", "CNF clauses added" per round must be ~0 for unchanged prefixes.
- **Fuzzing**: murxla's incremental mode; STP-only configuration before
  cross-solver blame. The frontend/backend seam (verdict cache + assumption sets)
  is exactly the kind of state machine fuzzers break.
- **The existing test suite in batch mode must stay bit-identical** — the
  two-driver split makes this checkable by construction.

---

## 8. Risks and open questions

1. **`is_simplified` node bit** — *audited in Phase 0, cleared for soundness.*
   The bit is consulted only by the Simplifier's own memo short-circuit
   (`CheckSimplifyMap`, `Simplifier.cpp:73`, plus `hasBeenSimplified` child
   checks); the deep substitution application that equality-consumption
   soundness rests on (`SubstitutionMap::replace`, applied under the
   `hasUnappliedSubstitutions()` guard, `STP.cpp:743`) never reads it. The
   bit asserts "this node simplifies to itself", which is
   substitution-map-relative — carried across queries it can only cause the
   Simplifier to return the node *unchanged* (trivially equivalent), i.e.
   missed simplifications, never wrong ones. It remains a cross-query
   completeness quirk worth an epoch stamp someday; the incremental driver
   sidesteps it entirely by not using the batch Simplifier.
2. **SimplifyingMinisat + assumptions** — variable elimination vs frozen
   assumption literals; may end up gated like cvc5's SatELite. Decide by
   experiment in Phase 1.
3. **Assumption-set size** on deep stacks (thousands of active root literals per
   solve). Bitwuzla lives with exactly this; if it measures, per-level activation
   literals are the drop-in alternative (§4.4).
4. **Memory growth** — persistent AIG/CNF/node tables grow monotonically across a
   session (all reference solvers accept this); periodic re-encode is the relief
   valve (P5.3).
5. **FP witness determinism** — Phase 4 hinges on lowering being reproducible per
   node across flushes; needs a focused audit of `FpTotalise`/`FloatBlast`
   introduced-symbol naming.
6. **C-API semantics** — `vc_query`'s validity orientation and the un-stacked
   `_current_query` need a defined contract before the incremental driver is
   exposed there (P0.5).
7. **ABC global state** — persistent AIG manager lifetime vs `Cnf_ClearMemory` and
   `Dar_LibStart`; the incremental encoder should own a private, session-long AIG
   manager and never route through the global-cleanup paths.
8. **Where the win is** — BMC rounds whose time is SAT-dominated will benefit
   enormously (learned clauses + no re-encode); rounds dominated by parsing or by
   level-0 simplification less so. Phase 0's measurements keep expectations honest
   and should drive which Class-C passes are worth windowing in Phase 2.
