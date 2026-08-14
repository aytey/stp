# UFSTP v2 fixed integration report

Date: 2026-08-14 (Europe/London)

## Integration verdict

`uf_codex_fixed` is the recommended implementation lineage for merging UF
support into `master`. It is a direct descendant of the current master
`e27b10d0b6569821b5b2cd275c81ab5a8b8fc984`, retains the reviewable
`uf_codex` milestones, and adds red-first fixes for every release blocker
found while comparing `uf` and `uf_codex`.

The original `uf_codex` report at `90c57a4a` is historical evidence, not an
acceptance result. In particular, the audit reproduced an unsound answer
after a SAT-only backend rebuild, a batch fatal on compound UF results,
non-transactional malformed commands, binder-shadowing failure, public-model
permission drift, raw-handle ABA, Python crashes, and an incomplete installed
header set. The fixed branch has tracked regressions for those classes and
passes the combined validation below.

## Lineage and review slices

The branch is intentionally not a squash. The original implementation remains
reviewable as AST/frontend, lowering, checker/lemma, batch/persistent adapters,
models/APIs, and tests. The follow-up commits are:

| Commit | Review slice |
|---|---|
| `fa4574a4` | Import `uf` lifecycle regressions and fuzz/model harnesses before fixes |
| `e1bc0e91` | Add frontend transaction, shadowing, and model-permission red tests |
| `ff957282` | Add invalid/stale/destroyed/cross-context API and install red tests |
| `e8439cce` | Own solve scalars in the live SAT backend; add backend generations and post-order lowering |
| `dfc431e9` | Make binder resolution and malformed-command rejection transactional |
| `643bb7d1` | Replace raw C UF declarations with generation-checked opaque records |
| `43b2f235` | Make Python Bool/NULL/stale/literal model paths safe |
| `23a01675` | Install and export the public C/C++ UF header closure |
| `2a33d376` | Add deep/shared lowering, CNF, parser-recovery, and permission tests |

## What was taken from `uf`

The comparison did not simply select one branch and discard the other. The
fixed branch retains `uf_codex`'s immutable typed declarations, durable
`UF_APPLY`, completed-root boundary, shared checker, defensive lemma adapters,
and deterministic source-level model design, while incorporating the useful
parts of `uf`:

- the batch-liveness, backend-rebuild, deep-chain, FP/array, assuming,
  observability, and source-sort regression corpus;
- all three reusable differential/peer/model fuzzing tools, plus compound
  result families which reproduced the original batch failure;
- explicit `solveScalars`, a solve-scoped preprocessing-protection window,
  post-CNF totalisation/freezing, and one direct SAT candidate authority;
- heap-backed, memoised post-order lowering in place of repeated substitution
  walks, preserving `uf_codex`'s typed validation and adapter records;
- useful constant, cache, malformed-leaf, and guarded-block CNF unit cases;
- Python literal ergonomics and nonfatal validation, adapted to the stronger
  generation-checked C boundary.

The `uf` parser poison mechanism, fatal C API contract, and stale persistent
SAT-literal cache were deliberately not ported.

## Correctness changes

### Solve lifecycle and liveness

- Every symbolic UF argument/name/result is explicitly registered as a solve
  scalar and has exactly one full Bool/BV mapping in the current SAT backend.
- Batch registration occurs after CNF conversion, including roots reduced to
  `true`; candidate reads never fall back to a competing symbolic model path.
- Preprocessing protection is active only inside an RAII solve scope.
- The persistent adapter keys reification literals by semantic epoch, concrete
  SAT-backend generation, and block. Every solver replacement advances the
  generation and clears stale literals/state.
- Persistent helper definitions and final congruence clauses remain guarded by
  the active block literal.

### Frontend and public API

- Let/formal binders resolve before global functions, UFs, and ordinary
  symbols; formal declaration names are never lexed as global UF tokens.
- A top-level parser command now commits or rolls back its UF applications as
  one transaction. Rejected `check-sat-assuming` commands do not push, solve,
  print a verdict, or perturb model state. Parse recovery resets temporary
  binders and lexer latches.
- Internal candidate construction no longer grants public `get-model` or
  `get-value` permission.
- C declarations are opaque process-stable tokens carrying owner/generation;
  invalid, stale, destroyed, and cross-context declarations/actuals are
  rejected before dereference. Legacy raw `Expr` wrapper addresses are
  tombstoned to prevent allocator ABA while their AST references are released
  promptly.
- Python turns rejected/stale/NULL paths into exceptions, handles Bool UF
  results, accepts correctly sorted Python Bool/int arguments, preserves the
  historic BV `True`/`False` shorthand, and safely slices wide model values.
- The installed target exports its include directories and installs the full
  public UF/AST header closure; staged C and C++ consumers compile and link
  using only `find_package(STP)` and the exported target.

### Lowering and CNF

- Completed-root lowering is one memoised, left-to-right post-order DAG walk
  with heap-resident frames. Nested applications precede consumers, shared
  compound actuals receive one name, and the durable public root remains
  untouched.
- The UF barrier is checked once over the semantic root and naming
  definitions, avoiding the former quadratic repeated scans.
- Added tests cover a 4,096-node adversarial shared DAG and 20,000 nested UF
  applications under a 1 MiB stack.
- Refinement tests now exhaust Bool/BV constant atoms, pre-mutation validation
  failures, exact duplicate elimination/cache reuse, and active/inactive
  guarded-block truth tables.

## Final validation

| Matrix | Result |
|---|---|
| Assertions-on RelWithDebInfo, all compiled backends, complete CTest | **136/136 pass** |
| Assertions-off Release, all compiled backends, complete CTest | **136/136 pass** |
| Complete default query corpus | **644 pass, 2 unsupported, 0 fail** |
| UF lit corpus | **53/53 pass** in default and explicit CaDiCaL modes |
| CryptoMiniSat, MiniSat, Riss UF-applicable corpus | **52/52 each pass**; rebuild repro also gives 14/14 SAT |
| Simplifying MiniSat applicable corpus | **47/47 pass**; five warning-sensitive fixtures pass after filtering its documented persistent-fallback warning |
| Focused native UF/source-sort tests in Release | **58/58 pass** |
| Python API in Release | **77/77 pass** |
| Staged install-tree C/C++ consumer | **pass** |
| Differential fuzz, seed 7 | **200/200**, plus **50/50** push/pop, zero disagreements |
| Fuzz participants | eager oracle; STP default/CaDiCaL/CryptoMiniSat/simplifying-MiniSat/Riss; batch/persistent; CVC5; Z3 |
| Bitwuzla differential fuzz, seed 11 | **200/200**, plus **50/50** push/pop, zero disagreements |
| CVC5/Z3 model replay | 4 cases, 20 SAT models, 60 producer/validator pairs, **0 failures** |
| Bitwuzla model replay | 4 cases, 15 SAT models, 30 producer/validator pairs, **0 failures** |
| Selected real CVC5 peer regressions | 5 cases × batch/persistent, **10/10 pass** |

The CaDiCaL inprobing fixture is necessarily backend-specific; when another
backend is forced, lit still selects it from the build capability rather than
the runtime backend. Simplifying MiniSat also documents that persistent mode
falls back to plain MiniSat and prints a warning before verdicts. Those are
test qualification/output-order limitations, not answer disagreements.

ASan+UBSan validation used explicit Clang sanitizer flags because the
repository's `SANITIZE=ON` option rewrites the compiler to a non-absolute name
after `project()`, which the nested ABC project rejects. The new parser,
lowerer, and UF handle paths show no sanitizer memory-safety failures: focused
native UF tests passed 43/43 with leak detection, UF lit passed 53/53, the
UF-specific deep-stack test and sanitized install consumer passed, and Python
passed 75/75 with leak detection disabled. A 32-byte malformed-parser recovery
leak found during the run was fixed with a Bison destructor and reran clean.
Real SAT solves still trigger pre-existing misaligned access and signed-shift
UB inside vendored ABC `cnfCut.c`; the UF lit run used a narrow suppression for
that directory while all other UBSan failures remained fatal. Python's legacy
no-op finalizers also prevent a leak-clean interpreter shutdown. Neither
finding is introduced by UF logic, but both should be tracked separately from
this merge.

## Remaining integration guidance

1. Review/merge the existing milestone and fixed commits in order; do not
   replace them with the competing `uf` branch wholesale.
2. Keep the new backend-generation and compound-result fixtures as release
   gates. They caught respectively an unsound answer and a batch fatal that
   both original suites missed.
3. In CI, qualify the inprobing fixture on the selected runtime backend and
   teach warning-sensitive checks about simplifying-MiniSat's documented
   fallback line.
4. Track the generic sanitizer-CMake issue, vendored ABC alignment UB, and
   Python ownership/finalizer cleanup independently. They are real maintenance
   work but do not change the UF verdicts established here.
5. Benchmark long-lived C services: declaration/expression tombstones trade a
   small process-lifetime metadata allocation for the promised stale-pointer
   safety of an ABI whose public handles are raw `void*` values.

Subject to normal code review, `uf_codex_fixed` is the branch to integrate.
