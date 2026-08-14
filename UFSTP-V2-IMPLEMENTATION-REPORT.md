# UFSTP v2.0.0 implementation report

> **Historical report.** This document records the original `uf_codex`
> implementation at `90c57a4a`. A subsequent cross-branch audit found
> release-blocking backend-cache, batch-liveness, frontend, and API defects,
> so its completion statement is not the current integration verdict. The
> fixes and independently rerun evidence are recorded in
> `UFSTP-V2-FIXED-INTEGRATION-REPORT.md`.

Date: 2026-08-14 (Europe/London)

## Completion statement

STP now implements the complete mandatory `UFSTP-REFERENCE` profile from the
supplied `stp-uninterpreted-functions-spec-v2.0.0.zip`. All 102 requirements
tagged `MUST`, CI-mandatory `OBL-09`, milestones M0 through M7, and all 64
applicable mandatory/active target-test catalogue rows are implemented and
pass. There are no skipped mandatory tests and no approved normative
deviations.

The selected profile is the required durable-application, one-conflict,
no-eager reference design. The optional production optimizations and future
profiles were not selected.

## Target and specification provenance

- Repository: `/home/avj/clones/stp/uf_codex`
- Working branch: `uf_codex`
- Required baseline: `e27b10d0b6569821b5b2cd275c81ab5a8b8fc984`
- Verified baseline: exact match; no successor drift was used
- Implementation tip before this report:
  `9f3642088190cd466439f0ab86bf5fe03d02fedf`
- Authoritative archive: `stp-uninterpreted-functions-spec-v2.0.0.zip`
- Archive SHA-256:
  `5f0e4d40899312f52699b121c6813358721aabd8205c870abdd746603853b326`
- `unzip -t` result: pass
- Extracted `SHA256SUMS` result: pass for every member
- Specification archive and extracted package: not modified

`SPECIFICATION.md` was read first and treated as highest-precedence. The
implementation guide, requirements, profiles, host contract/code map, seam
maps, algorithms, schemas, catalogue, reference implementation, fixtures,
traceability, provenance, and validation tools were then reconciled against
the exact baseline. The pre-edit relocation record is
`UFSTP-V2-SEAM-RELOCATION.md`.

## Reviewable milestone commits and diffstat

| Commit | Milestone and content | Diffstat |
|---|---|---|
| `856a4801` | M0: v2 seam relocation and drift verdict | 1 file, +81 |
| `09cf04e5` | M1: typed frontend, declaration lifecycle, durable handles | 26 files, +1206/-39 |
| `8832aa38` | M2: completed-root lowering, barriers, protected UF scalars | 14 files, +965/-99 |
| `40f4bc17` | M3: pure checker, lemma validation, shared CNF semantics, adapters | 9 files, +2214 |
| `d3e679dd` | M4-M5: batch and persistent coordination/refinement | 8 files, +327/-30 |
| `f0ebc700` | M6: deterministic models and C/C++/Python durable APIs | 12 files, +827/-13 |
| `5e2f101d` | M7: acceptance, differential, and performance tests | 41 files, +1156 |
| `2fabb6ce` | M7: complete target-test traceability | 1 file, +77 |
| `9f364208` | M7: make model-producing fixture host-contract explicit | 1 file, +1 |

Aggregate baseline-to-implementation diff before this report: 97 files,
6,838 insertions, 165 deletions.

## Implemented requirement IDs

The implemented mandatory inventory is:

- `HOST-01` through `HOST-10`
- `FE-00` through `FE-10`
- `PRE-00` through `PRE-10`
- `GATE-00` through `GATE-09`
- `CHK-01` through `CHK-09`
- `LEM-01` through `LEM-06`
- `CNF-01` through `CNF-08`
- `LOOP-01` through `LOOP-07`
- `MDL-01` through `MDL-08`
- `OBL-01` through `OBL-11`, including `OBL-09` (`MUST in CI`)
- `UF2-REP-01`, `UF2-SORT-01`, `UF2-BATCH-01`, `UF2-INC-01`,
  `UF2-INC-02`, `UF2-LIVE-01`, `UF2-LOOP-01`, `UF2-MDL-01`,
  `UF2-LIFE-01`, `UF2-FE-01`, `UF2-API-01`, and `UF2-FP-01`

Unselected optional requirements are `OPT-01` through `OPT-05` and `OPT-08`.
Future requirements `OPT-06` and `OPT-07` are also unselected. This is the
normative `UFSTP-REFERENCE` choice: exactly one deterministic conflict per
candidate, no selected eager pairs, and no alternate congruence-closure or
sort-extension profile.

All 68 catalogue rows are mapped in `UFSTP-V2-TEST-TRACEABILITY.md`. Of these,
64 are applicable mandatory/active target obligations. `T-EAGER-01` and
`T-OPT-01` belong to unselected optional profiles; `T-ALT-CC-01` and
`T-SORT-EXT-01` are future rows, not skipped mandatory tests.

## Milestone and architecture result

| Milestone | Implemented result |
|---|---|
| M0 | Exact-target integrity, source-seam relocation, drift evidence, and package reconciliation |
| M1 | Default-off flag; independent logic policy; typed non-nullary UF declarations/applications; atomic diagnostics; namespace, frame, reset, and durable-handle ownership |
| M2 | Durable typed `UF_APPLY`; iterative nested-first completed-root lowering; stable deduplication; Bool/nonzero-BV `SourceSort`; substitution, simplification, FP/array ordering, liveness, and bitblast barriers |
| M3 | One stateless pure dynamic-Ackermann checker; deterministic conflict and model seed; model-false lemma validation; exact fully reified Bool/BV CNF; separate mutable adapters |
| M4-M5 | `EXTCHK` then `UFCHK` then ordinary replay; fresh-query batch re-entry; persistent same-block-assumption re-entry; bypass closure; block guards and block/epoch-qualified caches |
| M6 | Deterministic active-declaration `define-fun` models; internal/public model separation; deferred persistent publication; durable C/C++/Python value queries; no lowered-symbol exposure |
| M7 | Full suite, backend/mode/assertion matrix, differential references/fuzzing, lifecycle sanitizers, performance families, and complete traceability |

## Changed source seams

| Seam | Implemented files/symbols and contract |
|---|---|
| Feature and logic policy | `UserDefinedFlags::uninterpreted_functions`, CLI `--uninterpreted-functions`, and SMT-LIB logic handling accept both `QF_UFBV` and `QF_AUFBV` only when the feature is explicitly enabled. Neither logic enables the feature. |
| Typed frontend and lifecycle | `smt2.lex`, `smt2.y`, `Cpp_interface::{declareUninterpretedFunction,declareScopedUninterpretedFunction,applyUninterpretedFunction}`, and `UFContext` implement the nonempty Bool/BV signature funnel, atomic failures, namespace priority, scoped/global declarations, reset, and destruction. |
| Durable representation | `UF_APPLY` is appended to `ASTKind`; `ASTNode`, hashing/simplifying factories, `UFSignature`, `UFDecl`, and `UFContext::apply` retain declaration identity and exact `SourceSort` while handles live independently of solve-local symbols. |
| Completed-root lowering | `UFLowering::lowerCompletedRoot` is called from `STP::TopLevelSTP` and `IncrementalSolver::Impl::exactStackCheckSat` before FP, array, and ordinary preprocessing. It traverses iteratively, lowers nested applications first, deduplicates, names non-leaf actuals, and rejects any barrier crossing. |
| Protection and liveness | `SubstitutionMap`, `RemoveUnconstrained`, `ToSATAIG::mark_variables_as_frozen`, `BitBlaster`, and persistent `totalizeSymbol` rebuild pre-barrier children, protect generated scalars, make Bool results one SAT bit, and forbid downstream `UF_APPLY`. |
| Pure checker and lemma | `UFChecker::check`, `UFLemma`, and immutable `LoweredApplicationView` implement one shared arbitrary-width Bool/BV dynamic-Ackermann check, declaration/tuple separation, non-injectivity, deterministic ordering, duplicate-premise removal, and model-false validation. |
| Batch adapter | `UFBatchAdapter` owns query-local candidate values, equality literals, unguarded clauses, certification, and `ASTTrue` re-entry for one fresh SAT query. |
| Persistent adapter | `UFPersistentAdapter` owns one exact-stack block in one encoding epoch. Every helper and final semantic clause is block-guarded; caches are keyed by block and epoch and cleared by `rotateEncodingEpoch`. Re-entry preserves the same assumptions. |
| Theory coordinator | `AbsRefine_CounterExample::CallSAT_ResultCheck` preserves separate extensionality and UF owners and enforces `EXTCHK -> UFCHK -> ordinary replay`, with first-conflict short-circuiting. UF activity forces an internal candidate independently of `:produce-models`. |
| Persistent routing | `IncrementalSolver`, `IncrementalDriverStages`, `IncrementalExactStack`, and `IncrementalSolverImpl` close the direct/plain bypasses whenever UF is active and invalidate active/pending/cached state on stack, block, assertion, reset, epoch, or context changes. |
| Models and APIs | `UFModel`, counterexample replay, `Cpp_interface::getUninterpretedApplicationValue`, `vc_declareFun`, `vc_applyFun`, `vc_getUFApplicationValue`, and Python wrappers publish only certified source-level values and deterministic total interpretations. |
| Assembly and tests | Dedicated `UninterpretedFunctions` library objects, three native unit suites, C and Python API coverage, 37 dual-mode lit files, differential fuzzing, performance evidence, and catalogue traceability are registered in CMake. |

## Package validation

The package was validated on an isolated copy so its generated files in the
repository remained untouched:

```sh
cd /tmp/ufstp-v2-spec-validation.z5aRMk
/usr/bin/python3 tools/generate_traceability.py
/usr/bin/python3 tools/generate_traces.py
/usr/bin/python3 tools/validate_spec.py
/usr/bin/python3 -m unittest discover -s tests -v
```

Results:

- Traceability generation: pass; 111 requirements, 82 sources, 68 tests
- Reference-trace generation: pass; 9 fixture traces
- Schema/package validator: pass; 111 requirements (99 inherited + 12 v2),
  68 tests (54 inherited + 14 v2), 84 checked anchors, exact baseline target
- Reference implementation tests: 46/46 pass in 2.029 seconds

## Build configurations and complete-suite results

Assertions-enabled all-backend build:

```sh
cmake -S . -B /tmp/ufstp-v2-all -G Ninja \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DENABLE_ASSERTIONS=ON -DENABLE_TESTING=ON \
  -DCMAKE_COMPILE_WARNING_AS_ERROR=OFF -DSTP_ALLOCATOR=system \
  -DLIT_TOOL=/tmp/ufstp-v2-tools/bin/lit \
  -DUSE_CADICAL=ON \
  -DCADICAL_DIR=/home/avj/clones/stp/deps/cadical-3.0.1 \
  -Dcryptominisat5_DIR=/home/avj/clones/stp/modernize-ci/deps/install/lib/cmake/cryptominisat5 \
  -DUSE_MINISAT=ON \
  -Dminisat_DIR=/home/avj/clones/stp/modernize-ci/deps/install/lib/cmake/minisat \
  -DUSE_RISS=ON -DRISS_DIR=/home/avj/clones/stp/deps/deps-riss
cmake --build /tmp/ufstp-v2-all --parallel
PATH=/tmp/ufstp-v2-tools/bin:$PATH \
  ctest --test-dir /tmp/ufstp-v2-all --output-on-failure
```

Result: build pass; complete current STP suite 133/133 pass, 0 failed, final
current-tree run 82.72 seconds. The registered query test includes all 630 lit
query files; native unit, C API, Python API, FP, array, incremental, and legacy
tests are included.

Assertions-off Release all-backend build:

```sh
cmake -S . -B /tmp/ufstp-v2-release -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DENABLE_ASSERTIONS=OFF -DENABLE_TESTING=ON \
  -DCMAKE_COMPILE_WARNING_AS_ERROR=OFF \
  -DLIT_TOOL=/tmp/ufstp-v2-tools/bin/lit \
  -DUSE_CADICAL=ON \
  -DCADICAL_DIR=/home/avj/clones/stp/deps/cadical-3.0.1 \
  -Dcryptominisat5_DIR=/home/avj/clones/stp/modernize-ci/deps/install/lib/cmake/cryptominisat5 \
  -DUSE_MINISAT=ON \
  -Dminisat_DIR=/home/avj/clones/stp/modernize-ci/deps/install/lib/cmake/minisat \
  -DUSE_RISS=ON -DRISS_DIR=/home/avj/clones/stp/deps/deps-riss
cmake --build /tmp/ufstp-v2-release --parallel
PATH=/tmp/ufstp-v2-tools/bin:$PATH \
  ctest --test-dir /tmp/ufstp-v2-release --output-on-failure
```

Result: build pass; complete current STP suite 133/133 pass, 0 failed, 23.95
seconds.

An initial GCC 15 warnings-as-errors experiment stopped in the vendored ABC
source `lib/extlib-abc/src/base/abc/abcHieNew.c` on an existing
`-Warray-bounds` diagnostic. No STP or UF source emitted the failing warning.
The conformance builds therefore use the repository's supported
warnings-not-errors configuration and retain all normal warnings. This is a
host/toolchain observation, not a UF requirement deviation.

## Backend, solve-mode, and assertion matrix

The UF lit matrix was run with the following command shape for both build
configurations:

```sh
for backend in --cadical --cryptominisat --minisat --riss --simplifying-minisat
do
  PATH=/tmp/ufstp-v2-tools/bin:$PATH \
    lit -s --config-prefix=RelWithDebInfo --filter='uf/' \
      --param solver_params="$backend" /tmp/ufstp-v2-all/tests/query-files
done

for backend in --cadical --cryptominisat --minisat --riss --simplifying-minisat
do
  PATH=/tmp/ufstp-v2-tools/bin:$PATH \
    lit -s --config-prefix=Release --filter='uf/' \
      --param solver_params="$backend" /tmp/ufstp-v2-release/tests/query-files
done
```

Every one of the 37 discovered UF files has one forced
`--incremental=off` batch run and one forced `--incremental=on` persistent run.

| Build | Assertions | Backend | Batch | Persistent | Lit result |
|---|---:|---|---:|---:|---:|
| RelWithDebInfo | on | CaDiCaL | pass | pass | 37/37 |
| RelWithDebInfo | on | CryptoMiniSat | pass | pass | 37/37 |
| RelWithDebInfo | on | MiniSat | pass | pass | 37/37 |
| RelWithDebInfo | on | Riss | pass | pass | 37/37 |
| RelWithDebInfo | on | simplifying-MiniSat | pass | pass | 37/37 |
| Release | off | CaDiCaL | pass | pass | 37/37 |
| Release | off | CryptoMiniSat | pass | pass | 37/37 |
| Release | off | MiniSat | pass | pass | 37/37 |
| Release | off | Riss | pass | pass | 37/37 |
| Release | off | simplifying-MiniSat | pass | pass | 37/37 |

This is 740 forced UF solver invocations across the final assertion/backend
matrix (37 files x 2 modes x 5 backends x 2 builds), with no skip.

## Differential and fuzz evidence

```sh
/usr/bin/python3 tests/ufstp/differential_fuzz.py \
  --stp /tmp/ufstp-v2-all/stp \
  --backend cadical=--cadical \
  --backend cryptominisat=--cryptominisat \
  --backend minisat=--minisat \
  --backend riss=--riss \
  --reference cvc5=/home/avj/clones/cvc5/main/build/bin/cvc5 \
  --reference bitwuzla=/home/avj/clones/bitwuzla/main/build/src/main/bitwuzla \
  --reference z3=/home/avj/clones/z3/master/build/z3 \
  --seeds 240 \
  --evidence-out /tmp/ufstp-v2-differential-all.json
```

Result: pass. The deterministic campaign covered 240 seeds, six families,
three checks per seed, four STP backend families in both modes, and three
independent reference solvers: 2,640 solver runs total. Families were nested
congruence, non-injectivity, Boolean predicate, interpreted equality, array
actuals, and declaration separation. Corpus SHA-256:
`6333298d059aeba45130d73b1738f62a72273f671ae426b13dac82d0be73d62f`.

Measured aggregate seconds were: Bitwuzla 2.199243, cvc5 3.607651, Z3
3.427730; STP CaDiCaL batch/persistent 6.761878/2.585308,
CryptoMiniSat 6.848825/2.507192, MiniSat 7.036815/3.124132, and Riss
6.845351/2.580471.

## Performance evidence

```sh
/usr/bin/python3 tests/ufstp/performance.py \
  --stp /tmp/ufstp-v2-all/stp \
  --scales 16,64 --repeats 3 \
  --evidence-out /tmp/ufstp-v2-performance.json
```

Result: pass for all six families, both modes, both scales, and all three
repeats. Corpus SHA-256:
`229f2dd200a80bb59f30706bcec5d822ed4780e353a1c574835de75adeb3a00a`.

Scale-64 median seconds:

| Family | Batch | Persistent |
|---|---:|---:|
| Durable traversal/lowering | 0.022589 | 0.014787 |
| `define-fun` reuse | 0.025713 | 0.014756 |
| Nested `let` | 0.022370 | 0.006383 |
| Identical-block reuse | 0.530908 | 0.013104 |
| Pop scope | 0.149367 | 0.030795 |
| Encoding-epoch rebuild | 0.366565 | 0.118212 |

## Sanitizer and lifecycle evidence

Clang ASan+UBSan configuration:

```sh
cmake -S . -B /tmp/ufstp-v2-sanitize-manual -G Ninja \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DCMAKE_C_COMPILER=/usr/bin/clang \
  -DCMAKE_CXX_COMPILER=/usr/bin/clang++ \
  -DCMAKE_C_FLAGS=-fsanitize=address,undefined \
  -DCMAKE_CXX_FLAGS=-fsanitize=address,undefined \
  -DCMAKE_EXE_LINKER_FLAGS=-fsanitize=address,undefined \
  -DCMAKE_SHARED_LINKER_FLAGS=-fsanitize=address,undefined \
  -DENABLE_ASSERTIONS=ON -DENABLE_TESTING=ON \
  -DCMAKE_COMPILE_WARNING_AS_ERROR=OFF -DSTP_ALLOCATOR=system \
  -DLIT_TOOL=/tmp/ufstp-v2-tools/bin/lit \
  -DUSE_CADICAL=ON \
  -DCADICAL_DIR=/home/avj/clones/stp/deps/cadical-3.0.1 \
  -DNOCRYPTOMINISAT=ON -DUSE_MINISAT=OFF -DUSE_RISS=OFF
```

Focused native/API lifecycle run:

```sh
ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
UBSAN_OPTIONS=halt_on_error=0:print_stacktrace=0 \
PATH=/tmp/ufstp-v2-tools/bin:$PATH \
ctest --test-dir /tmp/ufstp-v2-sanitize-manual \
  -R '(uninterpreted-functions-api|UninterpretedFunctionsFrontend|UFChecker|UFRefinement)' \
  --output-on-failure
```

Result: 4/4 pass. A separate `halt_on_error=1` UBSan run of the pure
`UFChecker` and `UFRefinement` units also passed. The sanitizer build's 37-file
UF lit suite passed 37/37 with leak-detecting ASan active.

Python bindings require the ASan runtime to be loaded before `ctypes` opens
`libstp.so`; the direct run was:

```sh
LD_PRELOAD=/usr/lib64/clang/21/lib/linux/libclang_rt.asan-x86_64.so \
ASAN_OPTIONS=detect_leaks=0:halt_on_error=1 \
UBSAN_OPTIONS=halt_on_error=0:print_stacktrace=0 \
/usr/bin/python3.14 /tmp/ufstp-v2-sanitize-manual/tests/api/python/tests.py
```

Result: 63/63 pass, including the durable UF application/value test; ASan
reported no UF/API lifetime or memory error. UBSan reports an existing
third-party ABC pool-alignment issue beginning at
`lib/extlib-abc/src/sat/cnf/cnfCut.c:51` (and its downstream CNF accesses),
plus ABC's existing signed left-shift at `cnfCut.c:99`. Those reports occur in
non-UF baseline array/CNF tests, reproduce outside the pure UF components, and
are not hidden or reclassified as UF conformance failures.

The repository's built-in `-DSANITIZE=ON` convenience option also has a host
CMake ordering defect at this baseline: it rewrites the cached C++ compiler to
the non-absolute literal `clang++` after the top-level `project()`, and the
nested mimalloc `project()` then rejects it. The explicit compiler/flag
configuration above provides the intended instrumentation without changing
the source tree.

## Fixture drift and deviations

There are no implementation deviations from a normative requirement. Two
archive fixtures required target-side host-contract corrections; the archive
itself remains unchanged.

1. `tests/smt2/12-reset-assertions-keeps-declaration.smt2` in the archive
   expects a declaration to survive `reset-assertions` without setting
   `:global-declarations true`. This contradicts normative `FE-09`, `PRE-10`,
   and `UF2-LIFE-01`, as well as the baseline host behavior. Target evidence:
   `tests/query-files/uf/12-reset-assertions-keeps-declaration.smt2` explicitly
   enables global declarations; `13-reset-drops-declaration.smt2` and
   `reset-lifecycle.smt2` cover the default drop behavior. Proposed package
   amendment: add `(set-option :global-declarations true)` to archive fixture
   12, or rename it and change its expected result to exercise default scope.

2. `tests/smt2/02-noninjective-sat.smt2` in the archive calls `get-model`
   without `(set-option :produce-models true)`. Debug assertions happened to
   materialize a model, but the baseline Release host correctly reports that
   model production was not enabled. Target evidence:
   `tests/query-files/uf/02-noninjective-sat.smt2` sets the option explicitly
   and passes in both builds/modes/backends. The `T-UF-02`, `CHK-06`, and
   `OBL-05` non-injectivity verdict remains unchanged. Proposed package
   amendment: add the option when the fixture intends to inspect model output.

One integration defect found during the backend campaign was corrected before
the M3 commit: a valid UF blocking clause can make MiniSat immediately UNSAT;
the adapter now lets the next solver check certify that result instead of
treating immediate UNSAT as a fatal insertion error. The all-backend matrix and
differential campaign cover the correction.

## Remaining issues

- Mandatory UFSTP issue: none.
- Approved deviation: none.
- Optional/future profiles: intentionally not implemented, as listed above.
- Host/tooling observations: the vendored ABC GCC 15 warning, ABC UBSan
  alignment/shift findings, and built-in sanitizer CMake ordering issue are
  recorded above. They pre-exist and do not alter UF semantics or acceptance.

## Artifact hashes

| Artifact | SHA-256 |
|---|---|
| Authoritative v2 archive | `5f0e4d40899312f52699b121c6813358721aabd8205c870abdd746603853b326` |
| `UFSTP-V2-SEAM-RELOCATION.md` | `5271e561bb761037278240b4d674abdab6bfb2ea21cd00e09f228bd7c6fe052e` |
| `UFSTP-V2-TEST-TRACEABILITY.md` | `ca2b665ceaf650999c3967ffae7d8a28a08a5db4b3cba40c518416d6afc2a264` |
| `tests/ufstp/differential_fuzz.py` | `f0a79ab4640b875a4cb121770d66918de122e380723548e82703b0b539973acf` |
| Differential evidence JSON | `a90399f20da3f5e6e02bcb1f9e780f2be0523d315403080843890fa2e9718019` |
| `tests/ufstp/performance.py` | `12cba1c8540104d5140afe7d7fe83478e7c1061006d232d8738d0fbfbf4deb34` |
| Performance evidence JSON | `d631ec6e57cf2fa53d10f058b90f18b537d3a0b9ba7f4d94bbd024f201772372` |
| Assertions-enabled `stp` | `4fd0c2d922c921ac3a3b770c8661bba44e33817540a36be735804b8e7b40992b` |
| Assertions-off Release `stp` | `8ee26e4ac732818f5feb938be2e7fe3104e2282ac70a5e532c205ef8791c5d55` |
| Sanitized `stp` | `28a7e776d0b3c5de3e7913de0ac323c23f4e5f9085588e7c0d757395991a544b` |
| Assertions-enabled `libstp.so.2.4` | `23ecdb96f8f4b61dc592f42b9edc49fdedbcfccc9e8056388cd5cb9c5f4b7d7f` |
| Assertions-off Release `libstp.so.2.4` | `2ab3900607187c83e5b9aeffbcbf7492b5ea2a4548061fb9138a41277974520a` |

The evidence JSON files were emitted outside the source tree at the exact
paths shown in their commands; their complete data is summarized above.

## Final repository status

All implementation, tests, traceability, seam evidence, and this report are
intentional tracked artifacts. Both submodules touched idempotently by CMake's
vendored patch application were restored to their recorded commits after the
last build, and tracked files/submodules are clean.

The supplied specification archives and their pre-existing extracted trees
remain untracked and untouched. They are intentionally not deleted, modified,
or committed. Thus `git status --untracked-files=no` is clean; an ordinary
status lists only those supplied input archives/extractions.
