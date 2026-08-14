# UFSTP v2.0.0 pre-implementation seam relocation

## Baseline identity

- Repository: `/home/avj/clones/stp/uf_codex`
- Branch at inspection: `uf_codex`
- Target/HEAD: `e27b10d0b6569821b5b2cd275c81ab5a8b8fc984`
- Authoritative archive: `stp-uninterpreted-functions-spec-v2.0.0.zip`
- Archive SHA-256: `5f0e4d40899312f52699b121c6813358721aabd8205c870abdd746603853b326`
- Archive integrity: `unzip -t` passed; every extracted file passed the supplied
  `SHA256SUMS` manifest.
- Search rule: symbols were relocated at the pinned target; specification line
  numbers were treated as advisory.

No production UF implementation, `UF_APPLY` kind, `UFContext`, dynamic
Ackermann checker, or UF enable flag exists at this target.  The existing
`Cpp_interface::Function` is a `define-fun` macro record and is not UF
ownership.

## Relocated baseline seams

| Seam | Current file and symbol | Disposition and observed drift |
|---|---|---|
| `candidate_result_check` | `lib/AbsRefineCounterExample/CounterExample.cpp:2720`, `AbsRefine_CounterExample::CallSAT_ResultCheck`; `lib/Incremental/IncrementalExactStack.cpp:530,562` | Present. Split by solve mode as specified. UF must be inserted after EXTCHK and before ordinary replay. |
| `outer_refinement_driver` | `lib/STPManager/STP.cpp:106,264`, `STP::TopLevelSTP` / `TopLevelSTPAux`; `lib/Incremental/IncrementalExactStack.cpp:247`, `exactStackCheckSat` | Present. Batch owns `ASTTrue` re-entry; persistent owns same-block-assumption re-entry. |
| `uf_bind_point` | Completed root in `STP::TopLevelSTP`; assembled exact block in `IncrementalSolver::Impl::exactStackCheckSat` | New design required. Both points are before FP, array, and ordinary preprocessing as required. |
| `candidate_model_access` | `lib/AbsRefineCounterExample/CounterExample.cpp`, construction and scalar lookup; `lib/Incremental/IncrementalExactStack.cpp` plus pending-model state in `lib/Incremental/IncrementalSolverImpl.h` | Present and split. UF activity must force internal candidate construction independently of public model production. |
| `incremental_cnf` | `include/stp/Sat/SATSolver.h`; `lib/AbsRefineCounterExample/AbstractionRefinement.cpp:136`, `getEquals`; exact-stack guard insertion in `lib/Incremental/IncrementalExactStack.cpp` | Present. Shared semantics require distinct query-local and block/epoch-scoped adapters. |
| `sat_reentry` | `lib/STPManager/STP.cpp:892`, `CallSAT_ResultCheck(... ASTTrue ...)`; `lib/Incremental/IncrementalExactStack.cpp:562`, recheck with unchanged `assumptions` | Present and matches the normative split. |
| `result_liveness` | `lib/ToSat/ToSATAIG.cpp:166`, `mark_variables_as_frozen`; `lib/Incremental/IncrementalSolverImpl.h:2334`, `totalizeSymbol` | Present. Batch's legacy width loop needs Bool-safe UF registration; persistent already uses `max(1, width)`. |
| `substitution_protection` | `lib/Simplifier/SubstitutionMap.cpp:117,139`, `SubstitutionMap::replace` | Present. It must rebuild durable UF children before lowering and protect generated UF scalars afterward. |
| `extensional_array_solver` | `lib/Extensionality/` and calls in both candidate paths | Present. Ownership remains separate; coordinator order is EXTCHK then UFCHK with first-conflict short circuit. |
| `declaration_and_application_frontend` | `lib/Parser/smt2.y`; `lib/Parser/smt2.lex:179`; `lib/Interface/cpp_interface.cpp:295,322,331,337` | Present but supports only nullary declarations plus `define-fun`. Add a distinct typed UF declaration/application funnel. |
| `declaration_lifecycle` | `include/stp/cpp_interface.h::SolverFrame`; frame/reset/global-declaration operations in `lib/Interface/cpp_interface.cpp` | Present. UF declarations must join the same frame/adoption rules while solve/model state is invalidated separately. |
| `application_and_signature_types` | `include/stp/AST/SourceSort.h`; `lib/AST/ASTKind.kinds` (current final kind `ARRAY_EQ`); `lib/AST/ASTNode.cpp:532`, `deriveSourceSort` | Present foundation, new UF design required. Append `UF_APPLY` to preserve exported numeric kinds; accept only Bool and nonzero BV source sorts. |
| `function_model_printer` | `lib/AbsRefineCounterExample/CounterExample.cpp:2084,2282`; `lib/Printer/SMTLIB2Printer.cpp`; public model entry points in `lib/Interface/cpp_interface.cpp` | Present. Add certified SourceSort-aware UF tables/defaults without exposing introduced symbols. |
| `c_api` | `include/stp/c_interface.h`; `lib/Interface/c_interface.cpp`; Python binding sources under `bindings/python` | Present, with untyped opaque handles. New context-owned declaration and durable application handle surfaces are required. |

## Relocated host control seams

| Contract | Current location | Finding |
|---|---|---|
| Persistent route selection | `lib/Incremental/IncrementalSolver.cpp:246`, `checkSatBody`; `lib/Incremental/IncrementalDriverStages.cpp:172,201` | Fragment classification/route selection is separate from exact-stack execution. Both bypasses must be closed for active UF. |
| Persistent plain-solve bypass | `lib/Incremental/IncrementalExactStack.cpp:166,499`, `solvePlainExactStack` | Present; active UF must disable it. |
| Encoding epoch rotation | `lib/Incremental/IncrementalSolverImpl.h:2538`, `rotateEncodingEpoch` | Present; UF persistent caches, active mappings, and model certification must be released here. |
| Source-sort memoization | `lib/AST/ASTNode.cpp:490,532`; `include/stp/AST/ASTNode.h:274` | Present; declaration identity supplies the `UF_APPLY` codomain. |
| Model printing/materialization | `CounterExample.cpp:2282`; `cpp_interface.cpp:1241,1347` | Present; immediate and deferred paths need the same certified UF state. |
| CLI feature surface | `tools/stp/main.cpp:302` (adjacent array option); `include/stp/STPManager/UserDefinedFlags.h` | Present insertion points. Logic selection is independent from feature enablement. |
| Library assembly | `lib/CMakeLists.txt:53-68` and `stp_lib_targets` | Present. Add a dedicated `UninterpretedFunctions` object target. |
| Test registration | `tests/CMakeLists.txt`; `tests/query-files`, `tests/api`, `tests/unit-tests` | Present. Mandatory UF catalogue coverage can be registered without changing the harness architecture. |

The persistent seam is intentionally distributed: executable route/refinement
logic is in `IncrementalExactStack.cpp`, while declarations, totalization, and
epoch-owned state are in `IncrementalSolverImpl.h`.  This is not an invalidating
path drift; both halves are load-bearing.

## New mandatory seams to add

The following package-prescribed components have no predecessor and will be
added under `include/stp/UninterpretedFunctions/` and
`lib/UninterpretedFunctions/`: immutable `UFSignature`/`UFDecl`, context
registry, durable application view, completed-root lowering, one pure checker,
one shared native-CNF encoder, distinct batch and persistent adapters, and
certified model/handle state. Frontend, AST, API, printer, batch, persistent,
CNF/liveness, lifecycle, CMake, and test seams above are their integration
points.

## Drift verdict

No repository drift invalidates a normative UFSTP v2.0.0 contract. The target
SHA is exact, all named symbols can be relocated, and the split persistent
implementation agrees with the host map. Implementation may proceed.

One supplied *test fixture* conflicts with the normative lifecycle contract:
`tests/smt2/12-reset-assertions-keeps-declaration.smt2` expects a declaration to
survive `reset-assertions` without first setting `:global-declarations true`.
The specification and current host contract both make that option false by
default and require declarations to be dropped. The archive will remain
untouched; implementation follows the normative contract. The proposed package
amendment is to add `(set-option :global-declarations true)` to that fixture (or
rename/change its expected result to test the default scoped behavior).
