# UFSTP v2 target-test traceability

> Fixed-branch supplement: the original catalogue mapping below remains the
> specification map. `UFSTP-V2-FIXED-INTEGRATION-REPORT.md` records the later
> red-first audit additions: SAT-backend generation, compound-result
> liveness, formal shadowing, command transactions, public model permission,
> opaque C/Python handle lifetime, install consumers, deep/shared lowering,
> expanded CNF semantics, and imported differential/model/peer fuzzers.

This file maps every row in the normative v2 test catalogue to target-STP
evidence.  Unless a row explicitly says otherwise, each SMT-LIB test has both
`--incremental=off` (batch) and `--incremental=on` (persistent exact-stack)
`RUN` lines.  The `uf/` lit suite is also run once for every required SAT
backend.  Package-owned reference tests and validators are recorded in the
implementation report.

| Catalogue ID(s) | Target evidence |
|---|---|
| T-M0-01 | `UFSTP-V2-SEAM-RELOCATION.md`; package reconciliation and validator commands in the implementation report. |
| T-DNH-01, T-NOEAGER-01 | `UninterpretedFunctionsFrontend.IsDisabledByDefault`; `18-default-off-nonnullary-declare-fun.smt2`; `frontend-golden/aufbv-does-not-enable.smt2`; no eager clauses are emitted before a checker conflict. |
| T-FE-01 | `08-mixed-signature-roundtrip.smt2`, `frontend-golden/logic-policy.smt2`, and the frontend unit suite. |
| T-FE-02 | `09-malformed-arity-continues.smt2`, `10-malformed-sort-continues.smt2`, `source-sort-boundary.smt2`, and `FailedApplicationsRegisterNothing`. |
| T-FE-03 | `UninterpretedFunctionsCAPI.DefaultOffAndZeroArityAreRejected` and frontend signature units. |
| T-FE-04 | `UninterpretedFunctionsFrontend.DuplicateDeclarationsAreStableAndSignatureChangesFail` and namespace golden tests. |
| T-FE-05 | `frontend-golden/namespace-and-shadowing.smt2`, `frontend-golden/define-fun-bool-parameter.smt2`, and parser golden tests. |
| T-FE-06 | `09-malformed-arity-continues.smt2`, `10-malformed-sort-continues.smt2`, and `UninterpretedFunctionsFrontend.MalformedApplicationsAreAtomic`. |
| T-FE-07 | `frontend-golden/namespace-and-shadowing.smt2` and `let-specialization.smt2`. |
| T-FE-08 | `source-sort-boundary.smt2`, `frontend-golden/logic-policy.smt2`, `frontend-golden/aufbv-does-not-enable.smt2`, and `UninterpretedFunctionsFrontend.RejectsUnsupportedDirectSignatures`. |
| T-SCOPE-01 | `11-declaration-push-pop.smt2` and `declaration-push-pop-global.smt2`. |
| T-SCOPE-02 | `12-reset-assertions-keeps-declaration.smt2`, `13-reset-drops-declaration.smt2`, and `reset-lifecycle.smt2`. |
| T-SCOPE-03 | C, C++, and Python durable-handle ownership/destruction tests, plus the sanitizer run recorded in the report. |
| T-CANON-01, T-ACTIVE-01 | `DurableApplicationsAreTypedAndHashConsed`, `SubstitutionRebuildsDurableApplication`, `CompletedRootLoweringIsNestedFirstAndDeduplicated`, `define-fun-specialization.smt2`, and `let-specialization.smt2`. |
| T-LIVE-01, T-LIVE-02, T-NOAPPLY-01, T-GATE-01 | `result-liveness.smt2`, `14-hidden-boolean-result-unsat.smt2`, lowering/barrier units, release-mode suite, and explicit `UF_APPLY` barriers in bit-blasting. |
| T-SEP-01 | `theory-order.smt2`, `combined-model.smt2`, and the coordinator order assertions. |
| T-UF-01 | `01-unary-congruence-unsat.smt2` and `UFChecker.ReturnsStableUnaryConflictAndValidatedLemma`. |
| T-UF-02 | `02-noninjective-sat.smt2` and `UFChecker.PreservesNonInjectivity`. |
| T-UF-03 | `03-binary-congruence-unsat.smt2` and `UFChecker.KeepsTuplePositionsAndDeclarationsIndependent`. |
| T-UF-04 | `04-nested-congruence-unsat.smt2`, `define-fun-specialization.smt2`, and `let-specialization.smt2`. |
| T-UF-05 | `16-distinct-functions-sat.smt2` and the declaration-independence checker unit. |
| T-UF-06 | `05-boolean-predicate-unsat.smt2`, `14-hidden-boolean-result-unsat.smt2`, and mixed-sort checker units. |
| T-UF-07 | `17-interpreted-equal-arguments-unsat.smt2` and the differential interpreted-equality family. |
| T-UF-08 | `DurableApplicationsAreTypedAndHashConsed`, `CompletedRootLoweringIsNestedFirstAndDeduplicated`, and define-fun/let reuse tests. |
| T-UF-09 | Iterative completed-root traversal tests and nested-depth differential cases. |
| T-SORT-01 | `08-mixed-signature-roundtrip.smt2`, `source-sort-boundary.smt2`, `BooleanLoweringRetainsBoolSourceSort`, and `UFChecker.PreservesValuesWiderThanMachineWords`. |
| T-CNF-01, T-CNF-02 | `UFRefinement.BatchCNFExactlyImplementsCongruenceImplication` exhaustively checks the truth table and exact clauses; `PersistentCNFGuardsHelpersAndScopesItsCache` checks guarded helper/final clauses, widths, caches, blocks, and epochs. |
| T-VAL-01 | `UFChecker.ReturnsStableUnaryConflictAndValidatedLemma`, `OmitsOnlyIdenticalAndDuplicatePremises`, `DeduplicatesExactlyRepeatedPremiseAtoms`, and both refinement encoder tests. |
| T-LOOP-01, T-LOOP-03 | All conflict fixtures in both modes, `push-pop-scope.smt2`, `epoch-rebuild.smt2`, and the persistent guard/cache unit. |
| T-LOOP-02 | `theory-order.smt2` observes EXTCHK short-circuit before UFCHK. |
| T-COMB-01 | `06-array-read-as-uf-argument-unsat.smt2` and `fp-array-boundary.smt2`. |
| T-COMB-02 | `07-uf-result-as-array-index-unsat.smt2` and `fp-array-boundary.smt2`. |
| T-COMB-03 | `theory-order.smt2` observes independent EXTCHK and UFCHK conflicts and ordinary-replay short circuits. |
| T-COMB-04 | Source-sort rejection tests and the absence of any array/lambda UF encoding. |
| T-TERM-01 | The 240-seed differential campaign, repeated persistent checks, epoch churn, and six performance families. |
| T-MDL-01 | `15-function-model-active-only.smt2`, `active-model-scope.smt2`, and public-root replay. |
| T-MDL-02 | `active-model-scope.smt2`, `deferred-model.smt2`, and `UFChecker.ProducesDefaultSeedForDeclarationWithoutObservation`. |
| T-MDL-03 | `combined-model.smt2`, C/C++/Python model-value tests, and deterministic SMT-LIB model output. |
| T-API-01 | `UninterpretedFunctionsCAPI.CertifiedDurableValuesBatchAndRejection`, its persistent twin, C++ frontend API tests, and Python binding tests. |
| T-API-02 | `UninterpretedFunctionsCAPI.OwnershipTypingAndNonfatalRejection`, zero-arity/default-off rejection, and Python ownership checks. |
| T-DIFF-01 | `tests/ufstp/differential_fuzz.py`: 240 deterministic seeds, six families, four STP backends, both modes, and cvc5/Bitwuzla/Z3. |
| T-BACKEND-01 | The backend/assertion matrix in the report: CaDiCaL, CryptoMiniSat, MiniSat, Riss, simplifying-MiniSat, assertions enabled/disabled, batch/persistent. |
| T-PERF-01 | `tests/ufstp/performance.py`: durable traversal/lowering, define-fun reuse, nested let, identical-block reuse, pop scope, and epoch rebuild at scales 16/64 in both modes. |
| DR-T-DEFINE-01 | `define-fun-specialization.smt2` and `frontend-golden/define-fun-bool-parameter.smt2`. |
| DR-T-LET-01 | `let-specialization.smt2` and namespace/shadowing golden tests. |
| DR-T-MODE-EQUIV-01 | `mode-equivalence/reference-profile.smt2`, every root UF lit test's two mode runs, and the differential campaign. |
| DR-T-PUSHPOP-01 | `push-pop-scope.smt2` and the differential push/conflict/pop sequence. |
| DR-T-EPOCH-01 | `epoch-rebuild.smt2` with `--incremental-reencode-limit=1` and the performance epoch family. |
| DR-T-LIVE-MODES-01 | `result-liveness.smt2` and `14-hidden-boolean-result-unsat.smt2` in both modes. |
| DR-T-ORDER-MODES-01 | `theory-order.smt2` in both modes. |
| DR-T-NOMODEL-UFCHK-01 | `no-public-model-check.smt2` in both modes. |
| DR-T-DEFERRED-MODEL-01 | `deferred-model.smt2` and `active-model-scope.smt2`. |
| DR-T-SOURCESORT-01 | `source-sort-boundary.smt2`, mixed-signature tests, and direct signature-rejection units. |
| DR-T-GRAMMAR-01 | Frontend golden directory, malformed-command integration tests, and parser atomicity units. |
| DR-T-RESET-01 | `reset-lifecycle.smt2`, reset/reset-assertions tests, and global-declarations push/pop. |
| DR-T-API-HANDLE-01 | C/C++/Python certified durable-handle value and ownership tests. |
| DR-T-FP-BOUNDARY-01 | `fp-array-boundary.smt2` and completed-root lowering-order checks. |

The following catalogue rows are conditional, not skipped mandatory tests:

- T-EAGER-01 belongs to the optional selected-eager production profile.  The
  reference profile is intentionally no-eager and is covered by T-NOEAGER-01.
- T-OPT-01 belongs to the optional multi-lemma production profile.  The
  implemented reference profile emits exactly one deterministic conflict.
- T-ALT-CC-01 and T-SORT-EXT-01 are explicitly marked `future` by the
  normative catalogue.  Neither future profile is implemented.
