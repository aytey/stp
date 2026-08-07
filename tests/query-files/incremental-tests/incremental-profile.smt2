; The opt-in profiler reports deterministic work counters as well as timings.
; Changing the deepest level rolls CBP back to the two-level common prefix,
; then feeds only the replacement suffix. The forced-reset run is a diagnostic
; oracle for both the answers and the old prefix re-feed counters. Elapsed
; values are deliberately not checked.
; RUN: %solver --incremental --incremental-profile --check-sanity %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --incremental-profile --incremental-cbp-reset --check-sanity %s 2>&1 | %OutputCheck --check-prefix=RESET %s
; RUN: %solver --incremental %s 2>&1 | %OutputCheck --check-prefix=QUIET %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))

(push 1)
(assert (= x #x01))
(push 1)
(assert (= (bvadd x y) #x03))
; CHECK: Incremental profile: check=1 levels=3 total-us=[0-9]+.*cbp-reset-us=[0-9]+ cbp-rollback-us=[0-9]+ cbp-feed-us=[0-9]+ cbp-fresh-feed-us=[0-9]+ cbp-refeed-us=[0-9]+.*initial-sat-us=[0-9]+ refinement-sat-us=[0-9]+
; CHECK: Incremental profile cbp/backend: check=1 cbp-resets=0 cbp-divergences=0 cbp-rollbacks=0 cbp-rolled-levels=0.*cbp-fed-levels=3 cbp-fresh-levels=3 cbp-refed-levels=0 cbp-fed-nodes=9 cbp-fresh-nodes=9 cbp-refed-nodes=0
; CHECK: Incremental profile total: checks=1
; CHECK: ^sat
; RESET: Incremental profile cbp/backend: check=1 cbp-resets=0 cbp-divergences=0 cbp-rollbacks=0 cbp-rolled-levels=0.*cbp-fed-levels=3 cbp-fresh-levels=3 cbp-refed-levels=0 cbp-fed-nodes=9 cbp-fresh-nodes=9 cbp-refed-nodes=0
; RESET: ^sat
; QUIET-NOT: Incremental profile
; QUIET: ^sat
(check-sat)

(pop 1)
(push 1)
(assert (= (bvadd x z) #x04))
; CHECK: Incremental profile: check=2 levels=3
; CHECK: Incremental profile cbp/backend: check=2 cbp-resets=0 cbp-divergences=1 cbp-rollbacks=1 cbp-rolled-levels=1.*cbp-fed-levels=1 cbp-fresh-levels=1 cbp-refed-levels=0 cbp-fed-nodes=5 cbp-fresh-nodes=5 cbp-refed-nodes=0
; CHECK: Incremental profile total: checks=2
; CHECK: ^sat
; RESET: Incremental profile cbp/backend: check=2 cbp-resets=1 cbp-divergences=1 cbp-rollbacks=0 cbp-rolled-levels=0.*cbp-fed-levels=3 cbp-fresh-levels=1 cbp-refed-levels=2 cbp-fed-nodes=9 cbp-fresh-nodes=5 cbp-refed-nodes=4
; RESET: ^sat
; QUIET-NOT: Incremental profile
; QUIET: ^sat
(check-sat)

(pop 1)
(push 1)
(assert (= (bvadd x y) #x03))
; CHECK: Incremental profile: check=3 levels=3
; CHECK: Incremental profile cbp/backend: check=3 cbp-resets=0 cbp-divergences=1 cbp-rollbacks=1 cbp-rolled-levels=1.*cbp-fed-levels=1 cbp-fresh-levels=1 cbp-refed-levels=0 cbp-fed-nodes=5 cbp-fresh-nodes=5 cbp-refed-nodes=0
; CHECK: Incremental profile total: checks=3
; CHECK: ^sat
; RESET: Incremental profile cbp/backend: check=3 cbp-resets=1 cbp-divergences=1 cbp-rollbacks=0 cbp-rolled-levels=0.*cbp-fed-levels=3 cbp-fresh-levels=1 cbp-refed-levels=2 cbp-fed-nodes=9 cbp-fresh-nodes=5 cbp-refed-nodes=4
; RESET: ^sat
; QUIET-NOT: Incremental profile
; QUIET: ^sat
(check-sat)

; Extending the unchanged stack does not roll back or re-feed its prefix.
(push 1)
(assert (= y #x02))
; CHECK: Incremental profile: check=4 levels=4
; CHECK: Incremental profile cbp/backend: check=4 cbp-resets=0 cbp-divergences=0 cbp-rollbacks=0 cbp-rolled-levels=0.*cbp-fed-levels=1 cbp-fresh-levels=1 cbp-refed-levels=0 cbp-fed-nodes=3 cbp-fresh-nodes=3 cbp-refed-nodes=0
; CHECK: Incremental profile total: checks=4
; CHECK: ^sat
; RESET: Incremental profile cbp/backend: check=4 cbp-resets=0 cbp-divergences=0 cbp-rollbacks=0 cbp-rolled-levels=0.*cbp-fed-levels=1 cbp-fresh-levels=1 cbp-refed-levels=0 cbp-fed-nodes=3 cbp-fresh-nodes=3 cbp-refed-nodes=0
; RESET: ^sat
; QUIET-NOT: Incremental profile
; QUIET: ^sat
; QUIET-NOT: Incremental profile
(check-sat)

; Popping two levels preserves x's fixing but discards both suffix frames.
; Only the replacement level is fed.
(pop 2)
(push 1)
(assert (= z #x04))
; CHECK: Incremental profile: check=5 levels=3
; CHECK: Incremental profile cbp/backend: check=5 cbp-resets=0 cbp-divergences=1 cbp-rollbacks=1 cbp-rolled-levels=2.*cbp-fed-levels=1 cbp-fresh-levels=1 cbp-refed-levels=0 cbp-fed-nodes=3 cbp-fresh-nodes=3 cbp-refed-nodes=0
; CHECK: Incremental profile total: checks=5
; CHECK: ^sat
; RESET: Incremental profile cbp/backend: check=5 cbp-resets=1 cbp-divergences=1 cbp-rollbacks=0 cbp-rolled-levels=0.*cbp-fed-levels=3 cbp-fresh-levels=1 cbp-refed-levels=2 cbp-fed-nodes=7 cbp-fresh-nodes=3 cbp-refed-nodes=4
; RESET: ^sat
; QUIET-NOT: Incremental profile
; QUIET: ^sat
(check-sat)

; Popping the fixing level must restore the caller substitution map too.
; A stale x=#x01 entry would rewrite this replacement to false.
(pop 2)
(push 1)
(assert (distinct x #x01))
; CHECK: Incremental profile: check=6 levels=2
; CHECK: Incremental profile cbp/backend: check=6 cbp-resets=0 cbp-divergences=1 cbp-rollbacks=1 cbp-rolled-levels=2.*cbp-fed-levels=1 cbp-fresh-levels=1 cbp-refed-levels=0 cbp-fed-nodes=4 cbp-fresh-nodes=4 cbp-refed-nodes=0
; CHECK: Incremental profile total: checks=6
; CHECK: ^sat
; RESET: Incremental profile cbp/backend: check=6 cbp-resets=1 cbp-divergences=1 cbp-rollbacks=0 cbp-rolled-levels=0.*cbp-fed-levels=2 cbp-fresh-levels=1 cbp-refed-levels=1 cbp-fed-nodes=5 cbp-fresh-nodes=4 cbp-refed-nodes=1
; RESET: ^sat
; QUIET-NOT: Incremental profile
; QUIET: ^sat
(check-sat)
(exit)
