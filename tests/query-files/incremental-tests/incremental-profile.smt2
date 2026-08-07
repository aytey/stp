; The opt-in profiler reports deterministic work counters as well as timings.
; Changing the deepest level forces a CBP reset: the two-level common prefix
; is re-fed and the replacement suffix is a fresh feed. Elapsed values are
; deliberately not checked.
; RUN: %solver --incremental --incremental-profile %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental %s 2>&1 | %OutputCheck --check-prefix=QUIET %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))

(push 1)
(assert (= x #x01))
(push 1)
(assert (= (bvadd x y) #x03))
; CHECK: Incremental profile: check=1 levels=3 total-us=[0-9]+.*cbp-reset-us=[0-9]+ cbp-feed-us=[0-9]+ cbp-fresh-feed-us=[0-9]+ cbp-refeed-us=[0-9]+.*initial-sat-us=[0-9]+ refinement-sat-us=[0-9]+
; CHECK: Incremental profile cbp/backend: check=1 cbp-resets=0 cbp-fed-levels=3 cbp-fresh-levels=3 cbp-refed-levels=0 cbp-fed-nodes=9 cbp-fresh-nodes=9 cbp-refed-nodes=0
; CHECK: Incremental profile total: checks=1
; CHECK: ^sat
; QUIET-NOT: Incremental profile
; QUIET: ^sat
(check-sat)

(pop 1)
(push 1)
(assert (= (bvadd x z) #x04))
; CHECK: Incremental profile: check=2 levels=3
; CHECK: Incremental profile cbp/backend: check=2 cbp-resets=1 cbp-fed-levels=3 cbp-fresh-levels=1 cbp-refed-levels=2 cbp-fed-nodes=9 cbp-fresh-nodes=5 cbp-refed-nodes=4
; CHECK: Incremental profile total: checks=2
; CHECK: ^sat
; QUIET-NOT: Incremental profile
; QUIET: ^sat
(check-sat)

(pop 1)
(push 1)
(assert (= (bvadd x y) #x03))
; CHECK: Incremental profile: check=3 levels=3
; CHECK: Incremental profile cbp/backend: check=3 cbp-resets=1 cbp-fed-levels=3 cbp-fresh-levels=1 cbp-refed-levels=2 cbp-fed-nodes=9 cbp-fresh-nodes=5 cbp-refed-nodes=4
; CHECK: Incremental profile total: checks=3
; CHECK: ^sat
; QUIET-NOT: Incremental profile
; QUIET: ^sat
(check-sat)

; Extending the unchanged stack does not reset or re-feed its prefix.
(push 1)
(assert (= y #x02))
; CHECK: Incremental profile: check=4 levels=4
; CHECK: Incremental profile cbp/backend: check=4 cbp-resets=0 cbp-fed-levels=1 cbp-fresh-levels=1 cbp-refed-levels=0 cbp-fed-nodes=3 cbp-fresh-nodes=3 cbp-refed-nodes=0
; CHECK: Incremental profile total: checks=4
; CHECK: ^sat
; QUIET-NOT: Incremental profile
; QUIET: ^sat
; QUIET-NOT: Incremental profile
(check-sat)
(exit)
