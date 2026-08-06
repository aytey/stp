; Auto-engagement starts at the THIRD real solve. A pushed session's
; first two check-sats keep the batch pipeline's whole-formula
; simplification (no driver stats lines before the second answer); the
; third goes through the driver and reports its encode line. Two-check
; sessions -- where the driver's persistent encoding could never be
; repaid, and which dominated the campaign's loss tail -- are batch
; throughout by construction (engagement-two-checks.smt2 pins that
; side; --incremental still forces the driver from the first solve, as
; every forced-driver test in this directory exercises).
; RUN: %solver -s %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (bvult x #x80))
(push 1)
(assert (bvult x #x40))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvult x #x20))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvuge x #x80))
; CHECK: Incremental: encoded
; CHECK: ^unsat
(check-sat)
(pop 1)
(exit)
