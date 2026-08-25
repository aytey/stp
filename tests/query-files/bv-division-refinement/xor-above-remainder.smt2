; ((-s) ^ (x | s)) >=u t, over a remainder. Synthesised, and the
; strongest bound on a remainder here that is not simply t <u s.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvult (bvxor (bvneg b) (bvor a b)) (bvurem a b)))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
