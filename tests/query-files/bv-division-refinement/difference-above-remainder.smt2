; (x - s) >=u t, over a remainder. Subtracting the divisor once cannot
; take the dividend below its remainder.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvult (bvadd a (bvneg b)) (bvurem a b)))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
