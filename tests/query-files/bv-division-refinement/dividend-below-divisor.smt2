; x <u s -> t = x, over a remainder. The cheapest of the remainder facts
; and the one that settles the operation outright: a dividend smaller than
; the divisor is its own remainder.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (and (bvult a b) (not (= (bvurem a b) a))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
