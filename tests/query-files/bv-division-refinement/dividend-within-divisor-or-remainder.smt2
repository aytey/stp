; x = x & (s | t | -s), over a remainder. Synthesised, and the whole of
; what stands between this query and an exact 256-bit remainder.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (not (= a (bvand a (bvor b (bvor (bvurem a b) (bvneg b)))))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
