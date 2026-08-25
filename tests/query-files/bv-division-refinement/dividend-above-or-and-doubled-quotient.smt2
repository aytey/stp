; x >=u ((x | s) & (t << 1)). Synthesised, and worth a 128-bit divider:
; without it this query does not come back inside a minute.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 128))
(declare-fun b () (_ BitVec 128))
(assert (bvult a (bvand (bvor a b) (bvshl (bvudiv a b) (_ bv1 128)))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
