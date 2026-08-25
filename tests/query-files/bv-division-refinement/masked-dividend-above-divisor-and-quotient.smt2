; (x & -t) >=u (s & t). The only fact here that compares two masks of the
; operands rather than an operand against a shift of one.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 128))
(declare-fun b () (_ BitVec 128))
(assert (bvult (bvand a (bvneg (bvudiv a b))) (bvand b (bvudiv a b))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
