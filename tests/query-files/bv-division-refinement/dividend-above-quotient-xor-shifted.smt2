; x >=u (t ^ (t >> (s >> 1))). Synthesised: an exclusive-or of the
; quotient with a shift of itself, bounded by the dividend.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 128))
(declare-fun b () (_ BitVec 128))
(assert (bvult a (bvxor (bvudiv a b) (bvlshr (bvudiv a b) (bvlshr b (_ bv1 128))))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
