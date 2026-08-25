; x >=u ((t << 1) >> (t << s)), where t is the quotient. The
; highest-firing fact of the eleven added after the first set, and the one
; that needed a barrel shifter driven by a variable amount in each
; direction rather than only to the right.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 160))
(declare-fun b () (_ BitVec 160))
(assert (bvult a (bvlshr (bvshl (bvudiv a b) (_ bv1 160)) (bvshl (bvudiv a b) b))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
