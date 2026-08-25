; t >=u ((x >> s) << 1). A lower bound on the quotient, which nothing
; else here supplies -- every other quotient fact bounds it from above.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 128))
(declare-fun b () (_ BitVec 128))
(assert (bvult (bvudiv a b) (bvshl (bvlshr a b) (_ bv1 128))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
