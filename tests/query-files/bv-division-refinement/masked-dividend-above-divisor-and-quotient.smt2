; (x & -q) >=u (s & q), for q = x udiv s.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=udiv-observed %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: BVDIV masked-dividend-above-divisor-and-quotient lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 128))
(declare-fun s () (_ BitVec 128))
(assert
  (let ((q (bvudiv x s)))
    (bvult (bvand x (bvneg q)) (bvand s q))))
(check-sat)
(exit)
