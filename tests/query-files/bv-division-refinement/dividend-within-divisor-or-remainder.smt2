; x = x & (s | r | -s), for r = x urem s.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=urem %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: BVMOD dividend-within-divisor-or-remainder lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 256))
(declare-fun s () (_ BitVec 256))
(assert
  (distinct x
            (bvand x (bvor s (bvor (bvurem x s) (bvneg s))))))
(check-sat)
(exit)
