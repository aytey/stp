; (x - s) >=u r for r = x urem s. Subtracting the divisor once cannot
; take the dividend below its remainder.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=urem %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: BVMOD difference-above-remainder lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 256))
(declare-fun s () (_ BitVec 256))
(assert (bvult (bvsub x s) (bvurem x s)))
(check-sat)
(exit)
