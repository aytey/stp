; A quotient and remainder over identical operands obey the full modular
; recomposition identity x = q*s+r. The low-three-bit pair schema is cheaper
; and remains separately selectable; this test asks for the full escalation
; because the contradiction lives across the complete 256-bit relation.
;
; q=2 and r=1 require a=2b+1, which the final assertion denies.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=divrem-full %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: paired BVDIV/BVMOD full recomposition lemma over 256 bits
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (= (bvudiv a b) (_ bv2 256)))
(assert (= (bvurem a b) (_ bv1 256)))
(assert (distinct a (bvadd b (bvadd b (_ bv1 256)))))
(check-sat)
(exit)
