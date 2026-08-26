; If exactly one subtraction of b fits in a, the quotient is one:
;
;   b <=u a and (a-b) <u b -> a udiv b = 1.
;
; The first run also keeps multiplication abstraction off. Division must
; still be abstracted and refined, which is the end-to-end check that the
; new DIV/MOD scope switch is independent rather than merely exposed in the
; option structures.
;
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-mult=0 --bv-term-abstraction-divmod=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=quotient-one-quot %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: BVDIV quotient-is-one lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvule b a))
(assert (bvult (bvsub a b) b))
(assert (distinct (bvudiv a b) (_ bv1 256)))
(check-sat)
(exit)
