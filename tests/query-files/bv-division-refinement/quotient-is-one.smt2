; s <=u x <u 2s -> t = 1, the quotient read of the same premise the remainder
; fact beside this one uses. A divisor that fits the dividend exactly once
; divides it exactly once, and nothing else here says so: the quotient facts
; name a value only for a zero dividend, an all-ones divisor, and a divisor
; equal to the dividend. Everything between those is bounded and never named.
;
; Without it the refinement spends its whole allowance of blocking lemmas and
; then encodes an exact 256-bit divider: 41 rounds, 32 blocking lemmas, half a
; minute. With it, six rounds and no blocking lemma.
; RUN: %solver --incremental=off --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvule b a))
(assert (bvult a (bvadd b b)))
(assert (distinct (bvudiv a b) (_ bv1 256)))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
