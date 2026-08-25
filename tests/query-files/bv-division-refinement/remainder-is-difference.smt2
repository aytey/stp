; s <=u x <u 2s -> r = x - s. The divisor fits the dividend exactly once, so
; subtracting it once is the whole of the division -- and nothing else here
; says so. The remainder facts bound r below the divisor and at or under the
; dividend and relate it to their bitwise mixtures; not one of them names the
; value it takes, even in the case where the value is a subtraction away.
;
; `2s` is read in the integers rather than the bit vector: a divisor with its
; top bit set doubles past the width, so nothing can reach 2s and that half of
; the premise is free. `s != 0` is carried inside the premise -- a zero
; divisor cannot be at most the dividend and strictly above it at once.
;
; Without it the refinement spends its whole allowance of blocking lemmas and
; then encodes an exact 256-bit remainder: 41 rounds, 32 blocking lemmas, half
; a minute. With it, six rounds and no blocking lemma at all.
; RUN: %solver --incremental=off --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvule b a))
(assert (bvult a (bvadd b b)))
(assert (distinct (bvurem a b) (bvsub a b)))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
