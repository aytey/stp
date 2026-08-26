; x = t*s + r, over a quotient and a remainder the query takes of the same
; operands. The one fact the abstraction has about two of its records at once,
; and the only one that is a definition rather than a consequence of one.
;
; The query fixes the quotient at 2 and the remainder at 1 and then denies
; that the dividend is 2b + 1, which is exactly what the identity says it must
; be. Nothing about either record on its own can see that: the quotient's
; facts say nothing about the remainder and the remainder's say nothing about
; the quotient, so without the identity the refinement enumerates operand
; pairs until it gives up and encodes both operations exactly -- 49 rounds and
; 64 blocking lemmas, and a minute and a quarter. With it: two rounds, no
; blocking lemma, and under a second. An exact 256-bit divider is dearer than
; the multiplier the identity costs, and here it needs two of them.
; The family is named because it is not in the inherited profile. The
; identity costs a multiplier at the record's width, and on floating-point
; queries -- where SymFPU hands it a ~107-bit quotient/remainder pair for
; every `fp.div` -- that multiplier is 63% worse than not abstracting at
; all. `divrem-prefix` says the same thing of the low three bits and ships
; instead. This query is what the full-width form is for, and is why it is
; still here.
; RUN: %solver --incremental=off --bv-term-abstraction=1 --bv-term-abstraction-schema-groups=base,udiv,urem,mul6,mul8,divisor-magnitude,quotient-one,divrem-identity %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (= (bvudiv a b) (_ bv2 256)))
(assert (= (bvurem a b) (_ bv1 256)))
(assert (distinct a (bvadd b (bvadd b (_ bv1 256)))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
