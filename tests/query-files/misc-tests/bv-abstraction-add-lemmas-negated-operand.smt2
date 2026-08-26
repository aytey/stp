; ... and the same family over the lowering that makes an addition out of a
; subtraction. `bvsub a b` reaches the blaster as `a + (-b)`, with the
; negation folded into the record rather than standing as its own term, so
; every fact about this record is a fact about `-b` and not about `b`. An
; implementation that read the operand as written would be installing
; theorems about the wrong value: sound-looking, and wrong.
;
; Four ADD lemmas fire here, one of them over the negated operand, and the
; three legs have to agree.
; RUN: %solver --incremental=off --bv-term-abstraction=1 --bv-term-abstraction-schema-groups=base,add %s | %OutputCheck %s
; RUN: %solver --incremental=off --bv-term-abstraction=1 %s | %OutputCheck %s
; RUN: %solver --incremental=off %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (= ((_ extract 255 255) a) #b0))
(assert (= ((_ extract 255 255) (bvneg b)) #b0))
(assert (bvult (bvsub a b) (bvor a (bvneg b))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
