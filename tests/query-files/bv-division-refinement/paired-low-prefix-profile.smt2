; The broad-prefix profile adds only the cheap low-three-bit recomposition
; relation to the broad-no-pair catalogue. The quotient and remainder below
; require low(q*s+r)=1, while the dividend's low bits are zero, so that paired
; relation alone rejects the candidate before either record takes an individual
; schema. Fixing q and r to nonzero values also keeps both operations live
; through preprocessing.
;
; The paired relation is not inherited: an abstraction enabled without a
; profile gets the qualified mask, which does not contain it, so the last run
; below has to reach the same answer the long way.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-profile=broad-prefix %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=base,divrem-pair %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 %s 2>&1 | %OutputCheck %s --check-prefix=INHERITED
; CHECK: BV abstraction: paired BVDIV/BVMOD recomposition lemma over 3 bits
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
; INHERITED-NOT: paired BVDIV/BVMOD recomposition
; INHERITED: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (= (bvudiv a b) (_ bv2 256)))
(assert (= (bvurem a b) (_ bv1 256)))
(assert (= ((_ extract 2 0) a) #b000))
(assert (= ((_ extract 2 0) b) #b000))
(check-sat)
(exit)
