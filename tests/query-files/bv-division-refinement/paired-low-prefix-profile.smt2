; The broad-prefix profile adds only the cheap low-three-bit recomposition
; relation to SPEAR. The quotient and remainder below require low(q*s+r)=1,
; while the dividend's low bits are zero, so that paired relation alone rejects
; the candidate before either record takes an individual schema. Fixing q and r
; to nonzero values also keeps both operations live through preprocessing.
;
; `klee` is an alias for the same atomic mask/round pair.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-profile=broad-prefix %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-profile=klee %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: paired BVDIV/BVMOD recomposition lemma over 3 bits
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (= (bvudiv a b) (_ bv2 256)))
(assert (= (bvurem a b) (_ bv1 256)))
(assert (= ((_ extract 2 0) a) #b000))
(assert (= ((_ extract 2 0) b) #b000))
(check-sat)
(exit)
