; Multiplication and DIV/MOD have independent scope controls. Both runs keep
; multiplication abstraction off. The division remains a candidate in each,
; but only --bv-term-abstraction-divmod decides whether it is abstracted.
;
; RUN: %solver --incremental=off -t --bv-abstraction-width=1 --bv-term-abstraction=1 --bv-term-abstraction-mult=0 --bv-term-abstraction-divmod=1 --bv-term-abstraction-plus=0 %s 2>&1 | %OutputCheck --check-prefix=ON %s
; RUN: %solver --incremental=off -t --bv-abstraction-width=1 --bv-term-abstraction=1 --bv-term-abstraction-mult=0 --bv-term-abstraction-divmod=0 --bv-term-abstraction-plus=0 %s 2>&1 | %OutputCheck --check-prefix=OFF %s
; ON: Abstraction coverage \(candidates -> abstracted\): eq=[0-9]+->[0-9]+ compare=[0-9]+->[0-9]+ ite=[0-9]+->[0-9]+ plus=1->0 mult=0->0 divmod=1->1
; ON: ^sat$
; OFF: Abstraction coverage \(candidates -> abstracted\): eq=[0-9]+->[0-9]+ compare=[0-9]+->[0-9]+ ite=[0-9]+->[0-9]+ plus=1->0 mult=0->0 divmod=1->0
; OFF: ^sat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (= (bvudiv a b) (_ bv3 8)))
(assert (= (bvadd a b) (_ bv16 8)))
(check-sat)
(exit)
