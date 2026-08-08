; REQUIRES: floating-point, cadical
; An established many-query session keeps its useful trail when floating
; point arrives late. Retiring at this boundary used to rebuild the array
; registry and discard the refinement/search state accumulated by the prefix;
; representative Vector traces became 2x--6x slower. Early-FP sessions still
; retire the trail (trail-reuse-retired-for-fp.smt2), and the independent size
; belt may still retire this one after it grows large enough.
;
; Six distinct array queries establish the many-solve shape. The seventh adds
; FP while the solver is deliberately well below the size belt: it must not
; cause a trail rebuild.
; RUN: %solver --incremental --incremental-profile --check-sanity %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)
(declare-fun A () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun f () (_ FloatingPoint 8 24))

(push 1)
(assert (= (select A #x01) #x01))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (select A #x02) #x02))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (select A #x03) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (select A #x04) #x04))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (select A #x05) #x05))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (select A #x06) #x06))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.isNaN f))
; CHECK: Incremental profile cbp/backend: check=7 .*rebuild-trail=0
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
