; A model may expose only applications in the most recent certified active
; view.  Reusing the declaration at a tuple that query never observed must
; return the v2 public-API response, "unsupported", rather than exposing a
; solve-local result symbol or inventing a value.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^\( \(\|f\| \|x\|\)  #x03 \)
; CHECK: ^unsupported
;
(set-option :produce-models true)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= (f x) #x03))
(check-sat)
(get-value ((f x)))
(get-value ((f #xee)))
(exit)
