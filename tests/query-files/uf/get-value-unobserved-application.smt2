; A model may expose only applications in the most recent certified active
; view.  Reusing the declaration at a tuple that query never observed is a
; request the current model cannot answer, not a feature the solver lacks:
; the command gets exactly one SMT-LIB response, an (error ...) that names
; the reason, rather than exposing a solve-local result symbol, inventing a
; value, or answering the uninformative "unsupported".  The rejected command
; prints none of its other values, and the session continues.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^\($
; CHECK-NEXT: ^\( \(\|f\| \|x\|\)  #x03 \)$
; CHECK-NEXT: ^\)$
; CHECK-NEXT: ^\(error "uninterpreted-function application was not active in the certified solve"\)$
; CHECK-NEXT: ^\(error "uninterpreted-function application was not active in the certified solve"\)$
; CHECK-NEXT: ^\($
; CHECK-NEXT: ^\( \(\|f\| \|x\|\)  #x03 \)$
; CHECK-NEXT: ^\)$
; CHECK-NEXT: ^"REACHED-END"$
; CHECK-NOT: unsupported
;
(set-option :produce-models true)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= (f x) #x03))
(check-sat)
(get-value ((f x)))
(get-value ((f #xee)))
(get-value ((f x) (f #xee)))
(get-value ((f x)))
(echo "REACHED-END")
(exit)
