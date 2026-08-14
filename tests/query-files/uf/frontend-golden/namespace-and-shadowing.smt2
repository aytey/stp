; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: already denotes an uninterpreted function
; CHECK: already denotes an ordinary symbol
; CHECK: already denotes an uninterpreted function
; CHECK: already denotes a define-fun
; CHECK: ^sat
; CHECK: REACHED-END
;
; UF declarations, scalar symbols, and define-fun macros share the SMT-LIB
; top-level namespace. Rejected declarations leave the prior owner intact.
; Nested let binders still shadow normally and resolve before UF application
; hash-consing.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const f (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-fun x ((_ BitVec 8)) (_ BitVec 8))
(define-fun f ((q (_ BitVec 8))) (_ BitVec 8) q)
(define-fun m ((q (_ BitVec 8))) (_ BitVec 8) q)
(declare-fun m ((_ BitVec 8)) (_ BitVec 8))
(assert (= (let ((x #x01)) (let ((x #x02)) (f x))) (f #x02)))
(check-sat)
(echo "REACHED-END")
