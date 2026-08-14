; Every top-level declaration kind shares one namespace.  A rejected
; declaration is command-local, registers nothing, and leaves the original
; binding usable.  This intentionally freezes the repaired branch's uniform
; nonfatal policy for both zero- and nonzero-arity redeclarations.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error ".*g.*already.*"\)
; CHECK-NEXT: ^\(error ".*d.*define-fun"\)
; CHECK-NEXT: ^\(error ".*s.*ordinary symbol"\)
; CHECK-NEXT: ^\(error ".*g.*uninterpreted function"\)
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^"REACHED-END"
; CHECK-NOT: syntax error
;
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(define-fun d ((x (_ BitVec 8))) (_ BitVec 8) (bvnot x))
(declare-const s (_ BitVec 8))
(declare-fun g ((_ BitVec 8)) (_ BitVec 4))
(declare-fun d ((_ BitVec 8)) (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(declare-fun g () (_ BitVec 8))
(assert (distinct (g #x03) (g #x03)))
(check-sat)
(echo "REACHED-END")
