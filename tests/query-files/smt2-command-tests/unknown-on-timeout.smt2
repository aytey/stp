; A solve that runs out of clock answers `unknown`, not prose.
;
; The no-answer channel printed "Timed Out." in every mode, including SMT-LIB,
; where a caller cannot act on a sentence and where there is a word for this.
; Both reasons there may be no answer -- the clock, and an encoding that cannot
; represent every model of the input -- now print the same `unknown`, and
; (get-info :reason-unknown) is what tells them apart.
;
; The legacy CVC output keeps its own wording: it has no get-info to ask.
;
; Two hundred unconstrained 32-bit variables under one distinct, with the
; ordering rewrite off so the query survives to the solver, against a
; two-second budget.
;
; RUN: %solver --distinct-ordering=0 -g 2 %s 2>&1 | %OutputCheck %s
; CHECK: ^unknown$
; CHECK-NOT: Timed Out
; CHECK: :reason-unknown timeout
;
(set-logic QF_BV)
(declare-fun mk () (_ BitVec 32))
(declare-fun x0 () (_ BitVec 32))
(declare-fun x1 () (_ BitVec 32))
(declare-fun x2 () (_ BitVec 32))
(declare-fun x3 () (_ BitVec 32))
(declare-fun x4 () (_ BitVec 32))
(declare-fun x5 () (_ BitVec 32))
(declare-fun x6 () (_ BitVec 32))
(declare-fun x7 () (_ BitVec 32))
(declare-fun x8 () (_ BitVec 32))
(declare-fun x9 () (_ BitVec 32))
(assert (bvult (bvmul (bvmul x0 x1) (bvmul x2 x3)) (bvmul (bvmul x4 x5) (bvmul x6 x7))))
(assert (= (bvmul (bvmul (bvmul x0 x1) (bvmul x2 x3)) (bvmul (bvmul x4 x5) (bvmul x6 x7))) (bvmul x8 x9)))
(assert (= (bvmul x8 x9) mk))
(assert (bvugt mk #x7ffffff0))
(assert (distinct x0 x1 x2 x3 x4 x5 x6 x7 x8 x9))
(check-sat)
(get-info :reason-unknown)
