; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality -r %s | %OutputCheck %s
; RUN: %solver --incremental=on --array-equality %s | %OutputCheck %s
; RUN: %solver --incremental=on --array-equality -r %s | %OutputCheck %s
;
; The model half of array-rm-write-chain-cell-is-a-mode.smt2, and the control
; that pinning the cell is not the same as publishing RNE for it.
;
; Four of the five modes are excluded from a[i] by four disequalities between
; a chain of one write and its own base, which the array-equality context
; rewrites into constraints on that cell rather than abstracting them. The
; cell is a read minted after the pinning pass ran, so a free carrier could
; satisfy all four at once by naming no mode -- and the model published a mode
; for it anyway, because a carrier with nothing behind it completes to RNE.
; RNE is one of the four this query excludes, so what came back was
;
;   ( (select |a| |i|) RNE )
;
; a model that does not satisfy the query it answers. (Visible under
; --incremental with -r; the other three routes did not get as far as a model,
; and are here because they failed differently over the same free cell.)
;
; RNA is the only mode the four leave, and it is the answer whether or not any
; cell needed completing: a fix that pinned the cell but still published the
; completion for it would fail here.
;
; CHECK: ^sat
; CHECK: ^\( \(select \|a\| \|i\|\) RNA \)$
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-fun a () (Array RoundingMode RoundingMode))
(declare-fun i () RoundingMode)
(assert (not (= (store a i RNE) a)))
(assert (not (= (store a i RTP) a)))
(assert (not (= (store a i RTN) a)))
(assert (not (= (store a i RTZ) a)))
(check-sat)
(get-value ((select a i)))
(exit)
