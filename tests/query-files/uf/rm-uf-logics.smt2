; The UF+FP logic names. Without them no query can name a logic that admits
; both uninterpreted functions and the floating-point keywords: outside an FP
; logic "RoundingMode" is not a token at all, so a signature naming it is a
; plain syntax error rather than a UF diagnostic (see smt2.lex's
; SMT2SetFloatTokens gate).
;
; Each logic is accepted, turns the floating-point keywords on, and still
; admits a UF declaration; and each of them is gated on the feature flag
; exactly as QF_UFBV already is.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NOT: Wrong input logic
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: REACHED-END
;
(set-logic QF_UFFP)
(declare-fun kf (RoundingMode) RoundingMode)
(assert (distinct (kf RNE) (kf RNE)))
(check-sat)
(reset)
(set-logic QF_UFBVFP)
(declare-fun kb ((_ BitVec 4)) RoundingMode)
(assert (distinct (kb #x0) (kb #x0)))
(check-sat)
(reset)
(set-logic QF_UFABVFP)
(declare-fun ka ((_ BitVec 4)) RoundingMode)
(declare-const a (Array (_ BitVec 4) (_ BitVec 4)))
(assert (distinct (ka (select a #x0)) (ka (select a #x0))))
(check-sat)
(echo "REACHED-END")
