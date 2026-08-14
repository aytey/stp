; Unsupported UF signature sorts reject their declarations transactionally.
; Use an FP-capable logic so all source-sort spellings reach semantic
; validation instead of being intercepted by the logic-sensitive lexer.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: uninterpreted-function BitVec domain sorts must have positive width
; CHECK: uninterpreted-function signatures do not support Array
; CHECK: uninterpreted-function signatures do not support FloatingPoint
; CHECK: uninterpreted-function signatures do not support RoundingMode
; CHECK: ^sat
; CHECK: ^"REACHED-END"
;
(set-logic QF_ABVFP)
(declare-fun bad-zero ((_ BitVec 0)) Bool)
(declare-fun bad-array ((Array (_ BitVec 4) (_ BitVec 4))) Bool)
(declare-fun bad-fp ((_ BitVec 8)) (_ FloatingPoint 8 24))
(declare-fun bad-rm (RoundingMode) Bool)
(check-sat)
(echo "REACHED-END")
(exit)
