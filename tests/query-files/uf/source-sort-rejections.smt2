; Unsupported UF signature sorts reject their declarations transactionally.
; Use an FP-capable logic so all source-sort spellings reach semantic
; validation instead of being intercepted by the logic-sensitive lexer.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: unsupported domain sort \(_ BitVec 0\) at argument 0 of bad-zero
; CHECK: unsupported domain sort \(Array \(_ BitVec 4\) \(_ BitVec 4\)\) at argument 0 of bad-array
; CHECK: unsupported result sort \(_ FloatingPoint 8 24\) of bad-fp
; CHECK: unsupported domain sort RoundingMode at argument 0 of bad-rm
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
