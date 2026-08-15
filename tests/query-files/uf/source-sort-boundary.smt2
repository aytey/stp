; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: unsupported domain sort \(Array \(_ BitVec 8\) \(_ BitVec 8\)\) at argument 0 of bad-array
; CHECK: unsupported domain sort \(_ FloatingPoint 8 24\) at argument 0 of bad-fp
; CHECK: unsupported domain sort RoundingMode at argument 0 of bad-rm
; CHECK: unsupported domain sort UnknownSort at argument 0 of bad-unknown \(unknown
; CHECK: unsupported domain sort \(_ BitVec 0\) at argument 0 of bad-zero
; CHECK: unsupported result sort \(Array \(_ BitVec 8\) \(_ BitVec 8\)\) of bad-result
; CHECK: ^sat
; CHECK: REACHED-END
;
(set-logic QF_ABVFP)
(declare-fun bad-array ((Array (_ BitVec 8) (_ BitVec 8))) Bool)
(declare-fun bad-fp ((_ FloatingPoint 8 24)) Bool)
(declare-fun bad-rm (RoundingMode) Bool)
(declare-fun bad-unknown (UnknownSort) Bool)
(declare-fun bad-zero ((_ BitVec 0)) Bool)
(declare-fun bad-result (Bool) (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun p (Bool (_ BitVec 8)) Bool)
(assert (= (p true #x00) (p true #x00)))
(check-sat)
(echo "REACHED-END")
