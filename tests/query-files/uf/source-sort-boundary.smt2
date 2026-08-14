; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: signatures do not support Array
; CHECK: signatures do not support FloatingPoint
; CHECK: signatures do not support RoundingMode
; CHECK: signature sort 'UnknownSort' is unknown or unsupported
; CHECK: BitVec domain sorts must have positive width
; CHECK: signatures do not support Array
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
