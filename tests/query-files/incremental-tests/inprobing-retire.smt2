; Probe-based inprocessing re-runs over the whole persistent encoding
; at every solve, so once a session proves itself many-solve the driver
; retires it: one bounded rebuild onto a fresh solver configured
; without it. AUTO retires only after trail reuse is gone (the
; floating-point content here sheds it at the first solve, for free)
; and after enough solves; answers must carry straight through the
; restart.
; RUN: %solver -s --incremental %s 2>&1 | %OutputCheck %s
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
; CHECK: trail reuse retired
(push 1)
(assert (fp.lt x (fp #b0 #x7f #b00000000000000000000001)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt x (fp #b0 #x7f #b00000000000000000000010)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt x (fp #b0 #x7f #b00000000000000000000011)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt x (fp #b0 #x7f #b00000000000000000000100)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt x (fp #b0 #x7f #b00000000000000000000101)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt x (fp #b0 #x7f #b00000000000000000000110)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt x (fp #b0 #x7f #b00000000000000000000111)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.lt x (fp #b0 #x7f #b00000000000000000001000)))
; CHECK: ^sat
(check-sat)
(pop 1)
; the ninth solve crosses the many-solve threshold: the solver restarts
; without inprobing, and the session continues correctly on it
(push 1)
(assert (fp.gt x (fp #b0 #x7f #b00000000000000000001001)))
; CHECK: inprobing retired
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (fp.eq x (fp #b0 #x7f #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
