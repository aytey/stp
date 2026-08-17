; The ordering rewrite does not reach the persistent driver, and must not.
;
; Batch rebuilds the formula from the stored assertions at every solve, so the
; guard is re-decided each time and an assertion arriving after one check-sat
; simply stops the rewrite applying at the next. The driver's clauses are
; persistent: a chain encoded into a block would stay in force when a later
; assertion destroyed the symmetry that justified it, and there is no round
; at which that could be noticed. The containment is structural -- the driver
; has its own path and never enters the batch pipeline -- and this pins it,
; because it is the kind of separation a refactor removes by accident.
;
; The two runs agree on both verdicts, which is the part that matters; only
; the first one is allowed to say it ordered anything.
;
; RUN: %solver -s --incremental=off %s 2>&1 | %OutputCheck --check-prefix=BATCH %s
; RUN: %solver -s --incremental=on %s 2>&1 | %OutputCheck --check-prefix=DRIVER %s
;
; BATCH: Ordered 1 symmetric distinct group\(s\)
; BATCH: ^sat
; BATCH: ^unsat
;
; DRIVER-NOT: Ordered
; DRIVER: ^sat
; DRIVER: ^unsat
;
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (distinct a b c))
(check-sat)
(push 1)
; a is now compared, so the operands are no longer interchangeable: an
; ordering inherited from the solve above would report unsat here.
(assert (bvugt a b))
(assert (bvugt a c))
(assert (bvult a #x02))
(check-sat)
(pop 1)
