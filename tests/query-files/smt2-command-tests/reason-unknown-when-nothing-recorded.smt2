; An unknown whose producer recorded no reason still has to be admitted to.
;
; (get-info :reason-unknown) reports a reason that the producer of the
; no-answer recorded. When there is none the switch reaches its None arm,
; which has two shapes to tell apart: nothing has answered unknown, and
; something has but said nothing about why. It tells them apart by the cached
; verdict.
;
; SOLVER_UNKNOWN was the only verdict it counted, and it is not the only one
; that prints `unknown`: PrintOutput prints it for SOLVER_TIMEOUT as well. So
; a no-answer from a producer that records nothing printed `unknown` and then
; told a caller who asked why that the last answer was not unknown. That is
; not a missing reason, it is a contradiction of the line above it, and a
; caller that branches on it is being lied to.
;
; A bare `unknown` is the honest answer and the most this arm can give: the
; reason genuinely was not recorded. Naming the budget is the producer's job,
; done where the producer still knows it.
;
; The two legs are the same query stopped by the same budget through the two
; drivers, which is what isolates the arm. The batch pipeline asks its SAT
; solver which budget stopped it and names --max-num-confl; the incremental
; driver returns SOLVER_TIMEOUT without recording anything, and is the
; deterministic way into the None arm.
;
; A budget of zero conflicts rather than one, so that the legs do not depend
; on a solver being unlucky enough to need a second conflict: any query that
; needs search at all exceeds it, and this one is a real factorisation --
; zero-extended so the product cannot wrap, since modular multiplication
; would make it trivially satisfiable instead.
;
; RUN: %solver --incremental=on --max-num-confl=0 %s 2>&1 | %OutputCheck --check-prefix=INC %s
; RUN: %solver --incremental=off --max-num-confl=0 %s 2>&1 | %OutputCheck --check-prefix=BATCH %s
;
; INC: ^unknown$
; INC: ^\(:reason-unknown unknown\)$
; INC-NOT: the last answer was not unknown
;
; BATCH: ^unknown$
; BATCH: :reason-unknown \(incomplete "the conflict budget set by --max-num-confl ran out"\)
; BATCH-NOT: the last answer was not unknown
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (= (bvmul ((_ zero_extend 32) a) ((_ zero_extend 32) b)) #x7ffffffc80000005))
(assert (bvugt a #x00000001))
(assert (bvugt b #x00000001))
(check-sat)
(get-info :reason-unknown)
