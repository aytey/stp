; The automatic eager policy considers every floating-point signature after
; every bit-vector one, and then selects it if the budget still stretches.
;
; A float pair is worth less than a bit-vector pair of the same count: over
; bit-vectors the query's own (= a b) is a substitutable equality, so equality
; propagation collapses the actuals and the constraints dissolve before SAT;
; over floats it is FP_SMT_EQ, a predicate, and every constraint is paid in
; full. Floats used to be refused outright for that reason, which was right
; while the budget admitted a float declaration of up to 91 applications. At
; the current budget it admits at most 23, and across that band refusing costs
; more than it saves.
;
; What the ordering preserves is that a cheap float declaration cannot take
; budget a more expensive bit-vector one would have used: f is 231 pairs and
; ff is 66, and f is still selected first.
;
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=auto --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=auto --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck --check-prefix=REFERENCE %s
;
; CHECK: UF: eager selected f \(3 applications, 3 pairs estimated, 3 enumerated, 0 impossible, 3 constraints\)
; CHECK-NEXT: UF: eager selected ff \(2 applications, 1 pairs estimated, 1 enumerated, 0 impossible, 1 constraints\)
; CHECK: ^unsat$
;
; The reference profile still installs nothing up front, so the float pair is
; earned by a refuted candidate instead.
; REFERENCE-NOT: UF: eager selected
; REFERENCE: UF: installed congruence lemma
; REFERENCE: ^unsat$
;
(set-logic QF_UFBVFP)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun ff ((_ FloatingPoint 8 24)) (_ BitVec 4))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))
(declare-const u (_ FloatingPoint 8 24))
(declare-const v (_ FloatingPoint 8 24))
(assert (bvult (f x) (bvadd (f y) #x10)))
(assert (bvult (f z) #x20))
(assert (= u v))
(assert (distinct (ff u) (ff v)))
(check-sat)
