; The automatic eager-Ackermann policy declines a signature with a
; floating-point position, and still selects a bit-vector one.
;
; The policy's unit is a pair count, which is only a proxy for what a pair
; costs. Where the actuals are bit-vectors the query's own (= a b) is a
; substitutable equality, so equality propagation collapses the actuals onto
; one node, every eagerly installed premise becomes reflexive, and the whole
; encoding dissolves before SAT. Where they are floats (= a b) is FP_SMT_EQ,
; a predicate rather than a substitution, and an actual reaches its canonical
; name through a pack/unpack circuit -- so nothing collapses and every
; C(n, 2) constraint is paid in full. Measured, the trade inverts: eager is
; several times faster than lazy on a bit-vector signature and several times
; slower on a float one, diverging with size.
;
; --uf-ackermann=on still forces it. The encoding is correct; it is a bad
; trade, not a wrong one, and forcing it is what keeps it testable.
;
; The observable is the -s trace: a lemma is installed only when the dynamic
; loop had to earn one, which is exactly when eager encoding did not happen.
;
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=auto --incremental=off %s 2>&1 | %OutputCheck --check-prefix=DECLINED %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=auto --incremental=on %s 2>&1 | %OutputCheck --check-prefix=DECLINED %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=on --incremental=off %s 2>&1 | %OutputCheck --check-prefix=FORCED %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck --check-prefix=DECLINED %s
;
; DECLINED: UF: installed congruence lemma 1 for f
; DECLINED: ^unsat$
;
; FORCED-NOT: UF: installed congruence lemma
; FORCED: ^unsat$
;
(set-logic QF_UFBVFP)
(declare-fun f ((_ FloatingPoint 8 24)) (_ BitVec 4))
(declare-const u (_ FloatingPoint 8 24))
(declare-const v (_ FloatingPoint 8 24))
(assert (= u v))
(assert (distinct (f u) (f v)))
(check-sat)
