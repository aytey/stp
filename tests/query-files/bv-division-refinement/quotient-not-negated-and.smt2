; q != -(s & ~x), for q = x udiv s.
;
; The groups are disjoint: this fact belongs to udiv-observed, so selecting
; the unranked tail on its own must not reach it.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=udiv-observed %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=udiv-tail %s 2>&1 | %OutputCheck %s --check-prefix=TAILONLY
; TAILONLY-NOT: quotient-not-negated-and
; CHECK: BV abstraction: BVDIV quotient-not-negated-and lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 128))
(declare-fun s () (_ BitVec 128))
(assert (= (bvudiv x s) (bvneg (bvand s (bvnot x)))))
(check-sat)
(exit)
