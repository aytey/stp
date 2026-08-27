; x >=u ((x | s) & (q << 1)), for q = x udiv s.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=udiv-observed %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: BVDIV dividend-above-or-and-doubled-quotient lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 128))
(declare-fun s () (_ BitVec 128))
(assert
  (bvult x
         (bvand (bvor x s)
                (bvshl (bvudiv x s) (_ bv1 128)))))
(check-sat)
(exit)
