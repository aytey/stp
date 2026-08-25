; x >=u ((t << 1) >> (t << s)), where t = x udiv s. This is UDIV15,
; the highest-firing division fact left out of the first port. Its nested
; variable shift is also the end-to-end check for the generic left barrel
; shifter added to express it.
;
; The assertion is exactly the negation of the fact. With a 256-bit quotient
; abstraction, installing that fact should decide the query without falling
; through to an exact divider.
; RUN: %solver -s --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: BVDIV dividend-above-shifted-double-quotient lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 256))
(declare-fun s () (_ BitVec 256))
(assert
  (let ((t (bvudiv x s)))
    (bvult x (bvlshr (bvshl t (_ bv1 256)) (bvshl t s)))))
(check-sat)
(exit)
