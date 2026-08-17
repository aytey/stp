; (distinct t1 ... tn) over a sort with fewer than n values is unsatisfiable by
; pigeonhole. The parser expands distinct into C(n, 2) disequalities, so what
; would otherwise reach the solver is binary-encoded pigeonhole -- the shape
; resolution cannot do in polynomial size. Sixteen operands over (_ BitVec 4)
; answer instantly and seventeen did not answer at all; the cliff is one
; operand wide, so the count is checked where the sort is known.
;
; Guarded here: exactly saturating stays satisfiable, one more is refused, the
; same holds one bit down, and Bool is refused at three. A wide sort is never
; exceeded -- 2^32 operands cannot be written -- so that one is left alone and
; is satisfiable as before.
;
; RUN: %solver --SMTLIB2 --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --SMTLIB2 --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^unsat
; CHECK: REACHED-END
;
(set-logic QF_BV)

; sixteen values, sixteen operands: satisfiable, and it must not be folded.
(push 1)
(declare-const a0 (_ BitVec 4))
(declare-const a1 (_ BitVec 4))
(declare-const a2 (_ BitVec 4))
(declare-const a3 (_ BitVec 4))
(declare-const a4 (_ BitVec 4))
(declare-const a5 (_ BitVec 4))
(declare-const a6 (_ BitVec 4))
(declare-const a7 (_ BitVec 4))
(declare-const a8 (_ BitVec 4))
(declare-const a9 (_ BitVec 4))
(declare-const a10 (_ BitVec 4))
(declare-const a11 (_ BitVec 4))
(declare-const a12 (_ BitVec 4))
(declare-const a13 (_ BitVec 4))
(declare-const a14 (_ BitVec 4))
(declare-const a15 (_ BitVec 4))
(assert (distinct a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
(check-sat)
; one more than the sort holds.
(declare-const a16 (_ BitVec 4))
(assert (distinct a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16))
(check-sat)
(pop 1)

; three values in a two-value sort, one bit down.
(push 1)
(declare-const b0 (_ BitVec 1))
(declare-const b1 (_ BitVec 1))
(declare-const b2 (_ BitVec 1))
(assert (distinct b0 b1 b2))
(check-sat)
(pop 1)

; Bool has two values, and reaches the other distinct rule.
(push 1)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (distinct p q r))
(check-sat)
(pop 1)
(push 1)
(declare-const s Bool)
(declare-const t Bool)
(assert (distinct s t))
(check-sat)
(pop 1)

; A width the count cannot exceed is left alone: this is unsatisfiable for an
; ordinary reason, not by cardinality.
(push 1)
(declare-const w0 (_ BitVec 32))
(declare-const w1 (_ BitVec 32))
(assert (distinct w0 w1))
(assert (= w0 w1))
(check-sat)
(pop 1)
(echo "REACHED-END")
