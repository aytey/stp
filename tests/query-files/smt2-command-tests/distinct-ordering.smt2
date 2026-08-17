; A distinct whose operands are variables occurring nowhere else is ordered.
;
; Every permutation of such operands maps the formula to itself, so requiring
; them to increase discards n!-1 copies of each answer and keeps one. What is
; left is n-1 comparisons in place of n(n-1)/2 disequalities, and, more to the
; point, an ordering the bit-blaster is told rather than made to find: three
; hundred 32-bit variables under one distinct take 85 seconds pairwise and a
; tenth of a second chained.
;
; The three blocks are the guard's decision, not three shapes of the same
; case. Only the first is symmetric. In the second, b is compared outside the
; distinct, so the operands are no longer interchangeable and imposing
; a < b < c would contradict b < a -- reporting unsat where the answer is sat.
; In the third the distinct is negated, where the chain is the weaker claim,
; so a model of the rewritten formula need not be a model of the input; the
; rewrite declines rather than publish a model it cannot stand behind.
;
; RUN: %solver -s --incremental=off %s 2>&1 | %OutputCheck %s
; CHECK: Ordered 1 symmetric distinct group\(s\)
; CHECK: ^sat
; CHECK: SYMMETRIC-DONE
; CHECK-NOT: Ordered 1 symmetric distinct group\(s\)
; CHECK: ^sat
; CHECK: LEAKED-DONE
; CHECK-NOT: Ordered 1 symmetric distinct group\(s\)
; CHECK: ^sat
;
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(declare-const keep (_ BitVec 8))
(assert (distinct a b c))
(assert (bvult keep #x10))
(check-sat)
(echo "SYMMETRIC-DONE")
(reset)
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (distinct a b c))
(assert (bvult b a))
(check-sat)
(echo "LEAKED-DONE")
(reset)
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (not (distinct a b c)))
(check-sat)
