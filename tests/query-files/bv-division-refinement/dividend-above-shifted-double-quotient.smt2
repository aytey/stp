; x >=u ((t << 1) >> (t << s)), where t = x udiv s. This is UDIV15,
; the highest-firing division fact left out of the first port. Its nested
; variable shift is also the end-to-end check for the generic left barrel
; shifter added to express it.
;
; The assertion is exactly the negation of the fact. With a 256-bit quotient
; abstraction, installing that fact should decide the query without falling
; through to an exact divider.
; RUN: %solver -s --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 --bv-term-abstraction-schema-groups=udiv15 %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: BVDIV dividend-above-shifted-double-quotient lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
;
; ... and what that one lemma cost. This fact is three barrel shifters spliced
; through BVExactEncoder -- the same encoder an escalation goes through -- and
; for a while the cost line covered the escalations only, so a run whose whole
; refinement was schema lemmas reported no price at all. A profile is a choice
; of which schema families to enable, so this is the number a profile
; comparison most needs. Regexes rather than the measured 229,374 clauses:
; what has to hold is that a price is reported and is not zero, and pinning
; ABC's cut choices would make this a test of the mapper.
;
; RUN: %solver -t --incremental=off --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=udiv15 %s 2>&1 | %OutputCheck --check-prefix=COST %s
; COST: Abstraction refinement: rounds=1 blocking=0 schema=1 exact=0
; COST: Abstraction schema cost: clauses=[1-9][0-9]* variables=[1-9][0-9]* microseconds=[0-9]+
; COST: udiv15=1
; COST: ^unsat$
;
; There is no exact control leg here, and there cannot be an affordable one:
; the assertion is the negation of the fact, so anything that does not install
; the fact has to prove a 256-bit divider unsatisfiable, which does not finish.
; What this leg establishes is that the fact is offered, named and applied end
; to end at a realistic width -- not that it is true. That is established by
; BVAbstractionLemma_Test, which checks every fact against the operation
; exhaustively below seven bits, by sampling at eight through sixty-four, and
; against the circuit STP blasts for the operation itself.
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 256))
(declare-fun s () (_ BitVec 256))
(assert
  (let ((t (bvudiv x s)))
    (bvult x (bvlshr (bvshl t (_ bv1 256)) (bvshl t s)))))
(check-sat)
(exit)
