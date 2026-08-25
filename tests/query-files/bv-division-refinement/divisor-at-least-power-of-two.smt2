; b >=u 2^k -> t <=u (a >> k), the power-of-two divisor schema with its
; equality guard loosened to an inequality. `b = 2^k` names one divisor out of
; 2^256; `b >=u 2^k` names half of them, and taking k from where the candidate
; divisor's top bit sits bounds the quotient to within a factor of two of the
; truth. Nothing else says anything that sharp about a divisor which is
; neither zero nor a power of two -- the only other thing on offer is
; `t <=u a`, which is this same bound at k = 0.
;
; The divisor here is pinned to one binade and the quotient is then said to
; exceed the dividend shifted by that binade's exponent, which the bound
; refutes outright. Without it the refinement enumerates operand pairs and
; does not come back inside a minute; with it, four rounds and no blocking
; lemma at all.
; RUN: %solver --incremental=off --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvuge b (_ bv1267650600228229401496703205376 256)))
(assert (bvult b (_ bv2535301200456458802993406410752 256)))
(assert (bvugt (bvudiv a b) (bvlshr a (_ bv100 256))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
