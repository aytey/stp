; ... and with facts wider than the four schemas, taken from the same source
; as the division ones.
;
; The schemas beside this file are guarded on an operand's value or read off
; the product's low bits. These two are neither: they relate the product to
; both operands at once, and one of them shifts by a variable amount, which
; is why they are built by the bit-blaster rather than written a clause at a
; time.
;
;   s = s << (x & (1 >> t))     the shift amount is one exactly when the
;                               product is zero and x is odd, and then it
;                               forces s to zero
;   (x & t) != (s | ~t)         synthesised; not a theorem anyone wrote down
;
; The assertion below is the negation of the first, so nothing but that fact
; refutes it without an exact 256-bit multiplier. Three legs, as for the
; schemas: with them, without them, and without the abstraction at all. A
; fact that was merely usually true would show as a disagreement.
;
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=LEMMAS %s
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-schemas=0 %s 2>&1 | %OutputCheck --check-prefix=NOSCHEMAS %s
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; LEMMAS-NOT: Fatal Error
; LEMMAS-NOT: Assertion
; LEMMAS: BV abstraction: BVMULT factor-unchanged-by-masked-shift lemma over operand [01]
; LEMMAS: ^unsat$
;
; NOSCHEMAS-NOT: Fatal Error
; NOSCHEMAS-NOT: BVMULT [a-z-]+ lemma
; NOSCHEMAS: ^unsat$
;
; PLAIN: ^unsat$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (not (= b (bvshl b (bvand a (bvlshr (_ bv1 256) (bvmul a b)))))))
(check-sat)
