; (s ^ (x | t)) >=u (t ^ 1), which is Bitwuzla's UDIV33 and the strongest of
; the fifteen facts that fired nothing where the rest were ranked: it rules
; out 49.2% of the (x, s, t) cube at six bits, behind only
; `x >=u -((-s) & (-t))` among everything measured. Strength and marginal
; productivity disagree about this fact more than about any other in the
; registry, which is the reason to keep it reachable and the reason it is not
; in the inherited profile.
;
; It needs no variable shift -- two bitwise mixtures and a comparison -- so
; where it is the crux it is very cheap. Without it the refinement finds the
; contradiction the long way round, through the bounds and the magnitude
; schema: 12 rounds, 7.0s and 105MB at 256 bits. With it, 8 rounds, 0.33s and
; 28MB, and exactly two of the lemmas installed come from `udiv-extra`.
;
; The RUN line names the family because that is the point of it being a
; family: the fact is sound and tested whatever the mask says, and the mask
; is what decides whether a run pays for it.
; RUN: %solver --incremental=off --bv-term-abstraction=1 --bv-term-abstraction-schema-groups=base,udiv-extra %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvult (bvxor b (bvor a (bvudiv a b))) (bvxor (bvudiv a b) (_ bv1 256))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
