; Per-call constant-bit propagation over the live stack: a pushed
; definer level fixes a flag, the CBP prepass folds the flag through a
; deeper floating-point conjunct's lowered circuit, and the halved
; rewrite is adopted (content-keyed, so the identical re-push is a
; cache hit). The definer's own conjunct must never be consumed by its
; assumed truth -- the fed-conjunct exclusion pins the circularity the
; original experiment branches hit: the deeper bound still binds, so
; the contradicting round is unsat.
; RUN: %solver -s --incremental %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)
(declare-fun p () Bool)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun v () (_ BitVec 8))
(declare-fun w1 () (_ BitVec 32))
(declare-fun w2 () (_ BitVec 32))
(declare-fun w3 () (_ BitVec 32))
; base: keep both float cones alive so the fold is visible
(assert (fp.lt y (fp #b0 #x85 #b00000000000000000000000)))
(assert (bvult v #x05))
(push 1)
(assert (= p true))
; the flag gates the whole choice: under p -> true the lowered ITE
; collapses to x's cone. The ballast conjuncts keep the whole-level
; word-level trial from halving -- the fold is refused there (and the
; context substitution refuses it as a novel floating-point operation),
; so the post-lowered constant-bit pass is the one sanctioned route.
(assert (fp.gt (ite p x y) (_ +zero 8 24)))
(assert (bvult (bvmul w1 w2) #xf0000000))
(assert (bvult (bvadd w2 w3) #xf0000000))
(assert (bvult (bvxor w3 w1) #xf0000000))
; CHECK: cbp adopted
; CHECK: ^sat
(check-sat)
(pop 1)
; the circularity pin: a level whose conjuncts are an assumed flag pair
; AND a real bound; the bound's own assumed truth must not erase it
(push 1)
(assert (and p (fp.gt x (_ +zero 8 24))))
(assert (bvugt v #x10))
; v > 16 contradicts the base's v < 5: the bound must still bind
; CHECK: ^unsat
(check-sat)
(pop 1)
; identical re-push of the adopted round: everything is a cache hit
(push 1)
(assert (= p true))
(assert (fp.gt (ite p x y) (_ +zero 8 24)))
; CHECK: encoded 0 new conjuncts
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
