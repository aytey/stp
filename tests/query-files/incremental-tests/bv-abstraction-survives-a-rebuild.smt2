; The records do not survive the solver they were refined into.
;
; The abstraction records carry what refinement has established -- which bits
; of an equality have been pinned, how many blocking lemmas an operation has
; been given, whether it is exactly encoded by now -- and every one of those
; claims is about clauses in a particular SAT solver, over that solver's
; variable numbering. The driver replaces its solver (a configuration latch,
; a promoted level retracted) and rotates its whole encoding epoch (memory
; relief), and neither carries the clauses across. Records kept over such a
; boundary would say an abstraction was already pinned when nothing pins it,
; which is the unrefined encoding again, silently.
;
; So a rebuild forgets them and the next solve harvests and refines from
; nothing. This drives it: the two limits are set to 1, which makes every
; check-sat past the first eligible for relief, and the pushed levels are
; distinct enough that the epoch really does rotate. Twelve equalities, five
; multiplies and five comparisons are abstracted along the way.
;
; -s is on so the rotation is visible rather than assumed, and -d re-derives
; every model against the raw stack. The control leg is the same session
; without the abstractions.
;
; RUN: %solver --incremental=on --array-equality -d -s --incremental-semantic-cache-limit=1 --incremental-reencode-limit=1 --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-eq-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=on --array-equality -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: encoding epoch reset
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const x0 (_ BitVec 8))
(declare-const i0 (_ BitVec 4))
(declare-const x1 (_ BitVec 8))
(declare-const i1 (_ BitVec 4))
(declare-const x2 (_ BitVec 8))
(declare-const i2 (_ BitVec 4))
(declare-const x3 (_ BitVec 8))
(declare-const i3 (_ BitVec 4))
(declare-const x4 (_ BitVec 8))
(declare-const i4 (_ BitVec 4))
(assert (= (select a #x0) #x01))
(push 1)
(assert (bvult (bvmul x0 x1) (bvadd x0 #x07)))
(assert (= (select a i0) x0))
(assert (distinct x0 x2))
(check-sat)
(pop 1)
(push 1)
(assert (bvult (bvmul x1 x2) (bvadd x1 #x07)))
(assert (= (select a i1) x1))
(assert (distinct x1 x3))
(check-sat)
(pop 1)
(push 1)
(assert (bvult (bvmul x2 x3) (bvadd x2 #x07)))
(assert (= (select a i2) x2))
(assert (distinct x2 x4))
(check-sat)
(pop 1)
(push 1)
(assert (bvult (bvmul x3 x4) (bvadd x3 #x07)))
(assert (= (select a i3) x3))
(assert (distinct x3 x0))
(check-sat)
(pop 1)
(push 1)
(assert (bvult (bvmul x4 x0) (bvadd x4 #x07)))
(assert (= (select a i4) x4))
(assert (distinct x4 x1))
(check-sat)
(pop 1)
(check-sat)
(exit)
