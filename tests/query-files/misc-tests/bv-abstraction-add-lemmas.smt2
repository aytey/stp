; The ADD registry, which is off. `msb(x) = msb(s) = 0 -> t >=u (x | s)` is
; the crux here: two operands with a clear top bit cannot add to less than
; their disjunction, so the query is unsatisfiable for exactly that reason
; and the fact is what settles it.
;
; Three legs, and the third is the point of the family being off. With the
; facts the refinement takes three rounds and installs two of them; without
; them it takes two rounds and encodes the adder. Addition is the one
; abstracted operation whose exact encoding is linear and immediate, so a
; fact that defers it is competing against something cheap -- which is why
; `add` is not in the inherited profile, and why what is checked here is
; that the facts are sound and reachable rather than that they are fast.
; RUN: %solver --incremental=off --bv-term-abstraction=1 --bv-term-abstraction-schema-groups=base,add %s | %OutputCheck %s
; RUN: %solver --incremental=off --bv-term-abstraction=1 %s | %OutputCheck %s
; RUN: %solver --incremental=off %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (= ((_ extract 255 255) a) #b0))
(assert (= ((_ extract 255 255) b) #b0))
(assert (bvult (bvadd a b) (bvor a b)))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
