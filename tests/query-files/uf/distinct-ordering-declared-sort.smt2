; The ordering rewrite declines a group larger than its carrier can hold.
;
; A sort from (declare-sort S 0) is carried by a bit-vector of --uf-sort-width
; bits and is itself unbounded, so the carrier's capacity is a fact about the
; encoding and not about the query. Where the width really is the sort's own,
; the parser's cardinality fold has already replaced an oversized group with
; false and there is nothing left here to order; where it is a carrier, the
; fold stands down deliberately, and this declines for the same reason rather
; than inheriting it.
;
; What the narrow leg deliberately does NOT check is the verdict. Five elements
; of an unbounded sort are satisfiable, and STP answers unsat at a two-bit
; carrier -- not because of anything this rewrite does, but because the carrier
; cannot represent five elements and nothing tells the caller so. Asserting
; that unsat here would pin a wrong answer as expected output, which is how the
; defect would come to be defended by its own test suite. The verdict is left
; unasserted, and the open item is the carrier, not the rewrite: a declared sort
; has no identity of its own, so its cardinality cannot be distinguished from
; its carrier's.
;
; Widen the carrier by one bit and the group fits. Then the answer is the
; query's own, and the leg checks it.
;
; RUN: %solver --uninterpreted-functions --incremental=off -s --uf-sort-width=2 %s 2>&1 | %OutputCheck --check-prefix=TIGHT %s
; RUN: %solver --uninterpreted-functions --incremental=off -s --uf-sort-width=3 %s 2>&1 | %OutputCheck --check-prefix=ROOMY %s
;
; TIGHT-NOT: Ordered
; TIGHT: DECLARED-SORT-DONE
;
; ROOMY: Ordered 1 symmetric distinct group\(s\)
; ROOMY: ^sat
; ROOMY: DECLARED-SORT-DONE
;
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun e0 () S)
(declare-fun e1 () S)
(declare-fun e2 () S)
(declare-fun e3 () S)
(declare-fun e4 () S)
(assert (distinct e0 e1 e2 e3 e4))
(check-sat)
(echo "DECLARED-SORT-DONE")
