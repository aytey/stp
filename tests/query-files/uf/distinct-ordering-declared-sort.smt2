; The ordering rewrite declines a group larger than its carrier can hold.
;
; A sort from (declare-sort S 0) is carried by a bit-vector of --uf-sort-width
; bits, and the sort itself is unbounded, so the carrier's capacity is a fact
; about the encoding and not about the query. Five elements over a two-bit
; carrier are unsatisfiable in that encoding and satisfiable in the theory --
; and a chain says so immediately where the clique has to be searched for. That
; is exactly the case where being fast is the wrong thing to be: the same call
; the parser's cardinality fold already makes, for the same reason, and it is
; made here too rather than inherited, because the fold deliberately leaves
; declared sorts alone.
;
; Widen the carrier by one bit and the group fits, and it is ordered. Nothing
; about the guard is about declared sorts as such -- where the width really is
; the sort's own, the parser has already replaced an oversized group with
; false and there is nothing left here to order.
;
; RUN: %solver --uninterpreted-functions --incremental=off -s --uf-sort-width=2 %s 2>&1 | %OutputCheck --check-prefix=TIGHT %s
; RUN: %solver --uninterpreted-functions --incremental=off -s --uf-sort-width=3 %s 2>&1 | %OutputCheck --check-prefix=ROOMY %s
;
; TIGHT-NOT: Ordered
; TIGHT: ^unsat
;
; ROOMY: Ordered 1 symmetric distinct group\(s\)
; ROOMY: ^sat
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
