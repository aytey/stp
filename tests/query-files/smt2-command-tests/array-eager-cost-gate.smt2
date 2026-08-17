; Eager array Ackermannisation is gated on what the expansion would build,
; not only on how many reads there are.
;
; A read whose array operand is a chain of stores becomes one if-then-else per
; link in that chain, so the read count alone cannot tell a cheap expansion from
; a ruinous one: nine reads over a deep chain expand into tens of thousands of
; nodes and took 48x longer than leaving them to read refinement, on a query
; differing from a fast one by a single read.
;
; Both halves here have nine reads, which is under the count threshold. The
; first is over a 25-deep store chain and must NOT take the eager path; the
; second is over the bare array and must, which is what says the gate still
; admits the flat queries the count threshold was tuned for.
;
; RUN: %solver -s --incremental=off %s 2>&1 | %OutputCheck %s
; CHECK-NOT: Have removed array operations
; CHECK: ^sat
; CHECK: DEEP-DONE
; CHECK: Have removed array operations
; CHECK: ^sat
;
(set-logic QF_ABV)
(declare-const A (Array (_ BitVec 16) (_ BitVec 16)))
(declare-const r0 (_ BitVec 16))
(declare-const r1 (_ BitVec 16))
(declare-const r2 (_ BitVec 16))
(declare-const r3 (_ BitVec 16))
(declare-const r4 (_ BitVec 16))
(declare-const r5 (_ BitVec 16))
(declare-const r6 (_ BitVec 16))
(declare-const r7 (_ BitVec 16))
(declare-const r8 (_ BitVec 16))
(define-fun deep () (Array (_ BitVec 16) (_ BitVec 16)) (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store A (_ bv0 16) (_ bv1 16)) (_ bv1 16) (_ bv4 16)) (_ bv2 16) (_ bv7 16)) (_ bv3 16) (_ bv10 16)) (_ bv4 16) (_ bv13 16)) (_ bv5 16) (_ bv16 16)) (_ bv6 16) (_ bv19 16)) (_ bv7 16) (_ bv22 16)) (_ bv8 16) (_ bv25 16)) (_ bv9 16) (_ bv28 16)) (_ bv10 16) (_ bv31 16)) (_ bv11 16) (_ bv34 16)) (_ bv12 16) (_ bv37 16)) (_ bv13 16) (_ bv40 16)) (_ bv14 16) (_ bv43 16)) (_ bv15 16) (_ bv46 16)) (_ bv16 16) (_ bv49 16)) (_ bv17 16) (_ bv52 16)) (_ bv18 16) (_ bv55 16)) (_ bv19 16) (_ bv58 16)) (_ bv20 16) (_ bv61 16)) (_ bv21 16) (_ bv64 16)) (_ bv22 16) (_ bv67 16)) (_ bv23 16) (_ bv70 16)) (_ bv24 16) (_ bv73 16)))
(assert (distinct (select deep r0) (select deep r1) (select deep r2) (select deep r3) (select deep r4) (select deep r5) (select deep r6) (select deep r7) (select deep r8)))
(check-sat)
(echo "DEEP-DONE")
(reset)
(set-logic QF_ABV)
(declare-const B (Array (_ BitVec 16) (_ BitVec 16)))
(declare-const s0 (_ BitVec 16))
(declare-const s1 (_ BitVec 16))
(declare-const s2 (_ BitVec 16))
(declare-const s3 (_ BitVec 16))
(declare-const s4 (_ BitVec 16))
(declare-const s5 (_ BitVec 16))
(declare-const s6 (_ BitVec 16))
(declare-const s7 (_ BitVec 16))
(declare-const s8 (_ BitVec 16))
(assert (distinct (select B s0) (select B s1) (select B s2) (select B s3) (select B s4) (select B s5) (select B s6) (select B s7) (select B s8)))
(check-sat)
