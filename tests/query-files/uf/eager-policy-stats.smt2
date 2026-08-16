; The eager congruence policy reports what it decided under -s. Without this
; the only way to tell a declined declaration from one that had nothing to
; install is to edit a flag and compare wall clock.
;
; Three outcomes are pinned here. g has two applications over symbolic
; arguments, so it has one pair and is selected. h has two applications whose
; first arguments are distinct constants, so its one enumerated pair is
; impossible and it emits nothing -- the estimate says one, the emitted count
; says zero, and both are reported. The total names the budget.
;
; RUN: %solver --uninterpreted-functions --incremental=off -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on -s %s 2>&1 | %OutputCheck %s
; CHECK: UF: eager selected g \(2 applications, 1 pairs estimated, 1 enumerated, 0 impossible, 1 constraints\)
; CHECK: UF: eager selected h \(2 applications, 1 pairs estimated, 1 enumerated, 1 impossible, 0 constraints\)
; CHECK: UF: eager total 2/2 declarations, 1 constraints, budget 2/4096 spent
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(declare-fun h ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvult (g x) (bvadd (g y) #x10)))
(assert (bvult (h #x01 x) (bvadd (h #x02 y) #x10)))
(check-sat)
