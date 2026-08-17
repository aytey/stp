; The extensionality checker reports what its rounds looked like, not just
; how many lemmas it emitted.
;
; The checker deliberately keeps collecting after the first conflict a fixed
; point finds, so a round has no upper bound. That is a good trade when the
; large rounds come first and knock out whole classes of collision at once,
; and a bad one when every round is large -- and a total, or a mean, cannot
; tell those two apart. Until this line existed neither number was printed
; anywhere, so whether to cap a round was not a question anyone could answer
; from evidence.
;
; Five arrays over a sixteen-element sort asserted pairwise distinct: the
; pigeonhole is satisfiable here, and it takes several rounds with more than
; one lemma in some of them, which is what makes the largest-round figure
; mean something.
;
; RUN: %solver -s --array-equality --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --array-equality --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: Array equality: [0-9]+ lemmas, [0-9]+ rounds, largest [0-9]+, [0-9]+ atoms folded
; CHECK: ^sat
;
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun c () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun d () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun e () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (distinct a b c d e))
(check-sat)
