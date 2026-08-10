; Exact-stack preprocessing is deliberately deferred until the second
; persistent solve: the first array round keeps its useful raw search shape,
; while later changing stacks receive the cheap global reductions that the
; batch pipeline would have applied.  The second scope also redefines a
; symbol whose SAT bits were created by the first scope.  Its scoped model
; definition must win over those now-inactive bits, then be replaced again in
; the third scope.
; RUN: %solver --array-equality --incremental --incremental-profile --check-sanity %s 2>&1 | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))

(push 1)
(assert (= a b))
(assert (= x #x00))
; CHECK: Incremental profile cbp/backend: check=1 .*ext-preprocesses=0 ext-eliminations=0.*extensionality=1
; CHECK: ^sat
(check-sat)
; CHECK: \|x\| +#x00
(get-value (x))
(pop 1)

(push 1)
(assert (= a b))
(assert (= x #x2a))
; CHECK: Incremental profile cbp/backend: check=2 .*ext-preprocesses=1 ext-eliminations=[1-9][0-9]*.*extensionality=1
; CHECK: Incremental profile total: checks=2 .*ext-preprocesses=1 ext-eliminations=[1-9][0-9]*
; CHECK: ^sat
(check-sat)
; CHECK: \|x\| +#x2A
(get-value (x))
(pop 1)

(push 1)
(assert (= a b))
(assert (= x #x7f))
; CHECK: Incremental profile cbp/backend: check=3 .*ext-preprocesses=1 ext-eliminations=[1-9][0-9]*.*extensionality=1
; CHECK: Incremental profile total: checks=3 .*ext-preprocesses=2 ext-eliminations=[1-9][0-9]*
; CHECK: ^sat
(check-sat)
; CHECK: \|x\| +#x7F
(get-value (x))
(pop 1)
(exit)
