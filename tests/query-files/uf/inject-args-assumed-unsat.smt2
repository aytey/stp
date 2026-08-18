; An unsat reached over injectivity STP assumed for itself is withheld, and
; says which flag assumed it.
;
; --uf-inject-args adds the converse of congruence to the eager encoding: for
; a declaration whose results are compared only with each other, results equal
; implies arguments equal. Congruence is entailed by the query and preserves
; both answers. Its converse is not entailed by anything -- it says the
; function is injective, which the caller never wrote -- so what the encoding
; then describes is the query with that assumption conjoined.
;
; Which way that can go wrong is not symmetric. An assumption only ever removes
; models, so a model of the strengthened formula is a model of the query and
; `sat` is sound whatever was assumed. Only `unsat` can be an artefact, and it
; is also the one answer a caller cannot tell from a real refutation. So the
; query is solved and only an `unsat` is withheld -- the same bargain
; declared-sort-carrier-exhausted.smt2 strikes for a carrier too narrow to hold
; the query.
;
; Both queries below are satisfiable, and both answered `unsat` under the flag.
; The second is the one a cross-checked fuzzing campaign found; the first is
; the sharper statement of the same thing, because its last assertion is a
; tautology -- three applications into a one-bit codomain must collide -- so
; there is no query content to be non-injective about at all.
;
; The rule is deliberately coarse: it withholds whenever an injectivity
; implication was installed, not when one was used in the refutation. An unsat
; that had nothing to do with the assumption is withheld too. That costs
; answers only under a flag that is off by default and never claims to preserve
; verdicts, and the alternative is deciding entailment, which is another solve.
; Installing none of them -- the flag off, or on with no declaration that
; qualifies -- leaves the unsat exactly as it was; the last block pins that.
;
; RUN: %solver --uninterpreted-functions --incremental=off --uf-inject-args=1 %s 2>&1 | %OutputCheck --check-prefix=ASSUMED %s
; RUN: %solver --uninterpreted-functions --incremental=on  --uf-inject-args=1 %s 2>&1 | %OutputCheck --check-prefix=ASSUMED %s
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
; RUN: %solver --uninterpreted-functions --incremental=on  %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ASSUMED-NOT: ^unsat
; ASSUMED: ^unknown
; ASSUMED: :reason-unknown \(incomplete "--uf-inject-args assumed 1 uninterpreted function\(s\) injective, adding 3 implication\(s\) the query does not entail, so this unsat may be an artefact of that assumption rather than a refutation; re-run without --uf-inject-args to decide the query"\)
; ASSUMED: PIGEONHOLE-DONE
;
; PLAIN: ^sat
; PLAIN: :reason-unknown \(error "the last answer was not unknown"\)
; PLAIN: PIGEONHOLE-DONE
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 2)) (_ BitVec 1))
(declare-fun a () (_ BitVec 2))
(declare-fun b () (_ BitVec 2))
(declare-fun c () (_ BitVec 2))
(assert (distinct a b))
(assert (distinct b c))
(assert (distinct a c))
(assert (or (= (f a) (f b)) (= (f b) (f c)) (= (f a) (f c))))
(check-sat)
(get-info :reason-unknown)
(echo "PIGEONHOLE-DONE")
;
; The query the campaign minimised to. Two applications into a one-bit
; codomain, so injectivity is achievable here on cardinality grounds and a
; capacity test would have let this one through: what rules the models out is
; that the query asserts the two results equal while forcing the arguments
; apart. Cardinality is not the property that makes the assumption safe.
;
; ASSUMED-NOT: ^unsat
; ASSUMED: ^unknown
; ASSUMED: :reason-unknown \(incomplete "--uf-inject-args assumed 1 uninterpreted function\(s\) injective, adding 1 implication\(s\) the query does not entail
; ASSUMED: MINIMISED-DONE
;
; PLAIN: ^sat
; PLAIN: MINIMISED-DONE
(reset)
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 1))
(declare-fun g ((_ BitVec 1)) (_ BitVec 1))
(assert (= (= x (bvneg (_ bv1 1))) false))
(assert (= (g (bvneg (_ bv1 1))) (g x)))
(check-sat)
(get-info :reason-unknown)
(echo "MINIMISED-DONE")
;
; A satisfiable query keeps its answer with the assumption installed over it:
; the assumption removes models and this one has models left, so the answer is
; the query's own and refusing it would be a plain loss. h is injective in
; every model of this query anyway, which is the shape the flag exists for.
;
; ASSUMED: ^sat
; ASSUMED: KEPT-DONE
; PLAIN: ^sat
; PLAIN: KEPT-DONE
(reset)
(set-logic QF_UFBV)
(declare-fun p () (_ BitVec 4))
(declare-fun q () (_ BitVec 4))
(declare-fun h ((_ BitVec 4)) (_ BitVec 4))
(assert (distinct p q))
(assert (distinct (h p) (h q)))
(check-sat)
(echo "KEPT-DONE")
;
; Nothing was assumed here, so nothing is withheld. k has one application, so
; the eager encoding has no pair to state congruence over and none to state its
; converse over either; the flag is on and installs nothing, and the refutation
; is reported as the refutation it is.
;
; ASSUMED: ^unsat
; ASSUMED: NOTHING-ASSUMED-DONE
; PLAIN: ^unsat
; PLAIN: NOTHING-ASSUMED-DONE
(reset)
(set-logic QF_UFBV)
(declare-fun r () (_ BitVec 4))
(declare-fun k ((_ BitVec 4)) (_ BitVec 4))
(assert (= (k r) (_ bv1 4)))
(assert (= (k r) (_ bv2 4)))
(check-sat)
(echo "NOTHING-ASSUMED-DONE")
