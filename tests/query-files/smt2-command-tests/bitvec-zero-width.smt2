; (_ BitVec 0) is not a sort, and saying so is the parser's job.
;
; SourceSort::bitVector asserts a positive width, so a zero reached it and
; aborted inside a header on an asserting build. Without assertions the symbol
; kept a zero value width, which the legacy width checks read as a Boolean, and
; the query went on to be answered and to print a model at the wrong sort. The
; array-component rule already refused it with this wording; the three scalar
; rules -- declare-const, declare-fun with no arguments, and a define-fun
; formal -- did not, and each is reachable with no flags at all.
;
; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: bit-vectors must be of positive length
;
(set-logic QF_BV)
(declare-const a (_ BitVec 0))
(assert (distinct a a))
(check-sat)
