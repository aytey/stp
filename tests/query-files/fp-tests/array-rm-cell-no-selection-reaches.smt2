; RUN: %solver %s | %OutputCheck %s
;
; A RoundingMode value a model hands back names one of the five modes, even
; where nothing in the query decided it.
;
; The reads FpTotalise pins are the ones the formula names when it runs.
; Read-over-write expansion introduces reads over the base array afterwards,
; and pins them only through the enclosing read they stand in for -- which
; pins them exactly when the expansion selects one. Here j and k are the same
; mode, so the expansion always takes the written value, and (select a RTN)
; is a cell no selection reaches: free bits, and the backend leaves whatever
; it likes in them. get-value printed the raw carrier for it, #b00000, which
; is not a term of the sort and names no mode; through the programmatic model
; API the same value aborted the process.
;
; A cell no observation covers has always been completed with RNE, and this
; is that cell. (select a RTP) is the control: the query decides it, so what
; is printed for it is the mode asserted and not the completion.
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-fun a () (Array RoundingMode RoundingMode))
(declare-fun j () RoundingMode)
(declare-fun k () RoundingMode)
(declare-fun v () RoundingMode)
(assert (= j RTN))
(assert (= k RTN))
(assert (= (select (store a j v) k) v))
(assert (= (select a RTP) RTZ))
; CHECK: ^sat
(check-sat)
; CHECK: ^\( \(select \|a\| RTN\) (RNE|RNA|RTP|RTN|RTZ) \)$
; CHECK: ^\( \(select \|a\| RTP\) RTZ \)$
(get-value ((select a RTN) (select a RTP)))
