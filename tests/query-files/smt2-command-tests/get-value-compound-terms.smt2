; SMT-LIB 2.6 3.9.1: (get-value (t1 ... tn)) answers ((t1 v1) ... (tn vn)) for
; any well-sorted terms, not only for variables. STP used to accept a bare
; symbol and answer "unsupported" for everything else, so no query could read
; the model value of an expression it had actually written.
;
; The model evaluator already decides all of these -- get-value simply refused
; to ask it. Each row below is a shape the evaluator handles: an arithmetic
; term, a predicate, an array read, an if-then-else, a floating-point term and
; a rounding mode. Values are pinned by construction so the output is
; deterministic.
;
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
;
; The term is echoed as STP's interned node rather than as the input text --
; there is no surface syntax to keep, since hash-consing happens at parse
; time -- so commutative operands come back in STP's canonical order. The
; pairing is still unambiguous: two spellings of one term are one node and
; get one answer.
;
; CHECK: ^sat
; CHECK-L: ( |x|  #x2A )
; CHECK-L: ( |p| true )
; CHECK-L: ( (bvadd  #x01 |x|)  #x2B )
; CHECK-L: ( (= |x|  #x2A) true )
; CHECK-L: ( (= |x|  #x00) false )
; CHECK-L: ( (select |a|  #x00)  #x07 )
; CHECK-L: ( (ite |p| |x|  #x00)  #x2A )
; CHECK-L: ( |f| (fp #b0 #b10000000 #b10000000000000000000000) )
; CHECK-L: ( |r| RTZ )
; A single command answers every term it was given, in the order asked.
; CHECK-L: ( |x|  #x2A )
; CHECK-L: ( (bvnot |x|)  #xD5 )
; CHECK-L: ( |p| true )
; An array has no SMT-LIB2 value spelling here; (get-model) prints the
; completed interpretation instead. It is refused, not evaluated -- reaching
; the Boolean branch of the printer with an array used to abort the process.
; CHECK-L: unsupported
; CHECK: REACHED-END
;
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(declare-const p Bool)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const f (_ FloatingPoint 8 24))
(declare-const r RoundingMode)
(assert (= x #x2a))
(assert p)
(assert (= (select a #x00) #x07))
(assert (= f (fp #b0 #b10000000 #b10000000000000000000000)))
(assert (= r RTZ))
(check-sat)
(get-value (x))
(get-value (p))
(get-value ((bvadd x #x01)))
(get-value ((= x #x2a)))
(get-value ((= x #x00)))
(get-value ((select a #x00)))
(get-value ((ite p x #x00)))
(get-value (f))
(get-value (r))
(get-value (x (bvnot x) p))
(get-value (a))
(echo "REACHED-END")
