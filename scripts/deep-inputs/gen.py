#!/usr/bin/env python3
"""Write one deeply nested query. See README.md for what each shape reaches.

Usage: gen.py <fp-add|store|and-nest|ite> <depth>
"""

import sys


def fp_add(n, out):
    out("(set-logic QF_FP)")
    out("(declare-fun x () (_ FloatingPoint 8 24))")
    out("(define-fun t0 () (_ FloatingPoint 8 24) x)")
    for i in range(1, n):
        out("(define-fun t%d () (_ FloatingPoint 8 24) (fp.add RNE t%d x))"
            % (i, i - 1))
    out("(assert (fp.isNaN t%d))" % (n - 1))


def store(n, out):
    out("(set-logic QF_ABV)")
    out("(declare-fun A () (Array (_ BitVec 8) (_ BitVec 8)))")
    out("(declare-fun j () (_ BitVec 8))")
    out("(define-fun a0 () (Array (_ BitVec 8) (_ BitVec 8)) A)")
    for i in range(1, n):
        out("(define-fun a%d () (Array (_ BitVec 8) (_ BitVec 8)) "
            "(store a%d (_ bv%d 8) (_ bv0 8)))" % (i, i - 1, i % 256))
    out("(assert (= (select a%d j) #x01))" % (n - 1))


def and_nest(n, out):
    out("(set-logic QF_BV)")
    for i in range(n):
        out("(declare-fun p%d () Bool)" % i)
    out("(define-fun c0 () Bool p0)")
    for i in range(1, n):
        out("(define-fun c%d () Bool (and p%d c%d))" % (i, i, i - 1))
    out("(assert c%d)" % (n - 1))


def ite(n, out):
    out("(set-logic QF_BV)")
    out("(declare-fun x () (_ BitVec 8))")
    out("(declare-fun p () Bool)")
    out("(define-fun t0 () (_ BitVec 8) x)")
    for i in range(1, n):
        out("(define-fun t%d () (_ BitVec 8) (ite p #x00 t%d))" % (i, i - 1))
    out("(assert (= t%d #x01))" % (n - 1))


SHAPES = {"fp-add": fp_add, "store": store, "and-nest": and_nest, "ite": ite}


def main():
    if len(sys.argv) != 3 or sys.argv[1] not in SHAPES:
        print("usage: gen.py <%s> <depth>" % "|".join(sorted(SHAPES)),
              file=sys.stderr)
        return 2

    lines = []
    SHAPES[sys.argv[1]](int(sys.argv[2]), lines.append)
    lines += ["(check-sat)", "(exit)"]
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    sys.exit(main())
