Generators for the inputs the recursion audit measured against.

Each writes one query to stdout at a chosen depth. They are here rather than
in tests/query-files because they are not tests: the depths that matter are
far larger than a test suite should solve on every run, and the point of
having them is to re-measure a line of ast-recursion-allowlist.txt after
touching the pass it names.

    python3 scripts/deep-inputs/gen.py fp-add 8000 > /tmp/q.smt2
    stp --SMTLIB2 /tmp/q.smt2

What each shape reaches, as measured on 2026-08-10 at the ordinary 8 MiB:

    fp-add     the simplifier's formula recursion (SimplifyFormula ->
               simplifyNonAndOr -> SimplifyIteFormula) between 7,000 and
               8,000; with --disable-simplifications it gets past that and
               dies in FpTotalise::visit between 20,000 and 40,000
    store      numberOfReadsLessThan, which STP.cpp asks on every array
               solve, between 100,000 and 200,000
    and-nest   nothing: the simplifying factory flattens a conjunction as it
               builds it, so FlattenKindNoDuplicates never sees the nesting
    ite        nothing since the format and sort derivations were converted
