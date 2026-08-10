Generators for the inputs the recursion audit measured against.

Each writes one query to stdout at a chosen depth. They are here rather than
in tests/query-files because they are not tests: the depths that matter are
far larger than a test suite should solve on every run, and the point of
having them is to re-measure a line of ast-recursion-allowlist.txt after
touching the pass it names.

    python3 scripts/deep-inputs/gen.py fp-add 8000 > /tmp/q.smt2
    stp --SMTLIB2 /tmp/q.smt2

What each shape reaches, as measured on 2026-08-10 at the ordinary 8 MiB:

    fp-add     SplitExtracts::buildMap, between 30,000 and 60,000. This
               shape has moved three times as the passes in front of it were
               converted: 7,000-8,000 in the simplifier's formula arms, then
               20,000-30,000 in FpTotalise::visit, now here
    store      numberOfReadsLessThan, which STP.cpp asks on every array
               solve, between 100,000 and 200,000
    and-nest   nothing, and now for two reasons: the simplifying factory
               flattens a conjunction as it builds it, so the nested node
               never reaches FlattenKind -- and FlattenKind walks on the heap
               since the commit that added deep_flatten_kind_no_duplicates,
               so a pass building through the hashing factory would not die
               there either
    ite        nothing since the format and sort derivations were converted
