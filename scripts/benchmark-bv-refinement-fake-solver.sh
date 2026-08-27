#!/usr/bin/env bash

# A deterministic stand-in for the benchmark harness regression. It accepts
# the harness's ordinary STP arguments, reads only the final query path, and
# emits the same machine-readable telemetry as a completed abstraction run.

set -u

if (($# == 1)) && [[ $1 == --version ]]; then
  printf '%s\n' 'STP benchmark harness fake solver 1'
  exit 0
fi

(($# > 0)) || exit 2
query=${!#}
[[ -f $query ]] || exit 2

# The harness creates an unmarked smoke query before the real population.
if ! grep -q '^; HARNESS_COST=1$' "$query"; then
  printf '%s\n' sat
  exit 0
fi

verdict=sat
grep -q '^; HARNESS_VERDICT=unsat$' "$query" && verdict=unsat

printf '%s\n' \
  'BV abstraction record: record=0 node=7 kind=BVMULT width=64 state=exact blocking=1 schemas=0 exact=1 exact-bits=64 allowance=1 paired=0 pair-full=0 blocking-clauses=64 blocking-literals=128 exact-clauses=123 exact-vars=45 exact-us=67' \
  'Abstraction coverage (candidates -> abstracted): eq=0->0 compare=0->0 ite=0->0 plus=0->0 mult=1->1 divmod=0->0' \
  'Abstraction refinement: rounds=2 blocking=1 schema=0 exact=1 exact-mult=1 exact-divmod=0' \
  'Abstraction escalation cost: clauses=123 variables=45 microseconds=67' \
  'Abstraction schemas by group: base=0' \
  "$verdict"
