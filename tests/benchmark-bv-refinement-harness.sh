#!/usr/bin/env bash

# End-to-end contract tests for scripts/benchmark-bv-refinement.sh. These use
# a fake solver so failures identify harness parsing and identity bugs rather
# than SAT-search drift.

set -eu
set -o pipefail
export LC_ALL=C

harness=${1:?benchmark harness required}
solver=${2:?fake solver required}
harness=$(cd "$(dirname "$harness")" && pwd -P)/$(basename "$harness")
solver=$(cd "$(dirname "$solver")" && pwd -P)/$(basename "$solver")
[[ -x $harness ]] || { printf 'not executable: %s\n' "$harness" >&2; exit 1; }
[[ -x $solver ]] || { printf 'not executable: %s\n' "$solver" >&2; exit 1; }

scratch=$(mktemp -d "${TMPDIR:-/tmp}/stp-bv-harness-test.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT HUP INT TERM

fail()
{
  printf 'benchmark harness regression: %s\n' "$*" >&2
  exit 1
}

mkdir -p "$scratch/first" "$scratch/second" "$scratch/manifests" \
  "$scratch/caller"
printf '%s\n' '; HARNESS_COST=1' '; HARNESS_VERDICT=sat' \
  '(set-logic QF_BV)' '(check-sat)' > "$scratch/first/query.smt2"
printf '%s\n' '; HARNESS_COST=1' '; HARNESS_VERDICT=unsat' \
  '(set-logic QF_BV)' '(assert false)' '(check-sat)' \
  > "$scratch/second/query.smt2"

# Relative to the manifest, not the caller. Include CRLF, a comment and blank
# line, and deliberately omit the final newline while selecting two equal
# basenames from different families.
printf '# selected population\r\n\r\n../first/query.smt2\r\n../second/query.smt2' \
  > "$scratch/manifests/population.txt"

run_log=$scratch/run.log
if ! (cd "$scratch/caller" && "$harness" \
       --solver "$solver" \
       --list "$scratch/manifests/population.txt" \
       --output "$scratch/results" --backend default \
       --variant reference: --variant candidate:) > "$run_log" 2>&1; then
  sed -n '1,200p' "$run_log" >&2
  fail 'valid relative manifest failed'
fi

runs=$scratch/results/runs.tsv
records=$scratch/results/records.tsv
summary=$scratch/results/summary.tsv
comparisons=$scratch/results/comparisons.tsv
disagreements=$scratch/results/disagreements.tsv

[[ $(awk 'END { print NR - 1 }' "$runs") == 4 ]] ||
  fail 'expected four blocked runs'
[[ $(awk 'END { print NR - 1 }' "$records") == 4 ]] ||
  fail 'expected one record from every run'
[[ $(awk 'END { print NR - 1 }' "$comparisons") == 2 ]] ||
  fail 'equal basenames collapsed in the matched comparison'
[[ $(awk 'END { print NR }' "$disagreements") == 1 ]] ||
  fail 'equal basenames fabricated an answer disagreement'

awk -F '\t' -v first="$scratch/first/query.smt2" \
  -v second="$scratch/second/query.smt2" '
  NR == 1 { next }
  $6 != first && $6 != second { bad=1 }
  { query[$6]=1; variant[$3]=1 }
  END {
    nq=0; nv=0
    for (q in query) ++nq
    for (v in variant) ++nv
    exit bad || nq != 2 || nv != 2 || !("reference" in variant) ||
         !("candidate" in variant)
  }' "$runs" || fail 'manifest paths or custom variant names were not preserved'

# The global line and the sum of record lines describe the same encode. Pin
# both the separate-line parser and every output-column position.
awk -F '\t' '
  NF != 34 { bad=1 }
  NR == 1 { next }
  $28 != 123 || $29 != 45 || $30 != 67 ||
  $28 != $31 || $29 != $32 || $30 != $33 { bad=1 }
  END { exit bad }
  ' "$runs" || fail 'aggregate exact cost does not match per-record cost'
awk -F '\t' '
  NF != 23 { bad=1 }
  NR == 1 { next }
  $18 != $21 || $19 != $22 || $20 != $23 { bad=1 }
  END { exit bad }
  ' "$summary" || fail 'summary lost aggregate/per-record cost consistency'

expect_rejected()
{
  label=$1
  message=$2
  shift 2
  log=$scratch/rejected-$label.log
  set +e
  (cd "$scratch/caller" && "$harness" --solver "$solver" \
     --list "$scratch/manifests/population.txt" --backend default \
     --variant custom: "$@") > "$log" 2>&1
  rc=$?
  set -e
  [[ $rc == 2 ]] || fail "$label returned $rc instead of rejecting the request"
  grep -F -- "$message" "$log" >/dev/null ||
    fail "$label did not explain the option conflict"
}

expect_rejected profiles '--variant and --profiles are mutually exclusive' \
  --profiles qualified
expect_rejected limits '--variant and --limits are mutually exclusive' \
  --limits 4
expect_rejected width '--variant does not imply --width' --width 53
expect_rejected exact-control \
  '--variant cannot be combined with built-in control switches' \
  --no-exact-control
expect_rejected v4-control \
  '--variant cannot be combined with built-in control switches' \
  --no-v4-control

printf '%s\n' 'benchmark harness regression passed'
