#!/usr/bin/env bash
# Compare named STP configurations over a directory of standalone SMT-LIB2
# queries, and report where the time went rather than only how much there was.
#
# Runs are blocked by (repetition, query) with the variant order rotated
# inside each block, so machine drift does not systematically favour whichever
# configuration happens to be measured first. Every run is written out
# individually; the summary is derived from those records and can be re-derived
# from them without re-running anything.
#
# What it collects per run, beyond wall time:
#
#   rounds     refinement passes that installed something
#   blocking   value-pair lemmas: one pair of operands ruled out
#   schema     algebraic lemmas: a fact about every pair
#   exact      refinements that gave up and encoded the operation exactly
#   eclauses   what those exact encodings cost
#
# The last one is the point. Rounds and lemmas measure how hard the
# abstraction worked; escalations measure how often it failed, and a
# configuration that looks busy and a configuration that is winning are
# distinguishable only by that column.
#
#   compare-bv-abstraction.sh --corpus DIR \
#       --variant off:'' \
#       --variant on:'--bv-term-abstraction=1 --bv-eq-abstraction=1' \
#       -- --cnf-auto-threshold=0
#
# A variant is NAME:FLAGS. Flags after `--` are passed to every variant, which
# is where the ones that are not under test belong -- a difference in those is
# a different experiment, not a different variant.

set -u
set -o pipefail
export LC_ALL=C

die() { printf '%s\n' "$*" >&2; exit 1; }

usage()
{
  cat <<'EOF'
Usage: compare-bv-abstraction.sh --corpus DIR [options] [-- COMMON_STP_ARG ...]

Required (one of):
  --corpus DIR         directory of *.smt2 queries (searched one level deep)
  --list FILE          file of query paths, one per line -- for a population
                       selected by some means other than living in a directory

Required:
  --variant NAME:FLAGS one configuration to measure; repeatable, order kept

Options:
  --solver PATH        STP executable (default: ../build/stp beside this script)
  --output DIR         where records go (default: a fresh directory in $TMPDIR)
  --repetitions N      complete blocked repetitions (default: 1)
  --timeout SECONDS    per-query wall-clock cap (default: 20)
  --split-fp           report queries containing `fp.` separately from the rest
  --help               this text

Exit status is 0 unless a variant disagreed with another on some query, which
is a correctness result and is reported as one.
EOF
}

solver=""
corpus=""
list=""
output=""
repetitions=1
timeout_s=20
split_fp=0
variant_names=()
variant_flags=()
common=()

while (($#)); do
  case "$1" in
    --solver) solver=${2:?}; shift 2;;
    --corpus) corpus=${2:?}; shift 2;;
    --list) list=${2:?}; shift 2;;
    --output) output=${2:?}; shift 2;;
    --repetitions) repetitions=${2:?}; shift 2;;
    --timeout) timeout_s=${2:?}; shift 2;;
    --split-fp) split_fp=1; shift;;
    --variant)
      spec=${2:?}
      [[ $spec == *:* ]] || die "--variant wants NAME:FLAGS, got '$spec'"
      variant_names+=("${spec%%:*}")
      variant_flags+=("${spec#*:}")
      shift 2;;
    --help) usage; exit 0;;
    --) shift; common=("$@"); break;;
    *) die "unknown option '$1'; --help for usage";;
  esac
done

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
[ -n "$solver" ] || solver="$here/../build/stp"
[ -x "$solver" ] || die "not executable: $solver"
if [ -n "$list" ]; then
  [ -f "$list" ] || die "not a file: $list"
  [ -z "$corpus" ] || die "--corpus and --list are alternatives"
else
  [ -n "$corpus" ] || die "one of --corpus or --list is required"
  [ -d "$corpus" ] || die "not a directory: $corpus"
fi
((${#variant_names[@]} > 0)) || die "at least one --variant is required"

if [ -z "$output" ]; then
  output=$(mktemp -d "${TMPDIR:-/tmp}/stp-compare.XXXXXX")
else
  mkdir -p "$output" || die "cannot create $output"
fi

if [ -n "$list" ]; then
  mapfile -t queries < <(grep -v '^[[:space:]]*$' "$list")
  ((${#queries[@]} > 0)) || die "no paths in $list"
else
  mapfile -d '' queries < <(find -L "$corpus" -maxdepth 1 -type f -name '*.smt2' -print0 | sort -z)
  ((${#queries[@]} > 0)) || die "no *.smt2 files in $corpus"
fi

records="$output/runs.tsv"
: > "$records"

# Provenance, so a summary found later can be tied to what produced it.
{
  printf 'solver\t%s\n' "$solver"
  printf 'solver_sha256\t%s\n' "$(sha256sum "$solver" | cut -d' ' -f1)"
  printf 'corpus\t%s\n' "${corpus:-list:$list}"
  printf 'queries\t%d\n' "${#queries[@]}"
  printf 'repetitions\t%d\n' "$repetitions"
  printf 'timeout\t%d\n' "$timeout_s"
  printf 'common\t%s\n' "${common[*]-}"
  for i in "${!variant_names[@]}"; do
    printf 'variant\t%s\t%s\n' "${variant_names[i]}" "${variant_flags[i]}"
  done
} > "$output/run.meta"

printf 'variant\trep\tverdict\tseconds\trounds\tblocking\tschema\texact\teclauses\tquery\n' >> "$records"

nvariants=${#variant_names[@]}
total=$((repetitions * ${#queries[@]} * nvariants))
done_runs=0

for ((rep = 0; rep < repetitions; ++rep)); do
  for ((qi = 0; qi < ${#queries[@]}; ++qi)); do
    query=${queries[qi]}
    # Rotate the variant order per block: with a fixed order, a machine that
    # slows over the run makes the last variant look worst every time.
    for ((k = 0; k < nvariants; ++k)); do
      vi=$(( (k + qi + rep) % nvariants ))
      name=${variant_names[vi]}
      # shellcheck disable=SC2206
      flags=(${variant_flags[vi]})

      start=$(date +%s.%N)
      out=$(timeout -s KILL "$timeout_s" "$solver" --SMTLIB2 -t \
              "${common[@]}" "${flags[@]}" "$query" 2>&1) || true
      finish=$(date +%s.%N)

      verdict=$(printf '%s\n' "$out" | grep -xE 'sat|unsat' | head -1)
      [ -n "$verdict" ] || verdict=none

      ref=$(printf '%s\n' "$out" | grep -oE 'rounds=[0-9]+ blocking=[0-9]+ schema=[0-9]+' | head -1)
      esc=$(printf '%s\n' "$out" | grep -oE 'exact=[0-9]+ mult=[0-9]+ divmod=[0-9]+ clauses=[0-9]+' | head -1)
      pick() { printf '%s\n' "$2" | grep -oE "$1=[0-9]+" | head -1 | cut -d= -f2; }

      printf '%s\t%d\t%s\t%.3f\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$name" "$rep" "$verdict" "$(echo "$finish - $start" | bc)" \
        "$(pick rounds "$ref")" "$(pick blocking "$ref")" "$(pick schema "$ref")" \
        "$(pick exact "$esc")" "$(pick clauses "$esc")" \
        "$query" >> "$records"

      done_runs=$((done_runs + 1))
      # Only when someone is watching: piped into a file this is one very
      # long line of carriage returns.
      [ -t 2 ] && printf '\r  %d/%d runs' "$done_runs" "$total" >&2
    done
  done
done
[ -t 2 ] && printf '\r%*s\r' 24 '' >&2

FP_SPLIT=$split_fp CORPUS=$corpus python3 - "$records" <<'PY'
import collections, os, statistics, sys

rows = []
with open(sys.argv[1]) as fh:
    header = fh.readline().rstrip('\n').split('\t')
    for line in fh:
        rows.append(dict(zip(header, line.rstrip('\n').split('\t'))))

split = os.environ.get('FP_SPLIT') == '1'
corpus = os.environ.get('CORPUS', '')
isfp = {}
if split:
    for r in rows:
        q = r['query']
        if q not in isfp:
            with open(q if os.path.isabs(q) else os.path.join(corpus, q)) as fh:
                isfp[q] = 'fp.' in fh.read()

variants = list(dict.fromkeys(r['variant'] for r in rows))
by = collections.defaultdict(dict)
for r in rows:
    by[(r['query'], r['variant'])].setdefault('runs', []).append(r)

def median_seconds(query, variant):
    rs = by[(query, variant)]['runs']
    return statistics.median(float(r['seconds']) for r in rs)

def solved(query, variant):
    return all(r['verdict'] in ('sat', 'unsat') for r in by[(query, variant)]['runs'])

queries = list(dict.fromkeys(r['query'] for r in rows))

# A disagreement is a correctness result and outranks every timing here.
disagree = []
for q in queries:
    verdicts = {r['verdict'] for v in variants for r in by[(q, v)]['runs']} - {'none'}
    if len(verdicts) > 1:
        disagree.append(q)

groups = [('all', queries)]
if split:
    groups = [('floating-point', [q for q in queries if isfp[q]]),
              ('bit-vector', [q for q in queries if not isfp[q]])]

for label, qs in groups:
    if not qs:
        continue
    common_qs = [q for q in qs if all(solved(q, v) for v in variants)]
    print(f'\n{label}: {len(qs)} queries, {len(common_qs)} solved by every variant')
    head = f"  {'variant':<22}{'solved':>7}{'median':>9}{'total':>9}" \
           f"{'rounds':>9}{'blocking':>10}{'schema':>9}{'exact':>7}{'eclauses':>10}"
    print(head)
    print('  ' + '-' * (len(head) - 2))
    for v in variants:
        n = sum(1 for q in qs if solved(q, v))
        times = [median_seconds(q, v) for q in common_qs]
        def tot(col):
            return sum(int(by[(q, v)]['runs'][0][col] or 0) for q in common_qs)
        print(f'  {v:<22}{n:>7}'
              f'{statistics.median(times) if times else 0:>8.3f}s'
              f'{sum(times):>8.2f}s'
              f'{tot("rounds"):>9}{tot("blocking"):>10}{tot("schema"):>9}'
              f'{tot("exact"):>7}{tot("eclauses"):>10}')

if disagree:
    print(f'\n  ANSWER DISAGREEMENT on {len(disagree)} queries -- '
          f'a correctness result, not a speed one:')
    for q in disagree[:10]:
        print(f'    {q}')
    sys.exit(1)
PY
status=$?
printf '\n  records: %s\n' "$records"
exit $status
