#!/usr/bin/env python3
# AUTHORS: Andrew Teylu
#
# Time a solver over a corpus of SMT-LIB files and record the answers, so
# that two builds can be compared for both performance and soundness. Built
# for the incremental-solving work (docs/incremental-solving.rst): the
# same tool times incremental corpora (many check-sats per file) and guards
# the "batch performance must not regress" requirement on single-query files.
#
# Record a run:
#   scripts/incremental-bench.py --solver build/stp --out base.csv FILES...
# Compare a second run against it:
#   scripts/incremental-bench.py --solver build/stp --out new.csv \
#       --compare base.csv FILES...
#
# Answers are the sequence of sat/unsat/unknown lines the solver printed;
# a comparison flags any file whose sequence differs (a soundness alarm,
# not a perf number) and summarises the time deltas.

import argparse
import csv
import os
import subprocess
import sys
import time


def run_one(solver, extra_args, path, timeout):
    argv = [solver] + extra_args + [path]
    start = time.monotonic()
    try:
        proc = subprocess.run(
            argv,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=timeout,
        )
        elapsed = time.monotonic() - start
        answers = [
            line
            for line in proc.stdout.decode("utf-8", "replace").splitlines()
            if line in ("sat", "unsat", "unknown")
        ]
        status = "ok" if proc.returncode == 0 else "exit%d" % proc.returncode
        return status, elapsed, ";".join(answers)
    except subprocess.TimeoutExpired:
        return "timeout", timeout, ""


def collect_files(paths):
    out = []
    for p in paths:
        if os.path.isdir(p):
            for root, _, names in os.walk(p):
                out.extend(
                    os.path.join(root, n)
                    for n in names
                    if n.endswith((".smt2", ".cvc"))
                )
        else:
            out.append(p)
    return sorted(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--solver", required=True)
    ap.add_argument("--arg", action="append", default=[], dest="extra_args",
                    help="extra solver argument (repeatable)")
    ap.add_argument("--timeout", type=float, default=60.0)
    ap.add_argument("--out", help="CSV to write: file,status,seconds,answers")
    ap.add_argument("--compare", help="CSV from a previous run to diff against")
    ap.add_argument("files", nargs="+")
    args = ap.parse_args()

    baseline = {}
    if args.compare:
        with open(args.compare, newline="") as f:
            for row in csv.DictReader(f):
                baseline[row["file"]] = row

    rows = []
    mismatches = 0
    base_total = new_total = 0.0
    compared = 0
    for path in collect_files(args.files):
        status, secs, answers = run_one(
            args.solver, args.extra_args, path, args.timeout
        )
        rows.append(
            {"file": path, "status": status,
             "seconds": "%.3f" % secs, "answers": answers}
        )
        line = "%-8s %8.3fs  %s" % (status, secs, path)
        old = baseline.get(path)
        if old is not None and status == "ok" and old["status"] == "ok":
            compared += 1
            base_total += float(old["seconds"])
            new_total += secs
            if old["answers"] != answers:
                mismatches += 1
                line += "  ANSWERS DIFFER (was: %s)" % old["answers"]
        print(line, flush=True)

    if args.out:
        with open(args.out, "w", newline="") as f:
            w = csv.DictWriter(
                f, fieldnames=["file", "status", "seconds", "answers"]
            )
            w.writeheader()
            w.writerows(rows)

    if args.compare and compared:
        print(
            "\ncompared %d files: baseline %.1fs -> now %.1fs (%+.1f%%), "
            "%d answer mismatches"
            % (
                compared,
                base_total,
                new_total,
                100.0 * (new_total - base_total) / base_total
                if base_total else 0.0,
                mismatches,
            )
        )
        if mismatches:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
