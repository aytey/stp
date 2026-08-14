#!/usr/bin/env python3
"""Deterministic UFSTP differential campaign.

The generated corpus exercises nested applications, Bool/BV signatures,
define-fun specialization, let resolution, non-injectivity, interpreted
equalities, arrays-as-actuals, and guarded push/pop checks.  Every case is
run through both STP solve adapters and one or more independent SMT solvers.
Any unknown/error, timeout, or verdict disagreement is a hard failure.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
import time


VERDICT = re.compile(r"^(sat|unsat|unknown)$", re.MULTILINE)


def nested(term, depth):
    for _ in range(depth):
        term = "(g %s)" % term
    return term


def make_case(seed):
    width = 2 + seed % 7
    bv = "(_ BitVec %d)" % width
    zero = "#b" + "0" * width
    family = seed % 6
    logic = "QF_AUFBV" if family == 4 else "QF_UFBV"
    depth = 1 + (seed // 6) % 5
    gx = nested("x", depth)
    gy = nested("y", depth)

    lines = [
        "(set-logic %s)" % logic,
        "(declare-fun f (%s Bool) %s)" % (bv, bv),
        "(declare-fun g (%s) %s)" % (bv, bv),
        "(declare-fun p (%s Bool) Bool)" % bv,
        "(declare-const x %s)" % bv,
        "(declare-const y %s)" % bv,
        "(declare-const u %s)" % bv,
        "(declare-const v %s)" % bv,
        "(declare-const b Bool)",
        "(declare-const c Bool)",
        "(declare-const d Bool)",
        "(declare-const e Bool)",
        "(define-fun h ((z %s) (q Bool)) %s (f %s q))"
        % (bv, bv, nested("z", depth)),
    ]

    expected = "unsat"
    if family == 0:
        lines += [
            "(assert (= x y))",
            "(assert (= b c))",
            "(assert (distinct (let ((z x)) (h z b)) (h y c)))",
        ]
    elif family == 1:
        expected = "sat"
        lines += [
            "(assert (distinct x y))",
            "(assert (= b c))",
            "(assert (= (h x b) (h y c)))",
        ]
    elif family == 2:
        lines += [
            "(assert (= x y))",
            "(assert (= b c))",
            "(assert (p %s b))" % gx,
            "(assert (not (p %s c)))" % gy,
        ]
    elif family == 3:
        lines += [
            "(assert (distinct (f (bvadd x %s) b) (f x b)))" % zero,
        ]
    elif family == 4:
        lines += [
            "(declare-const a (Array %s %s))" % (bv, bv),
            "(declare-const i %s)" % bv,
            "(declare-const j %s)" % bv,
            "(assert (= i j))",
            "(assert (distinct (f (select a i) b) (f (select a j) b)))",
        ]
    else:
        expected = "sat"
        lines += [
            "(declare-fun q (%s Bool) %s)" % (bv, bv),
            "(assert (distinct (f x b) (q x b)))",
        ]

    # The pushed block has a fresh congruence conflict in every family. It is
    # then popped, so the third answer must recover the base verdict.
    lines += [
        "(check-sat)",
        "(push 1)",
        "(assert (= u v))",
        "(assert (= d e))",
        "(assert (distinct (f u d) (f v e)))",
        "(check-sat)",
        "(pop 1)",
        "(check-sat)",
        "(exit)",
    ]
    return "\n".join(lines) + "\n", [expected, "unsat", expected]


def reference_command(spec, path):
    name, command = spec.split("=", 1)
    argv = shlex.split(command)
    executable = os.path.basename(argv[0]).lower()
    if "cvc5" in executable:
        argv += ["--lang=smt2", "--incremental", str(path)]
    elif executable == "z3" or executable.startswith("z3-"):
        argv += ["-smt2", str(path)]
    else:
        argv.append(str(path))
    return name, argv


def stp_command(stp, specification, mode, path):
    name, flags = specification.split("=", 1)
    argv = [stp]
    argv += shlex.split(flags)
    argv += ["--uninterpreted-functions",
             "--incremental=" + ("on" if mode == "persistent" else "off"),
             str(path)]
    return "stp-%s-%s" % (name, mode), argv


def run(argv, timeout):
    started = time.monotonic()
    process = subprocess.run(argv, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True,
                             timeout=timeout, check=False)
    elapsed = time.monotonic() - started
    verdicts = VERDICT.findall(process.stdout)
    if process.returncode != 0:
        raise RuntimeError("command failed (%d): %s\n%s" %
                           (process.returncode, shlex.join(argv),
                            process.stdout))
    if "unknown" in verdicts:
        raise RuntimeError("solver returned unknown: %s\n%s" %
                           (shlex.join(argv), process.stdout))
    return verdicts, elapsed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stp", required=True)
    parser.add_argument(
        "--backend", action="append",
        help="NAME=STP_SOLVER_FLAG (repeatable; default is NAME=default)")
    parser.add_argument("--reference", action="append", required=True,
                        help="NAME=/path/to/solver (repeatable)")
    parser.add_argument("--seeds", type=int, default=240)
    parser.add_argument("--timeout", type=float, default=10.0)
    parser.add_argument("--evidence-out")
    parser.add_argument("--keep-corpus")
    args = parser.parse_args()
    if args.seeds <= 0:
        parser.error("--seeds must be positive")
    backends = args.backend or ["default="]
    if any("=" not in specification for specification in backends):
        parser.error("each --backend must be NAME=STP_SOLVER_FLAG")

    temporary = None
    if args.keep_corpus:
        corpus = Path(args.keep_corpus)
        corpus.mkdir(parents=True, exist_ok=True)
    else:
        temporary = tempfile.TemporaryDirectory(prefix="ufstp-fuzz-")
        corpus = Path(temporary.name)

    digest = hashlib.sha256()
    cases = []
    totals = {}
    for specification in backends:
        name = specification.split("=", 1)[0]
        totals["stp-%s-batch" % name] = 0.0
        totals["stp-%s-persistent" % name] = 0.0
    for specification in args.reference:
        totals[specification.split("=", 1)[0]] = 0.0

    for seed in range(args.seeds):
        text, expected = make_case(seed)
        digest.update(("case-%06d\0" % seed).encode())
        digest.update(text.encode())
        path = corpus / ("case-%06d.smt2" % seed)
        path.write_text(text)

        commands = []
        for specification in backends:
            commands.append(stp_command(args.stp, specification,
                                        "batch", path))
            commands.append(stp_command(args.stp, specification,
                                        "persistent", path))
        commands += [reference_command(specification, path)
                     for specification in args.reference]
        observed = {}
        for name, command in commands:
            verdicts, elapsed = run(command, args.timeout)
            totals[name] += elapsed
            observed[name] = verdicts
            if verdicts != expected:
                raise RuntimeError(
                    "seed %d disagreed for %s: expected %r, got %r" %
                    (seed, name, expected, verdicts))
        cases.append({"seed": seed, "expected": expected,
                      "observed": observed})

    evidence = {
        "schema": 1,
        "seed_count": args.seeds,
        "checks_per_seed": 3,
        "solver_runs": args.seeds * (2 * len(backends) +
                                      len(args.reference)),
        "stp_backends": [specification.split("=", 1)[0]
                         for specification in backends],
        "corpus_sha256": digest.hexdigest(),
        "families": ["nested-congruence", "noninjectivity",
                     "boolean-predicate", "interpreted-equality",
                     "array-actual", "declaration-separation"],
        "seconds_by_solver": {key: round(value, 6)
                              for key, value in totals.items()},
        "result": "pass",
    }
    encoded = json.dumps(evidence, sort_keys=True, indent=2) + "\n"
    if args.evidence_out:
        Path(args.evidence_out).write_text(encoded)
    print(encoded, end="")
    if temporary is not None:
        temporary.cleanup()


if __name__ == "__main__":
    main()
