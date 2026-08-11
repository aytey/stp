#!/usr/bin/env python3
# AUTHORS: Andrew Teylu
"""Run and compare STP builds on incremental SMT-LIB corpora.

The original single-solver interface remains available::

  incremental-bench.py --solver build/stp --out base.csv FILES...
  incremental-bench.py --solver build/stp --compare base.csv \
      --out candidate.csv FILES...

For campaign work, paired mode runs two explicit solver binaries back to back.
The first arm alternates by file and run, avoiding a permanent warm-cache bias::

  incremental-bench.py --solver-a master/stp --solver-b branch/stp \
      --arg=--array-equality --runs 3 --out campaign.csv CORPUS

Every sat/unsat/unknown answer is retained, including output produced before a
timeout.  Comparisons have three deliberately narrow outcomes:

* FULL_OK: both processes completed successfully with identical sequences.
* PREFIX_ONLY_INCONCLUSIVE: the common prefix agrees, but at least one process
  did not complete successfully.  This is not a correctness success.
* DISAGREEMENT: an answer in the common prefix differs, or two completed
  processes produced sequences of different lengths.

Paired output is flushed after every complete pair.  ``--resume`` skips those
pairs, while ``--manifest`` and ``--shard-index``/``--shard-count`` make a
campaign reproducibly chunkable.  Metadata and the resolved manifest live
beside the CSV.  Outliers are revalidated automatically unless
``--defer-revalidation`` is given.
"""

import argparse
import csv
import datetime
import hashlib
import json
import os
import platform
import re
import shutil
import socket
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass


FULL_OK = "FULL_OK"
PREFIX_ONLY_INCONCLUSIVE = "PREFIX_ONLY_INCONCLUSIVE"
DISAGREEMENT = "DISAGREEMENT"
ANSWER_WORDS = ("sat", "unsat", "unknown")
SCHEMA_VERSION = 2
# STP's own model check: construct the counterexample of a sat answer and
# evaluate the raw assertions against it. A wrong sat fails here even though
# its answer stream looks self-consistent, which is the whole reason paired
# mode turns it on for the candidate by default.
CHECK_MODELS_ARG = "--check-sanity"

PAIRED_FIELDS = [
    "file", "run", "order", "verdict",
    "a_status", "a_seconds", "a_answers", "a_returncode",
    "b_status", "b_seconds", "b_answers", "b_returncode",
]
LEGACY_FIELDS = [
    "file", "status", "seconds", "answers", "returncode", "comparison",
]


@dataclass(frozen=True)
class RunResult:
    status: str
    seconds: float
    answers: tuple
    returncode: object = None


@dataclass(frozen=True)
class SolverSpec:
    label: str
    path: str
    arguments: tuple


def parse_answers(output):
    """Extract complete SMT-LIB answer lines from bytes or text output."""
    if output is None:
        return tuple()
    if isinstance(output, bytes):
        output = output.decode("utf-8", "replace")
    return tuple(
        line.strip()
        for line in output.splitlines()
        if line.strip() in ANSWER_WORDS
    )


def answers_text(answers):
    return ";".join(answers)


def answers_from_text(value):
    if not value:
        return tuple()
    return tuple(value.split(";"))


def run_one(solver, extra_args, path, timeout):
    """Run one solver, preserving the answer prefix on timeout."""
    argv = [solver] + list(extra_args) + [path]
    start = time.monotonic()
    try:
        proc = subprocess.run(
            argv,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=timeout,
        )
        elapsed = time.monotonic() - start
        status = "ok" if proc.returncode == 0 else "exit%d" % proc.returncode
        return RunResult(
            status, elapsed, parse_answers(proc.stdout), proc.returncode
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = time.monotonic() - start
        return RunResult("timeout", elapsed, parse_answers(exc.stdout), None)
    except OSError:
        elapsed = time.monotonic() - start
        return RunResult("exec-error", elapsed, tuple(), None)


def compare_results(first, second):
    """Classify two results without treating a matching prefix as proof."""
    shared = min(len(first.answers), len(second.answers))
    if first.answers[:shared] != second.answers[:shared]:
        return DISAGREEMENT
    if first.status == "ok" and second.status == "ok":
        if first.answers == second.answers:
            return FULL_OK
        return DISAGREEMENT
    # A failed/truncated process may simply not have reached all of the
    # completed process's answers.  It cannot, however, legitimately have
    # produced answers beyond the completed process's final sequence.
    if first.status == "ok" and len(second.answers) > len(first.answers):
        return DISAGREEMENT
    if second.status == "ok" and len(first.answers) > len(second.answers):
        return DISAGREEMENT
    return PREFIX_ONLY_INCONCLUSIVE


def collect_files(paths):
    out = []
    for path in paths:
        if os.path.isdir(path):
            for root, directories, names in os.walk(path):
                directories.sort()
                out.extend(
                    os.path.join(root, name)
                    for name in sorted(names)
                    if name.endswith((".smt2", ".cvc"))
                )
        else:
            out.append(path)
    return out


def load_manifest(path):
    result = []
    base = os.path.dirname(os.path.abspath(path))
    with open(path, encoding="utf-8") as source:
        for line in source:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if not os.path.isabs(line):
                line = os.path.join(base, line)
            result.append(line)
    return result


def resolve_files(paths, manifest, shard_index, shard_count):
    inputs = list(paths)
    if manifest:
        inputs.extend(load_manifest(manifest))
    files = sorted(set(os.path.abspath(path) for path in collect_files(inputs)))
    missing = [path for path in files if not os.path.isfile(path)]
    if missing:
        sample = "\n  ".join(missing[:5])
        raise ValueError("manifest contains missing files:\n  " + sample)
    if shard_count is None:
        if shard_index != 0:
            raise ValueError("--shard-index requires --shard-count")
        return files
    if shard_count <= 0:
        raise ValueError("--shard-count must be positive")
    if shard_index < 0 or shard_index >= shard_count:
        raise ValueError("--shard-index must be in [0, shard-count)")
    return files[shard_index::shard_count]


def digest_lines(lines):
    digest = hashlib.sha256()
    for line in lines:
        digest.update(line.encode("utf-8"))
        digest.update(b"\n")
    return digest.hexdigest()


def file_sha256(path):
    digest = hashlib.sha256()
    try:
        with open(path, "rb") as source:
            while True:
                block = source.read(1024 * 1024)
                if not block:
                    break
                digest.update(block)
    except OSError:
        return None
    return digest.hexdigest()


def capture_command(argv, timeout):
    try:
        proc = subprocess.run(
            argv,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            text=True,
        )
        return proc.returncode, proc.stdout.strip()
    except (OSError, subprocess.TimeoutExpired) as exc:
        output = getattr(exc, "stdout", "") or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", "replace")
        return None, output.strip()


def parse_version_output(output):
    embedded_sha = None
    compilation_options = None
    for line in output.splitlines():
        match = re.match(r"STP version SHA string\s+(.+)$", line)
        if match:
            embedded_sha = match.group(1).strip()
        match = re.match(r"STP compilation options\s+(.+)$", line)
        if match:
            compilation_options = match.group(1).strip()
    return embedded_sha, compilation_options


def linked_stp_libraries(ldd_output):
    """Hash dynamic libstp targets, since the executable alone is not an arm."""
    libraries = []
    for line in (ldd_output or "").splitlines():
        match = re.search(r"=>\s+(/\S+)\s+\(", line)
        if not match:
            match = re.match(r"\s*(/\S+)\s+\(", line)
        if not match:
            continue
        path = match.group(1)
        if not os.path.basename(path).startswith("libstp"):
            continue
        realpath = os.path.realpath(path)
        libraries.append({
            "path": path,
            "realpath": realpath,
            "sha256": file_sha256(realpath),
        })
    return libraries


def inspect_solver(spec, version_timeout):
    realpath = os.path.realpath(spec.path)
    if not os.path.isfile(realpath):
        raise ValueError("solver binary does not exist: " + spec.path)
    version_code, version_output = capture_command(
        [spec.path, "--version"], version_timeout
    )
    embedded_sha, compilation_options = parse_version_output(version_output)
    dependencies = None
    if sys.platform.startswith("linux") and shutil.which("ldd"):
        _, dependencies = capture_command(["ldd", realpath], version_timeout)
    return {
        "label": spec.label,
        "binary": spec.path,
        "binary_realpath": realpath,
        "binary_sha256": file_sha256(realpath),
        "arguments": list(spec.arguments),
        "version_returncode": version_code,
        "version_output": version_output,
        "embedded_sha": embedded_sha,
        "compilation_options": compilation_options,
        "dynamic_dependencies": dependencies,
        "linked_stp_libraries": linked_stp_libraries(dependencies),
    }


def metadata_identity(metadata):
    solver_identity = {}
    for name, solver in metadata.get("solvers", {}).items():
        solver_identity[name] = {
            key: solver.get(key)
            for key in (
                "label", "binary_realpath", "binary_sha256", "arguments",
                "embedded_sha", "compilation_options",
                "linked_stp_libraries",
            )
        }
    return {
        "schema_version": metadata.get("schema_version"),
        "mode": metadata.get("mode"),
        "phase": metadata.get("phase"),
        "timeout_seconds": metadata.get("timeout_seconds"),
        "runs": metadata.get("runs"),
        "manifest_sha256": metadata.get("manifest_sha256"),
        "solvers": solver_identity,
    }


def ensure_solvers_unchanged(expected, specs, version_timeout):
    current = {
        name: inspect_solver(spec, version_timeout)
        for name, spec in specs.items()
    }
    expected_identity = metadata_identity({"solvers": expected})["solvers"]
    current_identity = metadata_identity({"solvers": current})["solvers"]
    if current_identity != expected_identity:
        raise ValueError("a solver binary or linked libstp changed during the run")


def write_metadata(path, metadata, resume):
    if resume and os.path.exists(path):
        with open(path, encoding="utf-8") as source:
            previous = json.load(source)
        if metadata_identity(previous) != metadata_identity(metadata):
            raise ValueError("resume metadata does not match " + path)
        return
    temporary = path + ".tmp"
    with open(temporary, "w", encoding="utf-8") as target:
        json.dump(metadata, target, indent=2, sort_keys=True)
        target.write("\n")
    os.replace(temporary, path)


def write_manifest(path, files, resume):
    content = "".join(file_path + "\n" for file_path in files)
    if resume and os.path.exists(path):
        with open(path, encoding="utf-8") as source:
            if source.read() != content:
                raise ValueError("resume manifest does not match " + path)
        return
    temporary = path + ".tmp"
    with open(temporary, "w", encoding="utf-8") as target:
        target.write(content)
    os.replace(temporary, path)


def require_resume_provenance(output, resume):
    """Never append to an existing result file with no identity sidecars."""
    if not resume or not os.path.exists(output):
        return
    missing = [
        path for path in (output + ".manifest", output + ".meta.json")
        if not os.path.exists(path)
    ]
    if missing:
        raise ValueError(
            "cannot safely resume %s; missing %s"
            % (output, ", ".join(missing))
        )


def make_metadata(mode, phase, timeout, runs, files, solvers, argv, extra=None):
    metadata = {
        "schema_version": SCHEMA_VERSION,
        "mode": mode,
        "phase": phase,
        "created_utc": datetime.datetime.now(
            datetime.timezone.utc
        ).isoformat(),
        "hostname": socket.gethostname(),
        "platform": platform.platform(),
        "python": sys.version,
        "working_directory": os.getcwd(),
        "command": list(argv),
        "timeout_seconds": timeout,
        "runs": runs,
        "file_count": len(files),
        "manifest_sha256": digest_lines(files),
        "solvers": solvers,
    }
    if extra:
        metadata.update(extra)
    return metadata


def result_from_pair_row(row, prefix):
    code = row.get(prefix + "_returncode", "")
    return RunResult(
        row[prefix + "_status"],
        float(row[prefix + "_seconds"]),
        answers_from_text(row[prefix + "_answers"]),
        int(code) if code not in ("", None) else None,
    )


def result_from_legacy_row(row):
    code = row.get("returncode", "")
    return RunResult(
        row["status"],
        float(row["seconds"]),
        answers_from_text(row.get("answers", "")),
        int(code) if code not in ("", None) else None,
    )


def read_csv_rows(path, required_fields):
    if not os.path.exists(path):
        return []
    if os.path.getsize(path) == 0:
        return []
    with open(path, newline="", encoding="utf-8") as source:
        reader = csv.DictReader(source)
        fields = set(reader.fieldnames or [])
        missing = set(required_fields) - fields
        if missing:
            raise ValueError(
                "%s is missing CSV fields: %s"
                % (path, ", ".join(sorted(missing)))
            )
        return list(reader)


def pair_order(path, run):
    parity = hashlib.sha256(path.encode("utf-8")).digest()[0] & 1
    return "AB" if (parity + run) % 2 == 0 else "BA"


def paired_row(path, run, order, first, second):
    verdict = compare_results(first, second)
    return {
        "file": path,
        "run": str(run),
        "order": order,
        "verdict": verdict,
        "a_status": first.status,
        "a_seconds": "%.6f" % first.seconds,
        "a_answers": answers_text(first.answers),
        "a_returncode": "" if first.returncode is None else str(first.returncode),
        "b_status": second.status,
        "b_seconds": "%.6f" % second.seconds,
        "b_answers": answers_text(second.answers),
        "b_returncode": "" if second.returncode is None else str(second.returncode),
    }


def open_csv_output(path, fields, resume):
    exists = os.path.exists(path) and os.path.getsize(path) > 0
    mode = "a" if resume and exists else "w"
    target = open(path, mode, newline="", encoding="utf-8")
    writer = csv.DictWriter(target, fieldnames=fields)
    if mode == "w":
        writer.writeheader()
        target.flush()
    return target, writer


def run_paired_campaign(files, first_spec, second_spec, timeout, runs,
                        output, resume):
    previous = read_csv_rows(output, PAIRED_FIELDS) if resume else []
    completed = {}
    for row in previous:
        key = (row["file"], int(row["run"]))
        if key in completed:
            raise ValueError("duplicate completed pair in %s: %r" % (output, key))
        completed[key] = row

    target, writer = open_csv_output(output, PAIRED_FIELDS, resume)
    skipped = 0
    try:
        for path in files:
            for run in range(runs):
                key = (path, run)
                if key in completed:
                    skipped += 1
                    continue
                order = pair_order(path, run)
                if order == "AB":
                    first = run_one(
                        first_spec.path, first_spec.arguments, path, timeout
                    )
                    second = run_one(
                        second_spec.path, second_spec.arguments, path, timeout
                    )
                else:
                    second = run_one(
                        second_spec.path, second_spec.arguments, path, timeout
                    )
                    first = run_one(
                        first_spec.path, first_spec.arguments, path, timeout
                    )
                row = paired_row(path, run, order, first, second)
                writer.writerow(row)
                target.flush()
                completed[key] = row
                print(
                    "%-26s A=%-8s %8.3fs B=%-8s %8.3fs run=%d %s %s"
                    % (
                        row["verdict"], first.status, first.seconds,
                        second.status, second.seconds, run, order, path,
                    ),
                    flush=True,
                )
    finally:
        target.close()

    rows = list(completed.values())
    counts = {FULL_OK: 0, PREFIX_ONLY_INCONCLUSIVE: 0, DISAGREEMENT: 0}
    for row in rows:
        counts[row["verdict"]] = counts.get(row["verdict"], 0) + 1
    print(
        "\npaired summary: %d pairs, %d resumed, %d %s, %d %s, %d %s"
        % (
            len(rows), skipped,
            counts[FULL_OK], FULL_OK,
            counts[PREFIX_ONLY_INCONCLUSIVE], PREFIX_ONLY_INCONCLUSIVE,
            counts[DISAGREEMENT], DISAGREEMENT,
        )
    )
    return rows, counts


def revalidation_files(rows, ratio_threshold):
    grouped = {}
    for row in rows:
        grouped.setdefault(row["file"], []).append(row)

    flagged = set()
    for path, file_rows in grouped.items():
        results = [
            (row, result_from_pair_row(row, "a"),
             result_from_pair_row(row, "b"))
            for row in file_rows
        ]
        if any(
            row["verdict"] != FULL_OK
            or first.status != "ok"
            or second.status != "ok"
            for row, first, second in results
        ):
            flagged.add(path)
            continue
        first_median = statistics.median(first.seconds for _, first, _ in results)
        second_median = statistics.median(second.seconds for _, _, second in results)
        low = max(min(first_median, second_median), 0.001)
        high = max(first_median, second_median)
        if high / low >= ratio_threshold:
            flagged.add(path)
    return sorted(flagged)


def write_revalidation_manifest(output, files):
    path = output + ".revalidate.manifest"
    write_manifest(path, files, False)
    return path


def revalidation_output_name(output):
    base, extension = os.path.splitext(output)
    return base + ".revalidation" + (extension or ".csv")


def run_paired_mode(args, files, argv):
    runs = args.runs if args.runs is not None else 3
    if runs <= 0:
        raise ValueError("--runs must be positive")
    common = tuple(args.extra_args)
    # Answer-sequence comparison alone is not a correctness gate. Both of the
    # soundness defects found in the incremental driver produced a wrong SAT
    # with a model that does not satisfy the asserted formulas, and a campaign
    # that only reads sat/unsat off stdout agrees with itself on every such
    # row. --check-sanity makes the candidate validate its own model against
    # the raw assertions and fail loudly instead, so it is on by default here
    # and has to be turned off deliberately -- which a timing campaign should
    # do, since model construction and validation are not free.
    candidate_args = tuple(args.args_b)
    if args.check_models and CHECK_MODELS_ARG not in candidate_args:
        candidate_args += (CHECK_MODELS_ARG,)
    first_spec = SolverSpec(
        args.label_a, args.solver_a, common + tuple(args.args_a)
    )
    second_spec = SolverSpec(
        args.label_b, args.solver_b, common + candidate_args
    )
    solver_metadata = {
        "a": inspect_solver(first_spec, args.version_timeout),
        "b": inspect_solver(second_spec, args.version_timeout),
    }
    metadata = make_metadata(
        "paired", "main", args.timeout, runs, files, solver_metadata, argv,
        {
            "shard_index": args.shard_index,
            "shard_count": args.shard_count,
            "revalidation_ratio": args.revalidation_ratio,
            "revalidation_deferred": args.defer_revalidation,
            "arm_order_policy": "sha256(file)-parity alternating by run",
            # Recorded so a report can state whether the candidate validated
            # its models, rather than leaving readers to infer it from the
            # command line: a campaign run without this is an answer-stream
            # comparison, not a correctness gate.
            "candidate_model_validation": bool(args.check_models),
        },
    )
    require_resume_provenance(args.out, args.resume)
    write_manifest(args.out + ".manifest", files, args.resume)
    write_metadata(args.out + ".meta.json", metadata, args.resume)
    rows, counts = run_paired_campaign(
        files, first_spec, second_spec, args.timeout, runs,
        args.out, args.resume,
    )
    ensure_solvers_unchanged(
        solver_metadata,
        {"a": first_spec, "b": second_spec},
        args.version_timeout,
    )

    flagged = revalidation_files(rows, args.revalidation_ratio)
    manifest_path = write_revalidation_manifest(args.out, flagged)
    print(
        "%d files require revalidation; manifest: %s"
        % (len(flagged), manifest_path)
    )

    final_counts = counts
    if flagged and not args.defer_revalidation:
        timeout = args.revalidation_timeout
        if timeout is None:
            timeout = max(args.timeout * 4.0, 120.0)
        output = args.revalidation_out or revalidation_output_name(args.out)
        reval_metadata = make_metadata(
            "paired", "revalidation", timeout, runs, flagged,
            solver_metadata, argv,
            {
                "source_output": os.path.abspath(args.out),
                "revalidation_ratio": args.revalidation_ratio,
                "arm_order_policy": "sha256(file)-parity alternating by run",
            },
        )
        require_resume_provenance(output, args.resume)
        write_manifest(output + ".manifest", flagged, args.resume)
        write_metadata(output + ".meta.json", reval_metadata, args.resume)
        _, final_counts = run_paired_campaign(
            flagged, first_spec, second_spec, timeout, runs,
            output, args.resume,
        )
        ensure_solvers_unchanged(
            solver_metadata,
            {"a": first_spec, "b": second_spec},
            args.version_timeout,
        )
    elif flagged:
        print("revalidation deferred")

    if counts.get(DISAGREEMENT, 0) or final_counts.get(DISAGREEMENT, 0):
        return 1
    return 0


def load_legacy_baseline(path):
    baseline = {}
    if not path:
        return baseline
    for row in read_csv_rows(path, ["file", "status", "seconds", "answers"]):
        baseline[row["file"]] = row
        baseline[os.path.abspath(row["file"])] = row
    return baseline


def run_legacy_mode(args, files, argv):
    runs = args.runs if args.runs is not None else 1
    if runs != 1:
        raise ValueError("--runs is available only in paired mode")
    spec = SolverSpec(args.label_b, args.solver, tuple(args.extra_args))
    baseline = load_legacy_baseline(args.compare)
    previous = read_csv_rows(args.out, LEGACY_FIELDS) if args.resume else []
    completed = {row["file"]: row for row in previous}

    if args.out:
        solver_metadata = {"solver": inspect_solver(spec, args.version_timeout)}
        extra = {"comparison_csv": os.path.abspath(args.compare) if args.compare else None}
        metadata = make_metadata(
            "single", "main", args.timeout, 1, files,
            solver_metadata, argv, extra,
        )
        require_resume_provenance(args.out, args.resume)
        write_manifest(args.out + ".manifest", files, args.resume)
        write_metadata(args.out + ".meta.json", metadata, args.resume)
        target, writer = open_csv_output(args.out, LEGACY_FIELDS, args.resume)
    else:
        target = writer = None

    counts = {FULL_OK: 0, PREFIX_ONLY_INCONCLUSIVE: 0, DISAGREEMENT: 0}
    for row in previous:
        verdict = row.get("comparison", "")
        if verdict in counts:
            counts[verdict] += 1
    base_total = new_total = 0.0
    compared = 0
    try:
        for path in files:
            if path in completed:
                continue
            result = run_one(spec.path, spec.arguments, path, args.timeout)
            verdict = ""
            old = baseline.get(path)
            if old is not None:
                previous_result = result_from_legacy_row(old)
                verdict = compare_results(previous_result, result)
                counts[verdict] += 1
                if previous_result.status == "ok" and result.status == "ok":
                    compared += 1
                    base_total += previous_result.seconds
                    new_total += result.seconds
            row = {
                "file": path,
                "status": result.status,
                "seconds": "%.6f" % result.seconds,
                "answers": answers_text(result.answers),
                "returncode": "" if result.returncode is None else str(result.returncode),
                "comparison": verdict,
            }
            if writer:
                writer.writerow(row)
                target.flush()
            suffix = "  " + verdict if verdict else ""
            print(
                "%-10s %8.3fs  %s%s"
                % (result.status, result.seconds, path, suffix),
                flush=True,
            )
    finally:
        if target:
            target.close()

    if args.out:
        ensure_solvers_unchanged(
            solver_metadata, {"solver": spec}, args.version_timeout
        )

    if args.compare:
        delta = (
            100.0 * (new_total - base_total) / base_total
            if base_total else 0.0
        )
        print(
            "\ncompared %d completed files: baseline %.1fs -> now %.1fs "
            "(%+.1f%%); %d %s, %d %s, %d %s"
            % (
                compared, base_total, new_total, delta,
                counts[FULL_OK], FULL_OK,
                counts[PREFIX_ONLY_INCONCLUSIVE], PREFIX_ONLY_INCONCLUSIVE,
                counts[DISAGREEMENT], DISAGREEMENT,
            )
        )
    return 1 if counts[DISAGREEMENT] else 0


def make_parser():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--solver", help="solver binary for single-solver mode")
    parser.add_argument("--solver-a", help="baseline solver binary for paired mode")
    parser.add_argument("--solver-b", help="candidate solver binary for paired mode")
    parser.add_argument("--label-a", default="baseline")
    parser.add_argument("--label-b", default="candidate")
    parser.add_argument(
        "--arg", action="append", default=[], dest="extra_args",
        help="common solver argument; repeat, using --arg=--flag for flags",
    )
    parser.add_argument(
        "--arg-a", action="append", default=[], dest="args_a",
        help="baseline-only solver argument (paired mode)",
    )
    parser.add_argument(
        "--arg-b", action="append", default=[], dest="args_b",
        help="candidate-only solver argument (paired mode)",
    )
    parser.add_argument(
        "--check-models", dest="check_models", action="store_true",
        default=True,
        help="validate the candidate's models against the raw assertions "
             "(adds %s; on by default in paired mode)" % CHECK_MODELS_ARG,
    )
    parser.add_argument(
        "--no-check-models", dest="check_models", action="store_false",
        help="do not validate the candidate's models; use for timing "
             "campaigns, where construction and checking are not free. A "
             "run with this set compares answer streams only.",
    )
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--runs", type=int)
    parser.add_argument("--out", help="CSV output path (required in paired mode)")
    parser.add_argument("--compare", help="single-mode CSV baseline")
    parser.add_argument("--manifest", help="input manifest, one path per line")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--shard-index", type=int, default=0)
    parser.add_argument("--shard-count", type=int)
    parser.add_argument(
        "--defer-revalidation", action="store_true",
        help="write the revalidation manifest but do not run it",
    )
    parser.add_argument("--revalidation-ratio", type=float, default=3.0)
    parser.add_argument("--revalidation-timeout", type=float)
    parser.add_argument("--revalidation-out")
    parser.add_argument("--version-timeout", type=float, default=5.0)
    parser.add_argument("files", nargs="*")
    return parser


def validate_arguments(parser, args):
    paired = bool(args.solver_a or args.solver_b)
    if paired:
        if not args.solver_a or not args.solver_b:
            parser.error("paired mode requires both --solver-a and --solver-b")
        if args.solver:
            parser.error("--solver cannot be combined with paired mode")
        if args.compare:
            parser.error("--compare belongs to single-solver mode")
        if not args.out:
            parser.error("paired mode requires --out")
    else:
        if not args.solver:
            parser.error("use --solver, or both --solver-a and --solver-b")
        if args.args_a or args.args_b:
            parser.error("--arg-a/--arg-b belong to paired mode")
        if args.defer_revalidation or args.revalidation_out:
            parser.error("revalidation options belong to paired mode")
    if not args.files and not args.manifest:
        parser.error("provide FILES/directories or --manifest")
    if args.resume and not args.out:
        parser.error("--resume requires --out")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.version_timeout <= 0:
        parser.error("--version-timeout must be positive")
    if args.revalidation_timeout is not None and args.revalidation_timeout <= 0:
        parser.error("--revalidation-timeout must be positive")
    if args.revalidation_ratio <= 1.0:
        parser.error("--revalidation-ratio must be greater than one")
    return paired


def main(argv=None):
    parser = make_parser()
    args = parser.parse_args(argv)
    paired = validate_arguments(parser, args)
    command = sys.argv if argv is None else [sys.argv[0]] + list(argv)
    try:
        files = resolve_files(
            args.files, args.manifest, args.shard_index, args.shard_count
        )
        if not files:
            raise ValueError("selected manifest/shard contains no files")
        if paired:
            return run_paired_mode(args, files, command)
        return run_legacy_mode(args, files, command)
    except KeyboardInterrupt:
        print("\ninterrupted; rerun with --resume", file=sys.stderr)
        return 130
    except ValueError as exc:
        parser.error(str(exc))
    return 2


if __name__ == "__main__":
    sys.exit(main())
