#!/usr/bin/env python3
# AUTHORS: Andrew Teylu
"""Validate, combine and report paired incremental-benchmark results.

Typical closeout usage::

  incremental-bench-report.py --main '/results/final/main-shard-*.csv'
      --revalidation '/results/final/revalidation-shard-*.csv'
      --expected-manifest /results/corpus.manifest --expected-runs 3
      --expected-answers 1865826
      --output-prefix /results/final/report --require-full-ok

Input globs may be quoted: this tool expands them itself.  Every input CSV must
have the schema-2 ``.meta.json`` and ``.manifest`` sidecars written by
``incremental-bench.py``.  Solver identities must agree across all shards and
phases, and ``(file, run)`` keys must be unique within each phase.

Revalidation is selected by its sidecar manifests, not by the rows that happen
to have completed.  All main rows for those files are replaced, exposing an
interrupted revalidation as missing work.  A disagreement observed in either
phase remains a sticky campaign failure.  With ``--output-prefix PREFIX`` the
tool writes:

* ``PREFIX.combined.csv``: effective rows, retaining complete answer streams;
* ``PREFIX.disagreements.csv``: every disagreement observation, including
  superseded main rows;
* ``PREFIX.files.csv``: per-file correctness and median timing data;
* ``PREFIX.summary.json`` and ``PREFIX.txt``: machine and human reports.

An observed disagreement always exits 1.  Supplying any expectation also
exits 1 for incomplete coverage; ``--require-full-ok`` additionally rejects
timeouts and other inconclusive effective rows.  Invalid inputs exit 2.
"""

import argparse
import collections
import csv
import datetime
import glob
import hashlib
import json
import math
import os
from pathlib import Path
import re
import statistics
import sys


SCHEMA_VERSION = 2
FULL_OK = "FULL_OK"
PREFIX_ONLY_INCONCLUSIVE = "PREFIX_ONLY_INCONCLUSIVE"
DISAGREEMENT = "DISAGREEMENT"
VERDICTS = (FULL_OK, PREFIX_ONLY_INCONCLUSIVE, DISAGREEMENT)
ANSWERS = ("sat", "unsat", "unknown")
PAIRED_FIELDS = [
    "file", "run", "order", "verdict",
    "a_status", "a_seconds", "a_answers", "a_returncode",
    "b_status", "b_seconds", "b_answers", "b_returncode",
]
SOLVER_IDENTITY_FIELDS = (
    "label", "binary_realpath", "binary_sha256", "arguments",
    "embedded_sha", "compilation_options", "linked_stp_libraries",
)
COMBINED_FIELDS = ["phase", "source_csv", "ever_disagreement"] + PAIRED_FIELDS
EVIDENCE_FIELDS = ["phase", "source_csv"] + PAIRED_FIELDS
FILE_FIELDS = [
    "file", "logic", "family", "effective_verdict", "ever_disagreement",
    "expected_runs", "completed_runs", "missing_runs", "effective_pairs",
    "full_ok_pairs", "inconclusive_pairs", "disagreement_pairs",
    "a_statuses", "b_statuses", "a_answers", "b_answers",
    "median_a_seconds", "median_b_seconds", "b_over_a", "classification",
    "timing_outlier",
]


class ReportError(ValueError):
    pass


def digest_lines(lines):
    digest = hashlib.sha256()
    for line in lines:
        digest.update(line.encode("utf-8"))
        digest.update(b"\n")
    return digest.hexdigest()


def read_manifest(path):
    base = os.path.dirname(os.path.abspath(path))
    files = []
    with open(path, encoding="utf-8") as source:
        for line in source:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            files.append(
                os.path.normpath(line if os.path.isabs(line)
                                 else os.path.join(base, line))
            )
    if len(files) != len(set(files)):
        raise ReportError("duplicate file in manifest: " + path)
    return files


def expand_inputs(values, option):
    paths = []
    for value in values or []:
        matches = sorted(glob.glob(value))
        if not matches and os.path.isfile(value):
            matches = [value]
        if not matches:
            raise ReportError("%s matched no files: %s" % (option, value))
        paths.extend(os.path.abspath(path) for path in matches)
    duplicates = [path for path, count in collections.Counter(paths).items()
                  if count > 1]
    if duplicates:
        raise ReportError("duplicate input CSV: " + duplicates[0])
    return paths


def solver_identity(metadata):
    solvers = metadata.get("solvers")
    if not isinstance(solvers, dict) or set(solvers) != {"a", "b"}:
        raise ReportError("metadata must describe paired solvers a and b")
    result = {}
    for arm in ("a", "b"):
        solver = solvers[arm]
        if not isinstance(solver, dict):
            raise ReportError("solver %s metadata is not an object" % arm)
        missing = [key for key in SOLVER_IDENTITY_FIELDS if key not in solver]
        if missing:
            raise ReportError(
                "solver %s metadata is missing %s"
                % (arm, ", ".join(missing))
            )
        result[arm] = {
            key: solver[key] for key in SOLVER_IDENTITY_FIELDS
        }
    return result


def parse_answers(value, source):
    if not value:
        return tuple()
    answers = tuple(value.split(";"))
    invalid = [answer for answer in answers if answer not in ANSWERS]
    if invalid:
        raise ReportError("invalid answer stream in %s: %r" % (source, value))
    return answers


def comparison(status_a, answers_a, status_b, answers_b):
    shared = min(len(answers_a), len(answers_b))
    if answers_a[:shared] != answers_b[:shared]:
        return DISAGREEMENT
    if status_a == "ok" and status_b == "ok":
        return FULL_OK if answers_a == answers_b else DISAGREEMENT
    if status_a == "ok" and len(answers_b) > len(answers_a):
        return DISAGREEMENT
    if status_b == "ok" and len(answers_a) > len(answers_b):
        return DISAGREEMENT
    return PREFIX_ONLY_INCONCLUSIVE


def validate_status(value, source):
    if value in ("ok", "timeout", "exec-error"):
        return
    if re.fullmatch(r"exit-?\d+", value or ""):
        return
    raise ReportError("invalid process status in %s: %r" % (source, value))


def validate_row(row, csv_path, line, manifest_files, runs):
    source = "%s:%d" % (csv_path, line)
    if None in row or any(row.get(field) is None for field in PAIRED_FIELDS):
        raise ReportError("malformed CSV row in " + source)
    path = os.path.normpath(row["file"])
    if path not in manifest_files:
        raise ReportError("row file is absent from its sidecar manifest: " + source)
    try:
        run = int(row["run"])
    except ValueError as exc:
        raise ReportError("invalid run number in " + source) from exc
    if str(run) != row["run"] or run < 0 or run >= runs:
        raise ReportError("run is outside metadata range in " + source)
    if row["order"] not in ("AB", "BA"):
        raise ReportError("invalid arm order in " + source)
    if row["verdict"] not in VERDICTS:
        raise ReportError("invalid verdict in " + source)

    parsed = {}
    for arm in ("a", "b"):
        validate_status(row[arm + "_status"], source)
        try:
            seconds = float(row[arm + "_seconds"])
        except ValueError as exc:
            raise ReportError("invalid timing in " + source) from exc
        if not math.isfinite(seconds) or seconds < 0:
            raise ReportError("invalid timing in " + source)
        returncode = row[arm + "_returncode"]
        if returncode:
            try:
                int(returncode)
            except ValueError as exc:
                raise ReportError("invalid return code in " + source) from exc
        parsed[arm] = {
            "seconds": seconds,
            "answers": parse_answers(row[arm + "_answers"], source),
        }

    expected = comparison(
        row["a_status"], parsed["a"]["answers"],
        row["b_status"], parsed["b"]["answers"],
    )
    if expected != row["verdict"]:
        raise ReportError(
            "stored verdict %s does not match answer streams (%s) in %s"
            % (row["verdict"], expected, source)
        )
    return {
        "key": (path, run),
        "path": path,
        "run": run,
        "row": dict(row),
        "parsed": parsed,
    }


def load_csv(csv_path, required_phase):
    metadata_path = csv_path + ".meta.json"
    manifest_path = csv_path + ".manifest"
    missing = [path for path in (metadata_path, manifest_path)
               if not os.path.isfile(path)]
    if missing:
        raise ReportError(
            "%s is missing identity sidecar(s): %s"
            % (csv_path, ", ".join(missing))
        )
    try:
        with open(metadata_path, encoding="utf-8") as source:
            metadata = json.load(source)
    except (OSError, json.JSONDecodeError) as exc:
        raise ReportError("cannot read metadata: " + metadata_path) from exc

    if not isinstance(metadata, dict):
        raise ReportError("metadata is not a JSON object: " + metadata_path)

    if metadata.get("schema_version") != SCHEMA_VERSION:
        raise ReportError(
            "%s has unsupported schema version %r (expected %d)"
            % (csv_path, metadata.get("schema_version"), SCHEMA_VERSION)
        )
    if metadata.get("mode") != "paired":
        raise ReportError(csv_path + " is not a paired campaign")
    if metadata.get("phase") != required_phase:
        raise ReportError(
            "%s is phase %r, expected %r"
            % (csv_path, metadata.get("phase"), required_phase)
        )
    runs = metadata.get("runs")
    if not isinstance(runs, int) or isinstance(runs, bool) or runs <= 0:
        raise ReportError(csv_path + " has invalid metadata runs")

    manifest = read_manifest(manifest_path)
    if metadata.get("file_count") != len(manifest):
        raise ReportError(csv_path + " sidecar file_count does not match manifest")
    if metadata.get("manifest_sha256") != digest_lines(manifest):
        raise ReportError(csv_path + " sidecar manifest digest does not match")
    identity = solver_identity(metadata)

    observations = []
    with open(csv_path, newline="", encoding="utf-8") as source:
        reader = csv.DictReader(source)
        missing_fields = set(PAIRED_FIELDS) - set(reader.fieldnames or [])
        unexpected_fields = set(reader.fieldnames or []) - set(PAIRED_FIELDS)
        if missing_fields or unexpected_fields:
            details = []
            if missing_fields:
                details.append("missing " + ", ".join(sorted(missing_fields)))
            if unexpected_fields:
                details.append("unexpected " + ", ".join(sorted(unexpected_fields)))
            raise ReportError("%s has wrong CSV schema: %s"
                              % (csv_path, "; ".join(details)))
        manifest_set = set(manifest)
        for line, row in enumerate(reader, start=2):
            observation = validate_row(row, csv_path, line, manifest_set, runs)
            observation["phase"] = required_phase
            observation["source_csv"] = csv_path
            observations.append(observation)
    return {
        "path": csv_path,
        "metadata": metadata,
        "identity": identity,
        "runs": runs,
        "manifest": manifest,
        "observations": observations,
    }


def load_phase(paths, phase):
    inputs = [load_csv(path, phase) for path in paths]
    if not inputs:
        return {
            "inputs": [], "manifest": set(), "observations": [],
            "by_key": {}, "identity": None, "runs": None,
        }
    identity = inputs[0]["identity"]
    runs = inputs[0]["runs"]
    timeout = inputs[0]["metadata"].get("timeout_seconds")
    observations = []
    manifests = set()
    by_key = {}
    for item in inputs:
        if item["identity"] != identity:
            raise ReportError(
                "solver identities differ between %s and %s"
                % (inputs[0]["path"], item["path"])
            )
        if item["runs"] != runs:
            raise ReportError("metadata run counts differ within %s phase" % phase)
        if item["metadata"].get("timeout_seconds") != timeout:
            raise ReportError("timeouts differ within %s phase" % phase)
        manifests.update(item["manifest"])
        for observation in item["observations"]:
            key = observation["key"]
            if key in by_key:
                raise ReportError(
                    "duplicate (file, run) key in %s phase: %r (from %s and %s)"
                    % (phase, key, by_key[key]["source_csv"], item["path"])
                )
            by_key[key] = observation
            observations.append(observation)
    return {
        "inputs": inputs,
        "manifest": manifests,
        "observations": observations,
        "by_key": by_key,
        "identity": identity,
        "runs": runs,
    }


def logic_family(path):
    parts = Path(path).parts
    for index, part in enumerate(parts):
        if re.fullmatch(r"QF_[A-Za-z0-9_]+", part):
            family_parts = parts[index + 1:-1]
            return part, "/".join(family_parts) if family_parts else "(root)"
    return "UNKNOWN", os.path.basename(os.path.dirname(path)) or "(root)"


def counter_text(counter):
    return ";".join("%s:%d" % item for item in sorted(counter.items()))


def timing_classification(median_a, median_b, ratio_threshold,
                          outlier_threshold):
    floor = 0.001
    b_over_a = max(median_b, floor) / max(median_a, floor)
    if b_over_a <= 1.0 / ratio_threshold:
        classification = "WIN"
    elif b_over_a >= ratio_threshold:
        classification = "LOSS"
    else:
        classification = "PARITY"
    magnitude = max(b_over_a, 1.0 / b_over_a)
    return b_over_a, classification, magnitude >= outlier_threshold


def make_file_rows(effective, intended_files, runs, disagreement_files,
                   ratio_threshold, outlier_threshold):
    by_file = collections.defaultdict(list)
    for observation in effective.values():
        by_file[observation["path"]].append(observation)
    all_files = sorted(set(intended_files) | set(by_file))
    result = []
    for path in all_files:
        observations = sorted(by_file[path], key=lambda item: item["run"])
        completed = {item["run"] for item in observations}
        missing = sorted(set(range(runs)) - completed)
        verdicts = collections.Counter(
            item["row"]["verdict"] for item in observations
        )
        statuses_a = collections.Counter(
            item["row"]["a_status"] for item in observations
        )
        statuses_b = collections.Counter(
            item["row"]["b_status"] for item in observations
        )
        a_answers = sum(len(item["parsed"]["a"]["answers"])
                        for item in observations)
        b_answers = sum(len(item["parsed"]["b"]["answers"])
                        for item in observations)
        ever_disagreement = path in disagreement_files
        if ever_disagreement or verdicts[DISAGREEMENT]:
            effective_verdict = DISAGREEMENT
        elif missing or verdicts[PREFIX_ONLY_INCONCLUSIVE]:
            effective_verdict = PREFIX_ONLY_INCONCLUSIVE
        elif observations and verdicts[FULL_OK] == runs:
            effective_verdict = FULL_OK
        else:
            effective_verdict = PREFIX_ONLY_INCONCLUSIVE

        timing_eligible = (
            not ever_disagreement
            and not missing
            and len(observations) == runs
            and all(item["row"]["verdict"] == FULL_OK
                    and item["row"]["a_status"] == "ok"
                    and item["row"]["b_status"] == "ok"
                    for item in observations)
        )
        median_a = median_b = b_over_a = None
        classification = "INELIGIBLE"
        outlier = False
        if timing_eligible:
            median_a = statistics.median(
                item["parsed"]["a"]["seconds"] for item in observations
            )
            median_b = statistics.median(
                item["parsed"]["b"]["seconds"] for item in observations
            )
            b_over_a, classification, outlier = timing_classification(
                median_a, median_b, ratio_threshold, outlier_threshold
            )
        logic, family = logic_family(path)
        result.append({
            "file": path,
            "logic": logic,
            "family": family,
            "effective_verdict": effective_verdict,
            "ever_disagreement": ever_disagreement,
            "expected_runs": runs,
            "completed_runs": sorted(completed),
            "missing_runs": missing,
            "effective_pairs": len(observations),
            "full_ok_pairs": verdicts[FULL_OK],
            "inconclusive_pairs": verdicts[PREFIX_ONLY_INCONCLUSIVE],
            "disagreement_pairs": verdicts[DISAGREEMENT],
            "a_statuses": dict(statuses_a),
            "b_statuses": dict(statuses_b),
            "a_answers": a_answers,
            "b_answers": b_answers,
            "median_a_seconds": median_a,
            "median_b_seconds": median_b,
            "b_over_a": b_over_a,
            "classification": classification,
            "timing_outlier": outlier,
        })
    return result


def group_summary(rows):
    verdicts = collections.Counter(row["effective_verdict"] for row in rows)
    classes = collections.Counter(row["classification"] for row in rows)
    status_a = collections.Counter()
    status_b = collections.Counter()
    for row in rows:
        status_a.update(row["a_statuses"])
        status_b.update(row["b_statuses"])
    ratios = [row["b_over_a"] for row in rows
              if row["b_over_a"] is not None]
    return {
        "files": len(rows),
        "effective_pairs": sum(row["effective_pairs"] for row in rows),
        "verdict_files": dict(verdicts),
        "observed_disagreement_files": sum(
            1 for row in rows if row["ever_disagreement"]
        ),
        "a_statuses": dict(status_a),
        "b_statuses": dict(status_b),
        "a_answers": sum(row["a_answers"] for row in rows),
        "b_answers": sum(row["b_answers"] for row in rows),
        "timing_eligible_files": len(ratios),
        "timing_classes": dict(classes),
        "timing_outliers": sum(1 for row in rows if row["timing_outlier"]),
        "median_b_over_a": statistics.median(ratios) if ratios else None,
        "sum_file_medians_a_seconds": sum(
            row["median_a_seconds"] or 0.0 for row in rows
        ),
        "sum_file_medians_b_seconds": sum(
            row["median_b_seconds"] or 0.0 for row in rows
        ),
    }


def grouped(rows, key):
    groups = collections.defaultdict(list)
    for row in rows:
        groups[key(row)].append(row)
    return {name: group_summary(group_rows)
            for name, group_rows in sorted(groups.items())}


def make_summary(main, revalidation, effective, file_rows, intended_files,
                 expected_runs, expected_answers, completeness_required,
                 ratio_threshold, outlier_threshold):
    all_observations = main["observations"] + revalidation["observations"]
    disagreement_observations = [
        item for item in all_observations
        if item["row"]["verdict"] == DISAGREEMENT
    ]
    intended_keys = {
        (path, run) for path in intended_files for run in range(expected_runs)
    }
    effective_keys = set(effective)
    verdict_rows = collections.Counter(
        item["row"]["verdict"] for item in effective.values()
    )
    statuses_a = collections.Counter(
        item["row"]["a_status"] for item in effective.values()
    )
    statuses_b = collections.Counter(
        item["row"]["b_status"] for item in effective.values()
    )
    answer_totals = {
        arm: sum(len(item["parsed"][arm]["answers"])
                 for item in effective.values())
        for arm in ("a", "b")
    }
    answer_summary = {
        "a": answer_totals["a"],
        "b": answer_totals["b"],
        "expected_per_arm": expected_answers,
        "a_shortfall": (
            max(expected_answers - answer_totals["a"], 0)
            if expected_answers is not None else None
        ),
        "b_shortfall": (
            max(expected_answers - answer_totals["b"], 0)
            if expected_answers is not None else None
        ),
        "a_excess": (
            max(answer_totals["a"] - expected_answers, 0)
            if expected_answers is not None else None
        ),
        "b_excess": (
            max(answer_totals["b"] - expected_answers, 0)
            if expected_answers is not None else None
        ),
    }
    effective_files = {path for path, _ in effective_keys}
    selected_main_files = set(main["manifest"])
    configured_runs = {
        "main": main["runs"],
        "revalidation": revalidation["runs"],
    }
    summary = {
        "schema_version": 1,
        "generated_utc": datetime.datetime.now(
            datetime.timezone.utc
        ).isoformat(),
        "inputs": {
            "main": [item["path"] for item in main["inputs"]],
            "revalidation": [item["path"]
                             for item in revalidation["inputs"]],
        },
        "solvers": main["identity"],
        "replacement": {
            "selected_files": len(revalidation["manifest"]),
            "main_rows_replaced": sum(
                1 for item in main["observations"]
                if item["path"] in revalidation["manifest"]
            ),
            "revalidation_rows": len(revalidation["observations"]),
        },
        "completeness": {
            "required": completeness_required,
            "expected_files": len(intended_files),
            "expected_runs": expected_runs,
            "expected_pairs": len(intended_keys),
            "effective_pairs": len(effective_keys),
            "selected_manifest_files": len(selected_main_files),
            "missing_manifest_files": sorted(
                set(intended_files) - selected_main_files
            ),
            "unexpected_manifest_files": sorted(
                selected_main_files - set(intended_files)
            ),
            "configured_runs": configured_runs,
            "configured_run_mismatch": any(
                value is not None and value != expected_runs
                for value in configured_runs.values()
            ),
            "missing_files": sorted(
                path for path in intended_files if path not in effective_files
            ),
            "missing_pairs": [
                {"file": path, "run": run}
                for path, run in sorted(intended_keys - effective_keys)
            ],
            "unexpected_pairs": [
                {"file": path, "run": run}
                for path, run in sorted(effective_keys - intended_keys)
            ],
        },
        "correctness": {
            "effective_row_verdicts": dict(verdict_rows),
            "effective_file_verdicts": dict(collections.Counter(
                row["effective_verdict"] for row in file_rows
            )),
            "observed_disagreement_rows": len(disagreement_observations),
            "observed_disagreement_files": len({
                item["path"] for item in disagreement_observations
            }),
        },
        "statuses": {
            "a": dict(statuses_a),
            "b": dict(statuses_b),
        },
        "answers": answer_summary,
        "timing": group_summary(file_rows),
        "thresholds": {
            "win_loss_ratio": ratio_threshold,
            "outlier_ratio": outlier_threshold,
        },
        "by_logic": grouped(file_rows, lambda row: row["logic"]),
        "by_logic_family": grouped(
            file_rows,
            lambda row: row["logic"] + "/" + row["family"],
        ),
    }
    return summary, disagreement_observations


def short_identity(identity, arm):
    solver = identity[arm]
    revision = solver.get("embedded_sha") or solver.get("binary_sha256") or "?"
    return "%s (%s)" % (solver.get("label") or arm, revision[:12])


def format_group_table(title, groups):
    lines = [
        title,
        "  group                                      "
        "files   full   inc   dis   win  loss  B/A",
    ]
    for name, item in groups.items():
        verdicts = item["verdict_files"]
        classes = item["timing_classes"]
        ratio = item["median_b_over_a"]
        lines.append(
            "  %-40s %6d %6d %5d %5d %5d %5d %5s"
            % (
                name[:40], item["files"], verdicts.get(FULL_OK, 0),
                verdicts.get(PREFIX_ONLY_INCONCLUSIVE, 0),
                verdicts.get(DISAGREEMENT, 0), classes.get("WIN", 0),
                classes.get("LOSS", 0),
                "-" if ratio is None else "%.2f" % ratio,
            )
        )
    return lines


def format_ranked(title, rows, reverse, top):
    eligible = [row for row in rows if row["b_over_a"] is not None]
    eligible.sort(key=lambda row: row["b_over_a"], reverse=reverse)
    lines = [title]
    for row in eligible[:top]:
        lines.append(
            "  B/A=%8.3f  A=%9.3fs  B=%9.3fs  %s"
            % (
                row["b_over_a"], row["median_a_seconds"],
                row["median_b_seconds"], row["file"],
            )
        )
    if not eligible:
        lines.append("  (none)")
    return lines


def human_report(summary, file_rows, top):
    completeness = summary["completeness"]
    correctness = summary["correctness"]
    timing = summary["timing"]
    verdict_rows = correctness["effective_row_verdicts"]
    classes = timing["timing_classes"]
    labels = summary["solvers"]
    lines = [
        "Paired incremental campaign report",
        "  A: " + short_identity(labels, "a"),
        "  B: " + short_identity(labels, "b"),
        "  inputs: %d main CSV(s), %d revalidation CSV(s)"
        % (len(summary["inputs"]["main"]),
           len(summary["inputs"]["revalidation"])),
        "",
        "Coverage",
        "  %d/%d effective pairs; %d/%d files; %d file(s) selected for revalidation"
        % (
            completeness["effective_pairs"], completeness["expected_pairs"],
            completeness["expected_files"] - len(completeness["missing_files"]),
            completeness["expected_files"],
            summary["replacement"]["selected_files"],
        ),
        "  missing pairs: %d; unexpected pairs: %d"
        % (len(completeness["missing_pairs"]),
           len(completeness["unexpected_pairs"])),
        "  manifest selection: %d missing, %d unexpected; run configuration: %s"
        % (
            len(completeness["missing_manifest_files"]),
            len(completeness["unexpected_manifest_files"]),
            "MISMATCH" if completeness["configured_run_mismatch"] else "ok",
        ),
        "",
        "Correctness and process status",
        "  effective rows: %d %s, %d %s, %d %s"
        % (
            verdict_rows.get(FULL_OK, 0), FULL_OK,
            verdict_rows.get(PREFIX_ONLY_INCONCLUSIVE, 0),
            PREFIX_ONLY_INCONCLUSIVE,
            verdict_rows.get(DISAGREEMENT, 0), DISAGREEMENT,
        ),
        "  disagreements ever observed: %d row(s), %d file(s)"
        % (correctness["observed_disagreement_rows"],
           correctness["observed_disagreement_files"]),
        "  A statuses: %s" % counter_text(summary["statuses"]["a"]),
        "  B statuses: %s" % counter_text(summary["statuses"]["b"]),
        "  answers retained: A=%d B=%d"
        % (summary["answers"]["a"], summary["answers"]["b"]),
    ]
    if summary["answers"]["expected_per_arm"] is not None:
        lines.append(
            "  expected per arm: %d; shortfall A=%d B=%d; excess A=%d B=%d"
            % (
                summary["answers"]["expected_per_arm"],
                summary["answers"]["a_shortfall"],
                summary["answers"]["b_shortfall"],
                summary["answers"]["a_excess"],
                summary["answers"]["b_excess"],
            ),
        )
    lines.extend([
        "",
        "Per-file median timing",
        "  eligible=%d; wins=%d parity=%d losses=%d; outliers=%d"
        % (
            timing["timing_eligible_files"], classes.get("WIN", 0),
            classes.get("PARITY", 0), classes.get("LOSS", 0),
            timing["timing_outliers"],
        ),
        "  sum of eligible file medians: A=%.3fs B=%.3fs; median B/A=%s"
        % (
            timing["sum_file_medians_a_seconds"],
            timing["sum_file_medians_b_seconds"],
            "-" if timing["median_b_over_a"] is None
            else "%.3f" % timing["median_b_over_a"],
        ),
        "",
    ])
    lines.extend(format_group_table("By logic", summary["by_logic"]))
    lines.append("")
    lines.extend(format_group_table(
        "By logic/family", summary["by_logic_family"]
    ))
    lines.append("")
    wins = [row for row in file_rows if row["classification"] == "WIN"]
    losses = [row for row in file_rows if row["classification"] == "LOSS"]
    outliers = [row for row in file_rows if row["timing_outlier"]]
    lines.extend(format_ranked("Largest wins (candidate B)", wins, False, top))
    lines.append("")
    lines.extend(format_ranked("Largest losses (candidate B)", losses, True, top))
    lines.append("")
    outliers.sort(
        key=lambda row: max(row["b_over_a"], 1.0 / row["b_over_a"]),
        reverse=True,
    )
    lines.append("Largest timing outliers (either direction)")
    for row in outliers[:top]:
        lines.append(
            "  %-4s B/A=%8.3f  A=%9.3fs  B=%9.3fs  %s"
            % (
                row["classification"], row["b_over_a"],
                row["median_a_seconds"], row["median_b_seconds"], row["file"],
            )
        )
    if not outliers:
        lines.append("  (none)")
    if completeness["missing_pairs"]:
        lines.extend(["", "First missing pairs"])
        for item in completeness["missing_pairs"][:top]:
            lines.append("  run=%d %s" % (item["run"], item["file"]))
    manifest_mismatches = (
        [("missing", path) for path in completeness["missing_manifest_files"]]
        + [("unexpected", path)
           for path in completeness["unexpected_manifest_files"]]
    )
    if manifest_mismatches:
        lines.extend(["", "First manifest-selection mismatches"])
        for kind, path in manifest_mismatches[:top]:
            lines.append("  %-10s %s" % (kind, path))
    return "\n".join(lines) + "\n"


def atomic_write(path, writer):
    directory = os.path.dirname(os.path.abspath(path))
    os.makedirs(directory, exist_ok=True)
    temporary = path + ".tmp"
    try:
        writer(temporary)
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def write_csv(path, fields, rows):
    def write(temporary):
        with open(temporary, "w", newline="", encoding="utf-8") as target:
            csv_writer = csv.DictWriter(target, fieldnames=fields)
            csv_writer.writeheader()
            csv_writer.writerows(rows)
    atomic_write(path, write)


def output_combined(prefix, effective, disagreement_observations, file_rows,
                    summary, report):
    combined = []
    disagreement_files = {
        evidence["path"] for evidence in disagreement_observations
    }
    for item in sorted(effective.values(), key=lambda value: value["key"]):
        row = {
            "phase": item["phase"],
            "source_csv": item["source_csv"],
            "ever_disagreement": (
                "yes" if item["path"] in disagreement_files else "no"
            ),
        }
        row.update(item["row"])
        combined.append(row)
    evidence_rows = []
    for item in sorted(
        disagreement_observations,
        key=lambda value: (value["path"], value["run"], value["phase"]),
    ):
        row = {"phase": item["phase"], "source_csv": item["source_csv"]}
        row.update(item["row"])
        evidence_rows.append(row)
    serialized_file_rows = []
    for item in file_rows:
        row = dict(item)
        row["ever_disagreement"] = "yes" if row["ever_disagreement"] else "no"
        row["completed_runs"] = ";".join(map(str, row["completed_runs"]))
        row["missing_runs"] = ";".join(map(str, row["missing_runs"]))
        row["a_statuses"] = counter_text(row["a_statuses"])
        row["b_statuses"] = counter_text(row["b_statuses"])
        for name in ("median_a_seconds", "median_b_seconds", "b_over_a"):
            row[name] = "" if row[name] is None else "%.6f" % row[name]
        row["timing_outlier"] = "yes" if row["timing_outlier"] else "no"
        serialized_file_rows.append(row)

    write_csv(prefix + ".combined.csv", COMBINED_FIELDS, combined)
    write_csv(prefix + ".disagreements.csv", EVIDENCE_FIELDS, evidence_rows)
    write_csv(prefix + ".files.csv", FILE_FIELDS, serialized_file_rows)

    def write_json(path):
        with open(path, "w", encoding="utf-8") as target:
            json.dump(summary, target, indent=2, sort_keys=True)
            target.write("\n")

    def write_text(path):
        with open(path, "w", encoding="utf-8") as target:
            target.write(report)

    atomic_write(prefix + ".summary.json", write_json)
    atomic_write(prefix + ".txt", write_text)


def aggregate(args):
    main_paths = expand_inputs(args.main, "--main")
    revalidation_paths = expand_inputs(args.revalidation, "--revalidation")
    if not main_paths:
        raise ReportError("provide at least one --main CSV or glob")
    main = load_phase(main_paths, "main")
    revalidation = load_phase(revalidation_paths, "revalidation")
    if revalidation["identity"] is not None:
        if revalidation["identity"] != main["identity"]:
            raise ReportError("solver identities differ between main and revalidation")
        if revalidation["runs"] != main["runs"]:
            raise ReportError("metadata run counts differ between phases")
    absent_from_main = revalidation["manifest"] - main["manifest"]
    if absent_from_main:
        raise ReportError(
            "revalidation selected a file absent from main manifests: "
            + sorted(absent_from_main)[0]
        )

    effective = {
        key: item for key, item in main["by_key"].items()
        if item["path"] not in revalidation["manifest"]
    }
    effective.update(revalidation["by_key"])

    intended_files = set(main["manifest"])
    if args.expected_manifest:
        intended_files = set(read_manifest(
            os.path.abspath(args.expected_manifest)
        ))
    expected_runs = args.expected_runs or main["runs"]
    disagreement_files = {
        item["path"]
        for item in main["observations"] + revalidation["observations"]
        if item["row"]["verdict"] == DISAGREEMENT
    }
    file_rows = make_file_rows(
        effective, intended_files, expected_runs, disagreement_files,
        args.ratio, args.outlier_ratio,
    )
    summary, disagreements = make_summary(
        main, revalidation, effective, file_rows, intended_files,
        expected_runs, args.expected_answers,
        bool(args.expected_manifest is not None
             or args.expected_runs is not None
             or args.expected_answers is not None),
        args.ratio, args.outlier_ratio,
    )
    report = human_report(summary, file_rows, args.top)
    if args.output_prefix:
        output_combined(
            os.path.abspath(args.output_prefix), effective, disagreements,
            file_rows, summary, report,
        )
    return summary, report


def make_parser():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--main", action="append", default=[], metavar="CSV_OR_GLOB",
        help="main paired CSV or glob; repeat as needed",
    )
    parser.add_argument(
        "--revalidation", action="append", default=[], metavar="CSV_OR_GLOB",
        help="revalidation paired CSV or glob; repeat as needed",
    )
    parser.add_argument(
        "--expected-manifest",
        help="require coverage of exactly this campaign manifest",
    )
    parser.add_argument(
        "--expected-runs", type=int,
        help="require run numbers 0..N-1 for every expected file",
    )
    parser.add_argument(
        "--expected-answers", type=int,
        help="require this total number of answer tokens from each arm",
    )
    parser.add_argument(
        "--output-prefix",
        help="write combined/evidence/per-file CSVs and JSON/text reports",
    )
    parser.add_argument(
        "--ratio", type=float, default=2.0,
        help="B/A ratio used to classify median timing wins/losses (default: 2)",
    )
    parser.add_argument(
        "--outlier-ratio", type=float, default=3.0,
        help="either-direction median timing outlier ratio (default: 3)",
    )
    parser.add_argument(
        "--top", type=int, default=20,
        help="maximum ranked and missing entries in the text report (default: 20)",
    )
    parser.add_argument(
        "--require-full-ok", action="store_true",
        help="exit 1 for any effective non-FULL_OK row or incomplete pair",
    )
    return parser


def main(argv=None):
    parser = make_parser()
    args = parser.parse_args(argv)
    if args.expected_runs is not None and args.expected_runs <= 0:
        parser.error("--expected-runs must be positive")
    if args.expected_answers is not None and args.expected_answers < 0:
        parser.error("--expected-answers must be non-negative")
    if args.ratio <= 1.0:
        parser.error("--ratio must be greater than one")
    if args.outlier_ratio <= 1.0:
        parser.error("--outlier-ratio must be greater than one")
    if args.top < 0:
        parser.error("--top must be non-negative")
    try:
        summary, report = aggregate(args)
    except (OSError, UnicodeError, ReportError) as exc:
        parser.error(str(exc))
    sys.stdout.write(report)

    correctness = summary["correctness"]
    completeness = summary["completeness"]
    failed = correctness["observed_disagreement_rows"] > 0
    if completeness["required"]:
        failed = failed or bool(
            completeness["missing_pairs"]
            or completeness["unexpected_pairs"]
            or completeness["missing_manifest_files"]
            or completeness["unexpected_manifest_files"]
            or completeness["configured_run_mismatch"]
        )
        expected_answers = summary["answers"]["expected_per_arm"]
        if expected_answers is not None:
            failed = failed or any(
                summary["answers"][arm] != expected_answers
                for arm in ("a", "b")
            )
    if args.require_full_ok:
        verdicts = correctness["effective_row_verdicts"]
        failed = failed or any(
            verdicts.get(verdict, 0)
            for verdict in (PREFIX_ONLY_INCONCLUSIVE, DISAGREEMENT)
        )
        failed = failed or bool(
            completeness["missing_pairs"] or completeness["unexpected_pairs"]
        )
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
