#!/usr/bin/env python3
# AUTHORS: Andrew Teylu

import csv
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


REPOSITORY = Path(__file__).resolve().parents[2]
REPORTER = REPOSITORY / "scripts" / "incremental-bench-report.py"
SPEC = importlib.util.spec_from_file_location("incremental_bench_report", REPORTER)
REPORT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = REPORT
SPEC.loader.exec_module(REPORT)


def solver_identity(suffix="same"):
    def arm(name):
        return {
            "label": name,
            "binary_realpath": "/build/%s/stp" % name,
            "binary_sha256": "%s-%s" % (name, suffix),
            "arguments": ["--array-equality"],
            "embedded_sha": "%s-revision-%s" % (name, suffix),
            "compilation_options": "Release %s" % suffix,
            "linked_stp_libraries": [{
                "path": "/build/%s/libstp.so" % name,
                "realpath": "/build/%s/libstp.so" % name,
                "sha256": "%s-library-%s" % (name, suffix),
            }],
        }
    return {"a": arm("baseline"), "b": arm("candidate")}


def pair_row(path, run, a_seconds, b_seconds, a_answers=("sat",),
             b_answers=None, a_status="ok", b_status="ok"):
    if b_answers is None:
        b_answers = a_answers
    verdict = REPORT.comparison(a_status, a_answers, b_status, b_answers)
    return {
        "file": str(path),
        "run": str(run),
        "order": "AB" if run % 2 == 0 else "BA",
        "verdict": verdict,
        "a_status": a_status,
        "a_seconds": "%.6f" % a_seconds,
        "a_answers": ";".join(a_answers),
        "a_returncode": "0" if a_status == "ok" else "",
        "b_status": b_status,
        "b_seconds": "%.6f" % b_seconds,
        "b_answers": ";".join(b_answers),
        "b_returncode": "0" if b_status == "ok" else "",
    }


def write_input(directory, name, phase, files, rows, runs=2, identity=None,
                timeout=30.0, revalidation_selection=(), source_output=None):
    path = directory / name
    files = [str(file) for file in files]
    with path.open("w", newline="", encoding="utf-8") as target:
        writer = csv.DictWriter(target, fieldnames=REPORT.PAIRED_FIELDS)
        writer.writeheader()
        writer.writerows(rows)
    Path(str(path) + ".manifest").write_text(
        "".join(file + "\n" for file in files), encoding="utf-8"
    )
    metadata = {
        "schema_version": REPORT.SCHEMA_VERSION,
        "mode": "paired",
        "phase": phase,
        "timeout_seconds": timeout,
        "runs": runs,
        "file_count": len(files),
        "manifest_sha256": REPORT.digest_lines(files),
        "solvers": identity or solver_identity(),
    }
    if phase == "main":
        Path(str(path) + ".revalidate.manifest").write_text(
            "".join(str(file) + "\n" for file in revalidation_selection),
            encoding="utf-8",
        )
    else:
        metadata["source_output"] = str(source_output)
    Path(str(path) + ".meta.json").write_text(
        json.dumps(metadata), encoding="utf-8"
    )
    return path


def read_rows(path):
    with path.open(newline="", encoding="utf-8") as source:
        return list(csv.DictReader(source))


class IncrementalBenchReportTests(unittest.TestCase):
    def run_reporter(self, arguments, expected_returncode=0):
        proc = subprocess.run(
            [sys.executable, str(REPORTER)] + list(arguments),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=10,
        )
        if proc.returncode != expected_returncode:
            self.fail(
                "reporter returned %d, expected %d\nstdout:\n%s\nstderr:\n%s"
                % (proc.returncode, expected_returncode, proc.stdout, proc.stderr)
            )
        return proc

    def test_combines_shards_and_reports_streams_medians_and_families(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            first = directory / "corpus" / "QF_BV" / "Suite" / "one.smt2"
            second = directory / "corpus" / "QF_ABV" / "Family" / "two.smt2"
            rows_first = [
                pair_row(first, 0, 4.0, 1.0, ("sat", "unsat", "unknown")),
                pair_row(first, 1, 6.0, 2.0, ("unsat",)),
            ]
            rows_second = [
                pair_row(second, 0, 1.0, 5.0),
                pair_row(second, 1, 1.0, 7.0),
            ]
            write_input(directory, "main-0.csv", "main", [first], rows_first)
            write_input(directory, "main-1.csv", "main", [second], rows_second)
            expected = directory / "corpus.manifest"
            expected.write_text("%s\n%s\n" % (first, second), encoding="utf-8")
            prefix = directory / "report"

            proc = self.run_reporter([
                "--main", str(directory / "main-*.csv"),
                "--expected-manifest", str(expected),
                "--expected-runs", "2",
                "--expected-answers", "6",
                "--output-prefix", str(prefix),
                "--require-full-ok",
            ])
            self.assertIn("4/4 effective pairs", proc.stdout)

            combined = read_rows(directory / "report.combined.csv")
            self.assertEqual(4, len(combined))
            self.assertEqual(
                "sat;unsat;unknown",
                next(row for row in combined if row["file"] == str(first)
                     and row["run"] == "0")["a_answers"],
            )
            files = {row["file"]: row
                     for row in read_rows(directory / "report.files.csv")}
            self.assertEqual("WIN", files[str(first)]["classification"])
            self.assertEqual("0.300000", files[str(first)]["b_over_a"])
            self.assertEqual("LOSS", files[str(second)]["classification"])
            self.assertEqual("QF_ABV", files[str(second)]["logic"])
            self.assertEqual("Family", files[str(second)]["family"])

            summary = json.loads(
                (directory / "report.summary.json").read_text(encoding="utf-8")
            )
            self.assertEqual(6, summary["answers"]["a"])
            self.assertEqual(6, summary["answers"]["expected_per_arm"])
            self.assertEqual(0, summary["answers"]["b_shortfall"])
            self.assertEqual(1, summary["by_logic"]["QF_BV"]["timing_classes"]["WIN"])
            family_timing = summary["by_logic_family"][
                "QF_ABV/Family"
            ]["timing_classes"]
            self.assertEqual(1, family_timing["LOSS"])

    def test_revalidation_replaces_whole_file_but_keeps_disagreement_evidence(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            query = directory / "QF_BV" / "Family" / "query.smt2"
            main_rows = [
                pair_row(query, 0, 1.0, 1.0, ("sat",), ("unsat",)),
                pair_row(query, 1, 1.0, 1.0, ("sat",)),
            ]
            revalidation_rows = [
                pair_row(query, 0, 2.0, 2.0, ("unsat", "sat")),
                pair_row(query, 1, 2.0, 2.0, ("sat", "sat")),
            ]
            main = write_input(
                directory, "main.csv", "main", [query], main_rows,
                revalidation_selection=[query],
            )
            revalidation = write_input(
                directory, "revalidation.csv", "revalidation", [query],
                revalidation_rows, timeout=120.0, source_output=main,
            )
            prefix = directory / "report"
            self.run_reporter([
                "--main", str(main), "--revalidation", str(revalidation),
                "--expected-runs", "2", "--output-prefix", str(prefix),
            ], expected_returncode=1)

            combined = read_rows(directory / "report.combined.csv")
            self.assertEqual(2, len(combined))
            self.assertEqual({"revalidation"}, {row["phase"] for row in combined})
            self.assertEqual({"yes"}, {row["ever_disagreement"] for row in combined})
            self.assertEqual(
                {"unsat;sat", "sat;sat"}, {row["a_answers"] for row in combined}
            )
            evidence = read_rows(directory / "report.disagreements.csv")
            self.assertEqual(1, len(evidence))
            self.assertEqual("main", evidence[0]["phase"])
            self.assertEqual("sat", evidence[0]["a_answers"])
            self.assertEqual("unsat", evidence[0]["b_answers"])
            file_row = read_rows(directory / "report.files.csv")[0]
            self.assertEqual(REPORT.DISAGREEMENT,
                             file_row["effective_verdict"])
            self.assertEqual("INELIGIBLE", file_row["classification"])
            summary = json.loads(
                (directory / "report.summary.json").read_text(encoding="utf-8")
            )
            self.assertEqual({REPORT.FULL_OK: 2},
                             summary["correctness"]["effective_row_verdicts"])
            self.assertEqual(1,
                             summary["correctness"]["observed_disagreement_rows"])

    def test_incomplete_revalidation_does_not_fall_back_to_main_row(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            query = directory / "QF_BV" / "Family" / "query.smt2"
            main = write_input(directory, "main.csv", "main", [query], [
                pair_row(query, 0, 1.0, 1.0),
                pair_row(query, 1, 1.0, 1.0),
            ], revalidation_selection=[query])
            revalidation = write_input(
                directory, "revalidation.csv", "revalidation", [query],
                [pair_row(query, 0, 2.0, 2.0)], timeout=120.0,
                source_output=main,
            )
            prefix = directory / "report"
            self.run_reporter([
                "--main", str(main), "--revalidation", str(revalidation),
                "--expected-runs", "2", "--output-prefix", str(prefix),
            ], expected_returncode=1)

            combined = read_rows(directory / "report.combined.csv")
            self.assertEqual(["0"], [row["run"] for row in combined])
            summary = json.loads(
                (directory / "report.summary.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                [{"file": str(query), "run": 1}],
                summary["completeness"]["missing_pairs"],
            )

    def test_rejects_duplicate_keys_and_changed_solver_identity(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            query = directory / "QF_BV" / "query.smt2"
            row = pair_row(query, 0, 1.0, 1.0)
            first = write_input(
                directory, "main-0.csv", "main", [query], [row], runs=1
            )
            second = write_input(
                directory, "main-1.csv", "main", [query], [row], runs=1
            )
            proc = self.run_reporter([
                "--main", str(first), "--main", str(second),
            ], expected_returncode=2)
            self.assertIn("duplicate (file, run) key", proc.stderr)

            revalidation = write_input(
                directory, "revalidation.csv", "revalidation", [query], [row],
                runs=1, identity=solver_identity("changed"), timeout=120.0,
                source_output=first,
            )
            proc = self.run_reporter([
                "--main", str(first), "--revalidation", str(revalidation),
            ], expected_returncode=2)
            self.assertIn("solver identities differ", proc.stderr)

    def test_matching_exit_signal_prefix_is_inconclusive_and_short(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            query = directory / "QF_BV" / "query.smt2"
            crash = pair_row(
                query, 0, 0.5, 0.6, ("sat",),
                a_status="exit-11", b_status="exit-11",
            )
            self.assertEqual(REPORT.PREFIX_ONLY_INCONCLUSIVE,
                             crash["verdict"])
            main = write_input(
                directory, "main.csv", "main", [query], [crash], runs=1
            )
            prefix = directory / "report"
            proc = self.run_reporter([
                "--main", str(main), "--expected-runs", "1",
                "--expected-answers", "2", "--output-prefix", str(prefix),
            ], expected_returncode=1)
            self.assertIn("1 PREFIX_ONLY_INCONCLUSIVE", proc.stdout)
            self.assertIn("shortfall A=1 B=1", proc.stdout)
            summary = json.loads(
                (directory / "report.summary.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                {REPORT.PREFIX_ONLY_INCONCLUSIVE: 1},
                summary["correctness"]["effective_row_verdicts"],
            )
            self.assertEqual({"exit-11": 1}, summary["statuses"]["a"])
            self.assertEqual(1, summary["answers"]["a_shortfall"])
            self.assertEqual(1, summary["answers"]["b_shortfall"])

    def test_missing_revalidation_csv_never_falls_back_to_main_timing(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            query = directory / "QF_BV" / "Family" / "query.smt2"
            main = write_input(
                directory, "main.csv", "main", [query],
                [pair_row(query, 0, 1.0, 5.0)], runs=1,
                revalidation_selection=[query],
            )
            prefix = directory / "report"
            self.run_reporter([
                "--main", str(main), "--expected-runs", "1",
                "--output-prefix", str(prefix),
            ], expected_returncode=1)

            self.assertEqual([], read_rows(directory / "report.combined.csv"))
            summary = json.loads(
                (directory / "report.summary.json").read_text(encoding="utf-8")
            )
            self.assertEqual(1, summary["replacement"]["selected_files"])
            self.assertEqual(
                [str(query)],
                summary["replacement"]["missing_output_files"],
            )
            self.assertEqual(
                [{"file": str(query), "run": 0}],
                summary["completeness"]["missing_pairs"],
            )

    def test_revalidation_must_name_its_loaded_selected_main_source(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            query = directory / "QF_BV" / "query.smt2"
            row = pair_row(query, 0, 1.0, 1.0)
            main = write_input(
                directory, "main.csv", "main", [query], [row], runs=1,
                revalidation_selection=[query],
            )
            revalidation = write_input(
                directory, "revalidation.csv", "revalidation", [query],
                [row], runs=1, timeout=120.0,
                source_output=directory / "different-main.csv",
            )
            proc = self.run_reporter([
                "--main", str(main), "--revalidation", str(revalidation),
            ], expected_returncode=2)
            self.assertIn("unloaded main source_output", proc.stderr)


if __name__ == "__main__":
    unittest.main()
