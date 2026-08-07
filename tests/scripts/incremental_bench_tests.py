#!/usr/bin/env python3
# AUTHORS: Andrew Teylu

import csv
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest


REPOSITORY = Path(__file__).resolve().parents[2]
HARNESS = REPOSITORY / "scripts" / "incremental-bench.py"
SPEC = importlib.util.spec_from_file_location("incremental_bench", HARNESS)
BENCH = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = BENCH
SPEC.loader.exec_module(BENCH)


def write_solver(path, program):
    path.write_text(
        textwrap.dedent(program).lstrip(),
        encoding="utf-8",
    )


def read_rows(path):
    with path.open(newline="", encoding="utf-8") as source:
        return list(csv.DictReader(source))


class IncrementalBenchUnitTests(unittest.TestCase):
    def result(self, status, answers):
        return BENCH.RunResult(status, 0.01, tuple(answers), 0)

    def test_comparison_requires_two_complete_equal_sequences(self):
        self.assertEqual(
            BENCH.FULL_OK,
            BENCH.compare_results(
                self.result("ok", ["sat", "unsat"]),
                self.result("ok", ["sat", "unsat"]),
            ),
        )
        self.assertEqual(
            BENCH.PREFIX_ONLY_INCONCLUSIVE,
            BENCH.compare_results(
                self.result("timeout", ["sat"]),
                self.result("ok", ["sat", "unsat"]),
            ),
        )
        self.assertEqual(
            BENCH.DISAGREEMENT,
            BENCH.compare_results(
                self.result("ok", ["sat"]),
                self.result("ok", ["sat", "unsat"]),
            ),
        )
        self.assertEqual(
            BENCH.DISAGREEMENT,
            BENCH.compare_results(
                self.result("timeout", ["sat", "unsat"]),
                self.result("timeout", ["sat", "sat"]),
            ),
        )
        self.assertEqual(
            BENCH.DISAGREEMENT,
            BENCH.compare_results(
                self.result("ok", ["sat"]),
                self.result("timeout", ["sat", "unsat"]),
            ),
        )

    def test_timeout_preserves_answer_prefix(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            solver = directory / "solver.py"
            query = directory / "query.smt2"
            query.write_text("(check-sat)\n", encoding="utf-8")
            write_solver(
                solver,
                """
                import time
                print("sat", flush=True)
                time.sleep(1.0)
                print("unsat", flush=True)
                """,
            )
            result = BENCH.run_one(
                sys.executable, [str(solver)], str(query), 0.1
            )
            self.assertEqual("timeout", result.status)
            self.assertEqual(("sat",), result.answers)

    def test_stp_version_metadata_is_parsed(self):
        output = """\
STP version 2.4.1
STP version SHA string deadbeef
STP compilation options CMAKE_BUILD_TYPE = Release | USE_CADICAL
"""
        sha, options = BENCH.parse_version_output(output)
        self.assertEqual("deadbeef", sha)
        self.assertIn("CMAKE_BUILD_TYPE = Release", options)

    def test_dynamic_libstp_identity_is_extracted(self):
        output = """\
libstp.so.2.4 => /tmp/lib/libstp.so.2.4 (0x00000000)
libstdc++.so.6 => /lib/libstdc++.so.6 (0x00000000)
"""
        libraries = BENCH.linked_stp_libraries(output)
        self.assertEqual(1, len(libraries))
        self.assertEqual("/tmp/lib/libstp.so.2.4", libraries[0]["path"])

    def test_resume_requires_identity_sidecars(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "results.csv"
            output.write_text("file,status\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "cannot safely resume"):
                BENCH.require_resume_provenance(str(output), True)

    def test_revalidation_uses_per_file_medians_for_timing(self):
        rows = []
        for run, first_time in enumerate((0.01, 0.01, 1.0)):
            first = BENCH.RunResult("ok", first_time, ("sat",), 0)
            second = BENCH.RunResult("ok", 0.01, ("sat",), 0)
            rows.append(
                BENCH.paired_row("query.smt2", run, "AB", first, second)
            )
        self.assertEqual([], BENCH.revalidation_files(rows, 3.0))


class IncrementalBenchCliTests(unittest.TestCase):
    def run_harness(self, arguments, expected_returncode=0):
        proc = subprocess.run(
            [sys.executable, str(HARNESS)] + list(arguments),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=15,
        )
        if proc.returncode != expected_returncode:
            self.fail(
                "harness returned %d, expected %d\nstdout:\n%s\nstderr:\n%s"
                % (
                    proc.returncode, expected_returncode,
                    proc.stdout, proc.stderr,
                )
            )
        return proc

    def test_paired_mode_shards_balances_defers_and_resumes(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            solver_a = directory / "solver_a.py"
            solver_b = directory / "solver_b.py"
            write_solver(
                solver_a,
                """
                import os
                import sys
                name = os.path.basename(sys.argv[-1])
                print("sat", flush=True)
                if "disagree" not in name:
                    print("unsat", flush=True)
                """,
            )
            write_solver(
                solver_b,
                """
                import os
                import sys
                name = os.path.basename(sys.argv[-1])
                print("unsat" if "disagree" in name else "sat", flush=True)
                if "disagree" not in name:
                    print("unsat", flush=True)
                """,
            )
            queries = []
            for name in (
                "0_full.smt2", "1_disagree.smt2",
                "2_full.smt2", "3_full.smt2",
            ):
                query = directory / name
                query.write_text("(check-sat)\n", encoding="utf-8")
                queries.append(query)
            manifest = directory / "input.manifest"
            manifest.write_text(
                "\n".join(query.name for query in queries) + "\n",
                encoding="utf-8",
            )
            output = directory / "campaign.csv"
            arguments = [
                "--solver-a", sys.executable,
                "--arg-a", str(solver_a),
                "--solver-b", sys.executable,
                "--arg-b", str(solver_b),
                "--manifest", str(manifest),
                "--shard-count", "2",
                "--shard-index", "1",
                "--runs", "2",
                "--out", str(output),
                "--defer-revalidation",
            ]
            self.run_harness(arguments, expected_returncode=1)

            rows = read_rows(output)
            self.assertEqual(4, len(rows))
            self.assertEqual(
                {str(queries[1].resolve()), str(queries[3].resolve())},
                {row["file"] for row in rows},
            )
            by_file = {}
            for row in rows:
                by_file.setdefault(row["file"], []).append(row)
            for file_rows in by_file.values():
                self.assertEqual({"AB", "BA"}, {row["order"] for row in file_rows})
            disagreement_rows = by_file[str(queries[1].resolve())]
            self.assertEqual(
                {BENCH.DISAGREEMENT},
                {row["verdict"] for row in disagreement_rows},
            )

            with Path(str(output) + ".meta.json").open(encoding="utf-8") as source:
                metadata = json.load(source)
            self.assertEqual("paired", metadata["mode"])
            self.assertEqual(2, metadata["file_count"])
            self.assertTrue(metadata["solvers"]["a"]["binary_sha256"])
            self.assertEqual([str(solver_a)], metadata["solvers"]["a"]["arguments"])

            revalidation_manifest = Path(str(output) + ".revalidate.manifest")
            self.assertEqual(
                str(queries[1].resolve()) + "\n",
                revalidation_manifest.read_text(encoding="utf-8"),
            )
            self.assertFalse((directory / "campaign.revalidation.csv").exists())

            self.run_harness(arguments + ["--resume"], expected_returncode=1)
            self.assertEqual(rows, read_rows(output))

    def test_original_single_solver_workflow_remains_available(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            solver = directory / "solver.py"
            write_solver(
                solver,
                """
                print("sat", flush=True)
                print("unsat", flush=True)
                """,
            )
            query = directory / "query.smt2"
            query.write_text("(check-sat)\n", encoding="utf-8")
            baseline = directory / "baseline.csv"
            candidate = directory / "candidate.csv"
            common = [
                "--solver", sys.executable,
                "--arg", str(solver),
                str(query),
            ]
            self.run_harness(
                common[:4] + ["--out", str(baseline)] + common[4:]
            )
            self.run_harness(
                common[:4]
                + ["--out", str(candidate), "--compare", str(baseline)]
                + common[4:]
            )
            row = read_rows(candidate)[0]
            self.assertEqual("sat;unsat", row["answers"])
            self.assertEqual(BENCH.FULL_OK, row["comparison"])

    def test_automatic_revalidation_uses_longer_timeout(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            quick = directory / "quick.py"
            slow = directory / "slow.py"
            write_solver(quick, 'print("sat", flush=True)\n')
            write_solver(
                slow,
                """
                import time
                print("sat", flush=True)
                time.sleep(0.2)
                """,
            )
            query = directory / "query.smt2"
            query.write_text("(check-sat)\n", encoding="utf-8")
            output = directory / "campaign.csv"
            self.run_harness(
                [
                    "--solver-a", sys.executable,
                    "--arg-a", str(quick),
                    "--solver-b", sys.executable,
                    "--arg-b", str(slow),
                    "--timeout", "0.05",
                    "--revalidation-timeout", "0.5",
                    "--runs", "1",
                    "--out", str(output),
                    str(query),
                ]
            )
            main_rows = read_rows(output)
            self.assertEqual(
                BENCH.PREFIX_ONLY_INCONCLUSIVE,
                main_rows[0]["verdict"],
            )
            revalidation = directory / "campaign.revalidation.csv"
            self.assertTrue(revalidation.exists())
            self.assertEqual(BENCH.FULL_OK, read_rows(revalidation)[0]["verdict"])


if __name__ == "__main__":
    unittest.main()
