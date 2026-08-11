#!/usr/bin/env python3
# AUTHORS: Andrew Teylu

import importlib.util
import pathlib
import sys
import tempfile
import unittest


def load_differential(path):
    spec = importlib.util.spec_from_file_location("prime_differential", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


DIFFERENTIAL = load_differential(sys.argv[1])


class PrimeMemosDifferentialTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.temporary.name)
        (self.root / "1").mkdir()
        (self.root / "0").mkdir()

    def tearDown(self):
        self.temporary.cleanup()

    def result(self, status="completed", detail="", files=(), stdout=b""):
        return DIFFERENTIAL.RunResult(status, detail, files, stdout)

    def test_accepts_only_exact_completed_pairs(self):
        (self.root / "1" / "out.cnf").write_text("p cnf 1 0\n")
        (self.root / "0" / "out.cnf").write_text("p cnf 1 0\n")
        on = self.result(files=("out.cnf",), stdout=b"sat\n")
        off = self.result(files=("out.cnf",), stdout=b"sat\n")

        self.assertIsNone(
            DIFFERENTIAL.comparison_problem(on, off, str(self.root)))

    def test_rejects_asymmetric_completion(self):
        problem = DIFFERENTIAL.comparison_problem(
            self.result(), self.result("exit", "-6"), str(self.root))

        self.assertIn("asymmetric", problem)
        self.assertIn("exit (-6)", problem)

    def test_rejects_newly_incomparable_pairs(self):
        problem = DIFFERENTIAL.comparison_problem(
            self.result("timeout", "60s"),
            self.result("timeout", "60s"), str(self.root))

        self.assertIn("newly incomparable", problem)

    def test_rejects_stdout_or_cnf_differences(self):
        (self.root / "1" / "out.cnf").write_text("p cnf 1 0\n")
        (self.root / "0" / "out.cnf").write_text("p cnf 2 0\n")
        on = self.result(files=("out.cnf",), stdout=b"sat\n")
        off = self.result(files=("out.cnf",), stdout=b"unsat\n")

        problem = DIFFERENTIAL.comparison_problem(on, off, str(self.root))

        self.assertIn("stdout", problem)
        self.assertIn("CNF contents", problem)

    def test_metadata_excludes_negative_and_unavailable_tests(self):
        negative = self.root / "negative.smt2"
        negative.write_text("; RUN: not %solver %s\n(check-sat)\n")
        required = self.root / "required.smt2"
        required.write_text(
            "; REQUIRES: libbf\n; RUN: %solver %s\n(check-sat)\n")

        self.assertFalse(DIFFERENTIAL.query_selected(
            str(negative), str(self.root), set())[0])
        self.assertFalse(DIFFERENTIAL.query_selected(
            str(required), str(self.root), set())[0])
        self.assertTrue(DIFFERENTIAL.query_selected(
            str(required), str(self.root), {"libbf"})[0])


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0]])
