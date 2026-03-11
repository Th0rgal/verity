#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_paths as checker


class CheckPathsTests(unittest.TestCase):
    def test_detects_top_level_case_conflict(self) -> None:
        paths = ["Compiler/Main.lean", "compiler/yul/Foo.yul"]
        conflicts = checker._find_case_conflicts(paths)
        self.assertIn(["Compiler", "compiler"], conflicts)

    def test_detects_nested_case_conflict(self) -> None:
        paths = ["Compiler/Proofs/A.lean", "compiler/proofs/B.lean"]
        conflicts = checker._find_case_conflicts(paths)
        self.assertIn(["Compiler", "compiler"], conflicts)
        self.assertIn(["Compiler/Proofs", "compiler/proofs"], conflicts)

    def test_no_conflicts_passes(self) -> None:
        stdout = io.StringIO()
        with redirect_stdout(stdout):
            rc = checker.check_paths(
                tracked_paths=["Compiler/Main.lean", "scripts/check_paths.py"],
            )
        self.assertEqual(rc, 0)
        self.assertIn("path checks passed", stdout.getvalue())

    def test_case_conflicts_fail(self) -> None:
        stderr = io.StringIO()
        with redirect_stderr(stderr):
            rc = checker.check_paths(
                tracked_paths=["Compiler/Main.lean", "compiler/yul/Foo.yul"],
            )
        self.assertEqual(rc, 1)
        out = stderr.getvalue()
        self.assertIn("path validation failed", out)
        self.assertIn("Compiler  <->  compiler", out)

    def test_main_uses_git_paths_by_default(self) -> None:
        with patch.object(checker, "_git_tracked_paths", return_value=["Compiler/Main.lean"]):
            self.assertEqual(checker.main(), 0)


if __name__ == "__main__":
    unittest.main()
