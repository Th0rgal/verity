#!/usr/bin/env python3
from __future__ import annotations

import argparse
import io
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_yul
import property_utils


class YulChecksTests(unittest.TestCase):
    def _run_boundary_check(self, ir_body: str, sem_body: str) -> list[str]:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            root = Path(tmpdir)
            proofs = root / "Compiler" / "Proofs"
            builtins = proofs / "YulGeneration" / "Builtins.lean"
            ir = proofs / "IRGeneration" / "IRInterpreter.lean"
            sem = proofs / "YulGeneration" / "Semantics.lean"
            builtins.parent.mkdir(parents=True, exist_ok=True)
            ir.parent.mkdir(parents=True, exist_ok=True)
            sem.parent.mkdir(parents=True, exist_ok=True)

            builtins.write_text("-- builtin boundary module\n", encoding="utf-8")
            ir.write_text(ir_body, encoding="utf-8")
            sem.write_text(sem_body, encoding="utf-8")

            old_root = check_yul.ROOT
            old_proofs = check_yul.PROOFS_DIR
            old_builtins = check_yul.BUILTINS_FILE
            old_runtime = check_yul.RUNTIME_INTERPRETERS
            check_yul.ROOT = root
            check_yul.PROOFS_DIR = proofs
            check_yul.BUILTINS_FILE = builtins
            check_yul.RUNTIME_INTERPRETERS = [ir, sem]
            try:
                return check_yul.collect_builtin_boundary_failures()
            finally:
                check_yul.ROOT = old_root
                check_yul.PROOFS_DIR = old_proofs
                check_yul.BUILTINS_FILE = old_builtins
                check_yul.RUNTIME_INTERPRETERS = old_runtime

    def test_comment_only_decoy_does_not_satisfy_boundary(self) -> None:
        body = """import Compiler.Proofs.YulGeneration.Builtins
-- decoy only: Compiler.Proofs.YulGeneration.evalBuiltinCall
def evalExpr := 0
"""
        failures = self._run_boundary_check(body, body)
        self.assertTrue(any("missing call" in failure for failure in failures))

    def test_string_literal_decoy_does_not_satisfy_boundary(self) -> None:
        body = """import Compiler.Proofs.YulGeneration.Builtins
def evalExpr := "Compiler.Proofs.YulGeneration.evalBuiltinCall"
"""
        failures = self._run_boundary_check(body, body)
        self.assertTrue(any("missing call" in failure for failure in failures))

    def test_eval_builtin_call_with_backend_satisfies_boundary(self) -> None:
        body = """import Compiler.Proofs.YulGeneration.Builtins
def evalExpr :=
  Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackend
"""
        failures = self._run_boundary_check(body, body)
        self.assertEqual(failures, [])

    def test_eval_builtin_call_with_backend_context_satisfies_boundary(self) -> None:
        body = """import Compiler.Proofs.YulGeneration.Builtins
def evalExpr :=
  Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext
"""
        failures = self._run_boundary_check(body, body)
        self.assertEqual(failures, [])

    def test_inline_dispatch_regex_covers_env_builtins(self) -> None:
        self.assertIsNotNone(check_yul.INLINE_DISPATCH_RE.search('func = "address"'))
        self.assertIsNotNone(check_yul.INLINE_DISPATCH_RE.search('func = "timestamp"'))

    def test_run_compilation_checks_reports_same_file_pair_mismatch(self) -> None:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            root = Path(tmpdir)
            dir_a = root / "a"
            dir_b = root / "b"
            dir_a.mkdir()
            dir_b.mkdir()
            (dir_a / "One.yul").write_text("{ }", encoding="utf-8")
            (dir_b / "Two.yul").write_text("{ }", encoding="utf-8")

            old_root = check_yul.ROOT
            old_run_solc = check_yul.run_solc
            check_yul.ROOT = root
            check_yul.run_solc = lambda _path: (0, "Binary representation:\n00\n", "")
            try:
                args = argparse.Namespace(
                    dirs=["a"],
                    compare_dirs=None,
                    same_file_pairs=[["a", "b"]],
                    allow_compare_diff_file=None,
                )
                failures, checked_files, compare_count = check_yul.run_compilation_checks(args)
            finally:
                check_yul.ROOT = old_root
                check_yul.run_solc = old_run_solc

        self.assertEqual(checked_files, 1)
        self.assertEqual(compare_count, 1)
        self.assertIn(f"{dir_b} missing file present in {dir_a}: One.yul", failures)
        self.assertIn(f"{dir_a} missing file present in {dir_b}: Two.yul", failures)

    def test_run_compilation_checks_defaults_to_artifacts_yul(self) -> None:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            root = Path(tmpdir)
            artifacts_yul = root / "artifacts" / "yul"
            artifacts_yul.mkdir(parents=True)
            (artifacts_yul / "One.yul").write_text("{ }", encoding="utf-8")

            old_root = check_yul.ROOT
            old_default_yul_dir = check_yul.DEFAULT_YUL_DIR
            old_run_solc = check_yul.run_solc
            check_yul.ROOT = root
            check_yul.DEFAULT_YUL_DIR = root / "artifacts" / "yul"
            check_yul.run_solc = lambda _path: (0, "Binary representation:\n00\n", "")
            try:
                args = argparse.Namespace(
                    dirs=None,
                    compare_dirs=None,
                    same_file_pairs=None,
                    allow_compare_diff_file=None,
                )
                failures, checked_files, compare_count = check_yul.run_compilation_checks(args)
            finally:
                check_yul.ROOT = old_root
                check_yul.DEFAULT_YUL_DIR = old_default_yul_dir
                check_yul.run_solc = old_run_solc

        self.assertEqual(failures, [])
        self.assertEqual(checked_files, 1)
        self.assertEqual(compare_count, 0)

    def test_main_builtin_boundary_only_skips_solc_checks(self) -> None:
        old_collect = check_yul.collect_builtin_boundary_failures
        old_run_compilation = check_yul.run_compilation_checks
        check_yul.collect_builtin_boundary_failures = lambda: []
        called = {"compile": False}

        def _unexpected_compile(_args: argparse.Namespace) -> tuple[list[str], int, int]:
            called["compile"] = True
            return [], 0, 0

        check_yul.run_compilation_checks = _unexpected_compile
        try:
            stdout = io.StringIO()
            with redirect_stdout(stdout):
                check_yul.main(["--builtin-boundary-only"])
        finally:
            check_yul.collect_builtin_boundary_failures = old_collect
            check_yul.run_compilation_checks = old_run_compilation

        self.assertFalse(called["compile"])
        self.assertIn("builtin boundary is enforced", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
