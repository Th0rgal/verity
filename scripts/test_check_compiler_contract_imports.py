#!/usr/bin/env python3
from __future__ import annotations

import io
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

import check_compiler_contract_imports


class CheckCompilerContractImportsTests(unittest.TestCase):
    def _run_check(self, files: dict[str, str]) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory() as tempdir_str:
            root = Path(tempdir_str)
            compiler_dir = root / "Compiler"
            compiler_dir.mkdir(parents=True)
            for rel_path, contents in files.items():
                path = root / rel_path
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(contents, encoding="utf-8")

            stdout = io.StringIO()
            stderr = io.StringIO()
            with redirect_stdout(stdout), redirect_stderr(stderr):
                rc = check_compiler_contract_imports.main_for_root(compiler_dir)  # type: ignore[attr-defined]
            return rc, stdout.getvalue(), stderr.getvalue()

    def test_accepts_compiler_only_imports(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Compiler/Foo.lean": "import Compiler.Bar\n",
            }
        )
        self.assertEqual(rc, 0)
        self.assertIn("boundary check passed", stdout)
        self.assertEqual(stderr, "")

    def test_rejects_contract_import(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Compiler/Foo.lean": "import Contracts.Specs\n",
            }
        )
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("forbidden Compiler -> Contracts import", stderr)

    def test_ignores_comment_decoy(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Compiler/Foo.lean": "-- import Contracts.Specs\nimport Compiler.Bar\n",
            }
        )
        self.assertEqual(rc, 0)
        self.assertIn("boundary check passed", stdout)
        self.assertEqual(stderr, "")


if __name__ == "__main__":
    unittest.main()
