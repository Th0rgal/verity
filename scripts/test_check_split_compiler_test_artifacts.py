#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_split_compiler_test_artifacts as check


class CheckSplitCompilerTestArtifactsTests(unittest.TestCase):
    def _write_lakefile(self, path: Path, globs: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            "\n".join(
                [
                    "import Lake",
                    "open Lake DSL",
                    "",
                    'package «verity-compiler» where',
                    '  version := v!"0.1.0"',
                    "",
                    "lean_lib «Compiler» where",
                    '  srcDir := "../.."',
                    "  globs := #[",
                    globs,
                    "  ]",
                    "",
                ]
            ),
            encoding="utf-8",
        )

    def _run_check(self, lakefile: Path) -> tuple[int, str, str]:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = check.main(["--lakefile", str(lakefile)])
        return rc, stdout.getvalue(), stderr.getvalue()

    def test_passes_when_compiler_submodules_are_exported(self) -> None:
        with tempfile.TemporaryDirectory() as tempdir_str:
            root = Path(tempdir_str)
            lakefile = root / "packages" / "verity-compiler" / "lakefile.lean"
            self._write_lakefile(lakefile, "    .andSubmodules `Compiler")
            rc, stdout, stderr = self._run_check(lakefile)
        self.assertEqual(rc, 0)
        self.assertIn("Split compiler test module coverage check passed", stdout)
        self.assertEqual(stderr, "")

    def test_fails_when_lakefile_is_missing(self) -> None:
        with tempfile.TemporaryDirectory() as tempdir_str:
            lakefile = Path(tempdir_str) / "missing" / "lakefile.lean"
            rc, stdout, stderr = self._run_check(lakefile)
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("missing lakefile", stderr)

    def test_fails_when_compiler_test_modules_are_not_covered(self) -> None:
        with tempfile.TemporaryDirectory() as tempdir_str:
            root = Path(tempdir_str)
            lakefile = root / "packages" / "verity-compiler" / "lakefile.lean"
            self._write_lakefile(lakefile, "    .one `Compiler.Main")
            rc, stdout, stderr = self._run_check(lakefile)
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("Compiler.MainTest", stderr)


if __name__ == "__main__":
    unittest.main()
