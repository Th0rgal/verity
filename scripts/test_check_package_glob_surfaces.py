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

import check_package_glob_surfaces


class CheckPackageGlobSurfacesTests(unittest.TestCase):
    def _write_lakefile(self, path: Path, package_name: str, globs: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            "\n".join(
                [
                    "import Lake",
                    "open Lake DSL",
                    "",
                    f'package «{package_name}» where',
                    '  version := v!"0.1.0"',
                    "",
                    "lean_lib «Test» where",
                    '  srcDir := "../.."',
                    "  globs := #[",
                    globs,
                    "  ]",
                    "",
                ]
            ),
            encoding="utf-8",
        )

    def _run_check(
        self,
        *,
        edsl_globs: str = "    .one `Verity.Core",
        compiler_globs: str = "    .andSubmodules `Compiler",
        examples_globs: str = "    .andSubmodules `Contracts.Counter",
    ) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory() as tempdir_str:
            root = Path(tempdir_str)
            self._write_lakefile(root / "packages" / "verity-edsl" / "lakefile.lean", "verity-edsl", edsl_globs)
            self._write_lakefile(
                root / "packages" / "verity-compiler" / "lakefile.lean", "verity-compiler", compiler_globs
            )
            self._write_lakefile(
                root / "packages" / "verity-examples" / "lakefile.lean", "verity-examples", examples_globs
            )

            surfaces = (
                (root / "packages" / "verity-edsl" / "lakefile.lean", "verity-edsl"),
                (root / "packages" / "verity-compiler" / "lakefile.lean", "verity-compiler"),
                (root / "packages" / "verity-examples" / "lakefile.lean", "verity-examples"),
            )

            stdout = io.StringIO()
            stderr = io.StringIO()
            with redirect_stdout(stdout), redirect_stderr(stderr):
                rc = check_package_glob_surfaces.main_for_surfaces(surfaces)
            return rc, stdout.getvalue(), stderr.getvalue()

    def test_accepts_owned_namespaces_and_bridge_globs(self) -> None:
        rc, stdout, stderr = self._run_check(
            edsl_globs="    .one `Verity.Core",
            compiler_globs="\n".join(
                [
                    "    .andSubmodules `Compiler",
                    "    .one `Verity.Macro",
                    "    .andSubmodules `Verity.Macro",
                    "    .one `Verity.Proofs.Stdlib.Automation",
                    "    .one `Verity.Proofs.Stdlib.MappingAutomation",
                ]
            ),
            examples_globs="    .one `Contracts.Specs",
        )
        self.assertEqual(rc, 0)
        self.assertIn("Package glob surface check passed.", stdout)
        self.assertEqual(stderr, "")

    def test_accepts_compiler_bridge_submodules_glob(self) -> None:
        rc, stdout, stderr = self._run_check(
            compiler_globs="\n".join(
                [
                    "    .andSubmodules `Compiler",
                    "    .submodules `Verity.Macro",
                ]
            )
        )
        self.assertEqual(rc, 0)
        self.assertIn("Package glob surface check passed.", stdout)
        self.assertEqual(stderr, "")

    def test_rejects_edsl_non_verity_glob(self) -> None:
        rc, stdout, stderr = self._run_check(edsl_globs="    .one `Compiler.CompilationModel")
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("unexpected verity-edsl glob .one `Compiler.CompilationModel`", stderr)

    def test_rejects_examples_non_contracts_glob(self) -> None:
        rc, stdout, stderr = self._run_check(examples_globs="    .one `Verity.Macro")
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("unexpected verity-examples glob .one `Verity.Macro`", stderr)

    def test_rejects_compiler_non_bridge_verity_glob(self) -> None:
        rc, stdout, stderr = self._run_check(compiler_globs="    .one `Verity.Core")
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("unexpected verity-compiler glob .one `Verity.Core`", stderr)
        self.assertIn("allowed non-Compiler bridge globs", stderr)

    def test_rejects_compiler_contracts_glob(self) -> None:
        rc, stdout, stderr = self._run_check(compiler_globs="    .one `Contracts.Specs")
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("unexpected verity-compiler glob .one `Contracts.Specs`", stderr)

    def test_ignores_comment_decoys(self) -> None:
        rc, stdout, stderr = self._run_check(
            edsl_globs="    -- .one `Compiler.CompilationModel\n    .one `Verity.Core",
            compiler_globs="    /- .one `Contracts.Specs -/\n    .andSubmodules `Compiler",
            examples_globs="    .one `Contracts.Specs",
        )
        self.assertEqual(rc, 0)
        self.assertIn("Package glob surface check passed.", stdout)
        self.assertEqual(stderr, "")


if __name__ == "__main__":
    unittest.main()
