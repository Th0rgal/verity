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

import check_package_import_boundaries


class CheckPackageImportBoundariesTests(unittest.TestCase):
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
                    'lean_lib «Test» where',
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
        files: dict[str, str],
        *,
        edsl_globs: str = "    .one `Verity.Foo",
        compiler_globs: str = "    .one `Compiler.Foo",
    ) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory() as tempdir_str:
            root = Path(tempdir_str)
            self._write_lakefile(root / "packages" / "verity-edsl" / "lakefile.lean", "verity-edsl", edsl_globs)
            self._write_lakefile(
                root / "packages" / "verity-compiler" / "lakefile.lean", "verity-compiler", compiler_globs
            )

            for rel_path, contents in files.items():
                path = root / rel_path
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(contents, encoding="utf-8")

            boundaries = (
                (
                    root / "packages" / "verity-edsl" / "lakefile.lean",
                    "verity-edsl",
                    "Compiler",
                ),
                (
                    root / "packages" / "verity-compiler" / "lakefile.lean",
                    "verity-compiler",
                    "Contracts",
                ),
            )

            stdout = io.StringIO()
            stderr = io.StringIO()
            with redirect_stdout(stdout), redirect_stderr(stderr):
                rc = check_package_import_boundaries.main_for_boundaries(boundaries, source_root=root)
            return rc, stdout.getvalue(), stderr.getvalue()

    def test_accepts_allowed_package_imports(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Verity/Foo.lean": "import Verity.Bar\n",
                "Compiler/Foo.lean": "import Compiler.Bar\n",
            }
        )
        self.assertEqual(rc, 0)
        self.assertIn("Package import boundary check passed.", stdout)
        self.assertEqual(stderr, "")

    def test_rejects_verity_edsl_importing_compiler(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Verity/Foo.lean": "import Compiler.CompilationModel\n",
                "Compiler/Foo.lean": "import Compiler.Bar\n",
            }
        )
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("forbidden verity-edsl -> Compiler import", stderr)

    def test_rejects_verity_compiler_importing_contracts(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Verity/Foo.lean": "import Verity.Bar\n",
                "Compiler/Foo.lean": "import Contracts.Specs\n",
            }
        )
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("forbidden verity-compiler -> Contracts import", stderr)

    def test_rejects_root_namespace_imports(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Verity/Foo.lean": "import Compiler\n",
                "Compiler/Foo.lean": "import Contracts\n",
            }
        )
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("forbidden verity-edsl -> Compiler import `Compiler`", stderr)
        self.assertIn("forbidden verity-compiler -> Contracts import `Contracts`", stderr)

    def test_ignores_comment_decoys(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Verity/Foo.lean": "-- import Compiler.CompilationModel\nimport Verity.Bar\n",
                "Compiler/Foo.lean": "/- import Contracts.Specs -/\nimport Compiler.Bar\n",
            }
        )
        self.assertEqual(rc, 0)
        self.assertIn("Package import boundary check passed.", stdout)
        self.assertEqual(stderr, "")

    def test_rejects_forbidden_module_from_multi_import_line(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Verity/Foo.lean": "import Verity.Bar Compiler.CompilationModel\n",
                "Compiler/Foo.lean": "import Compiler.Bar Contracts.Specs\n",
            }
        )
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("forbidden verity-edsl -> Compiler import `Compiler.CompilationModel`", stderr)
        self.assertIn("forbidden verity-compiler -> Contracts import `Contracts.Specs`", stderr)

    def test_expands_and_submodules_globs(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Verity/Core.lean": "import Verity.Core.Address\n",
                "Verity/Core/Address.lean": "import Verity.Core.Uint256\n",
                "Compiler/Foo.lean": "import Compiler.Bar\n",
            },
            edsl_globs="    .andSubmodules `Verity.Core",
        )
        self.assertEqual(rc, 0)
        self.assertIn("Package import boundary check passed.", stdout)
        self.assertEqual(stderr, "")

    def test_reports_missing_module_from_lake_glob(self) -> None:
        rc, stdout, stderr = self._run_check(
            {
                "Compiler/Foo.lean": "import Compiler.Bar\n",
            }
        )
        self.assertEqual(rc, 1)
        self.assertEqual(stdout, "")
        self.assertIn("missing module listed in globs", stderr)


if __name__ == "__main__":
    unittest.main()
