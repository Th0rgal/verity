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

import check_compilationmodel_split as checker


class CheckCompilationModelSplitTests(unittest.TestCase):
    def _make_layout(
        self,
        tempdir: Path,
        *,
        facade_text: str,
        submodules: tuple[str, ...] = ("Types", "Compile"),
    ) -> tuple[Path, Path]:
        compiler_dir = tempdir / "Compiler"
        module_dir = compiler_dir / "CompilationModel"
        module_dir.mkdir(parents=True)
        for name in submodules:
            module_path = module_dir / Path(*name.split("."))
            module_path.parent.mkdir(parents=True, exist_ok=True)
            module_path.with_suffix(".lean").write_text("-- stub\n", encoding="utf-8")
        facade = compiler_dir / "CompilationModel.lean"
        facade.write_text(facade_text, encoding="utf-8")
        return facade, module_dir

    def test_passes_for_pure_facade(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir_str:
            tempdir = Path(tempdir_str)
            facade, module_dir = self._make_layout(
                tempdir,
                facade_text=(
                    "/- facade -/\n"
                    "import Compiler.CompilationModel.Types\n"
                    "import Compiler.CompilationModel.Compile\n"
                ),
            )
            stdout = io.StringIO()
            with redirect_stdout(stdout):
                rc = checker.check_compilationmodel_split(facade=facade, submodule_dir=module_dir)
        self.assertEqual(rc, 0)
        self.assertIn("CompilationModel split check passed", stdout.getvalue())

    def test_rejects_over_budget_facade(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir_str:
            tempdir = Path(tempdir_str)
            facade, module_dir = self._make_layout(
                tempdir,
                facade_text="\n".join(
                    ["import Compiler.CompilationModel.Types"] * 5
                )
                + "\n",
            )
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                rc = checker.check_compilationmodel_split(
                    facade=facade,
                    submodule_dir=module_dir,
                    max_facade_lines=3,
                )
        self.assertEqual(rc, 1)
        self.assertIn("expected at most 3 lines, found 5", stderr.getvalue())

    def test_rejects_non_import_statement(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir_str:
            tempdir = Path(tempdir_str)
            facade, module_dir = self._make_layout(
                tempdir,
                facade_text=(
                    "import Compiler.CompilationModel.Types\n"
                    "def leakedImplementation := 1\n"
                    "import Compiler.CompilationModel.Compile\n"
                ),
            )
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                rc = checker.check_compilationmodel_split(facade=facade, submodule_dir=module_dir)
        self.assertEqual(rc, 1)
        self.assertIn("facade should contain only imports/comments", stderr.getvalue())

    def test_rejects_missing_submodule_import(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir_str:
            tempdir = Path(tempdir_str)
            facade, module_dir = self._make_layout(
                tempdir,
                facade_text="import Compiler.CompilationModel.Types\n",
            )
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                rc = checker.check_compilationmodel_split(facade=facade, submodule_dir=module_dir)
        self.assertEqual(rc, 1)
        self.assertIn("missing Compiler.CompilationModel.Compile", stderr.getvalue())

    def test_rejects_unexpected_import_namespace(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir_str:
            tempdir = Path(tempdir_str)
            facade, module_dir = self._make_layout(
                tempdir,
                facade_text=(
                    "import Compiler.CompilationModel.Types\n"
                    "import Compiler.Other\n"
                    "import Compiler.CompilationModel.Compile\n"
                ),
            )
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                rc = checker.check_compilationmodel_split(facade=facade, submodule_dir=module_dir)
        self.assertEqual(rc, 1)
        self.assertIn("unexpected Compiler.Other", stderr.getvalue())

    def test_requires_nested_submodule_imports(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tempdir_str:
            tempdir = Path(tempdir_str)
            facade, module_dir = self._make_layout(
                tempdir,
                facade_text=(
                    "import Compiler.CompilationModel.Types\n"
                    "import Compiler.CompilationModel.Deep.Walker\n"
                ),
                submodules=("Types", "Deep.Walker"),
            )
            stdout = io.StringIO()
            with redirect_stdout(stdout):
                rc = checker.check_compilationmodel_split(facade=facade, submodule_dir=module_dir)
        self.assertEqual(rc, 0)
        self.assertIn("CompilationModel split check passed", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
