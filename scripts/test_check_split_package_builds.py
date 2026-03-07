#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_split_package_builds as check


class CheckSplitPackageBuildsTests(unittest.TestCase):
    def test_parse_args_accepts_multiple_packages(self) -> None:
        args = check.parse_args(["--package", "packages/a", "--package", "packages/b"])
        self.assertEqual(args.packages, ["packages/a", "packages/b"])

    def test_resolve_packages_defaults_to_all_split_packages(self) -> None:
        resolved = check.resolve_packages([])
        self.assertEqual(
            resolved,
            [check.ROOT / rel_path for rel_path in check.DEFAULT_PACKAGES],
        )

    def test_check_split_package_builds_passes_when_all_builds_succeed(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tmpdir:
            root = Path(tmpdir)
            packages = [root / "packages" / "verity-edsl", root / "packages" / "verity-compiler"]
            for package_dir in packages:
                package_dir.mkdir(parents=True, exist_ok=True)

            with patch.object(check, "ROOT", root):
                with patch.object(check, "run_lake_build") as run_lake_build:
                    run_lake_build.side_effect = [
                        check.subprocess.CompletedProcess(["lake", "build"], 0, "", ""),
                        check.subprocess.CompletedProcess(["lake", "build"], 0, "", ""),
                    ]
                    stdout = io.StringIO()
                    stderr = io.StringIO()
                    with redirect_stdout(stdout), redirect_stderr(stderr):
                        rc = check.check_split_package_builds(packages)

        self.assertEqual(rc, 0)
        self.assertIn("Split package build check passed (2 package(s)).", stdout.getvalue())
        self.assertEqual(stderr.getvalue(), "")

    def test_check_split_package_builds_reports_missing_directory(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tmpdir:
            root = Path(tmpdir)
            missing = root / "packages" / "verity-edsl"

            with patch.object(check, "ROOT", root):
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check.check_split_package_builds([missing])

        self.assertEqual(rc, 1)
        self.assertEqual(stdout.getvalue(), "")
        self.assertIn("package directory does not exist", stderr.getvalue())

    def test_check_split_package_builds_reports_failing_build_output(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tmpdir:
            root = Path(tmpdir)
            package_dir = root / "packages" / "verity-edsl"
            package_dir.mkdir(parents=True, exist_ok=True)

            with patch.object(check, "ROOT", root):
                with patch.object(check, "run_lake_build") as run_lake_build:
                    run_lake_build.return_value = check.subprocess.CompletedProcess(
                        ["lake", "build"],
                        1,
                        "stdout details\n",
                        "stderr details\n",
                    )
                    stdout = io.StringIO()
                    stderr = io.StringIO()
                    with redirect_stdout(stdout), redirect_stderr(stderr):
                        rc = check.check_split_package_builds([package_dir])

        self.assertEqual(rc, 1)
        self.assertIn("Building packages/verity-edsl...", stdout.getvalue())
        self.assertIn("lake build failed with exit code 1", stderr.getvalue())
        self.assertIn("stdout details", stderr.getvalue())
        self.assertIn("stderr details", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
