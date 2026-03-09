#!/usr/bin/env python3
from __future__ import annotations

import io
import json
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_verify_sync as check


class VerifySyncTests(unittest.TestCase):
    def _run_jobs_check(self, workflow_text: str, expected_jobs: list[str]) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            verify = root / "verify.yml"
            spec = root / "verify_sync_spec.json"
            verify.write_text(workflow_text, encoding="utf-8")
            spec.write_text(json.dumps({"expected_jobs": expected_jobs}), encoding="utf-8")

            old_verify = check.VERIFY_YML
            old_spec = check.SPEC_PATH
            check.VERIFY_YML = verify
            check.SPEC_PATH = spec
            old_argv = sys.argv
            sys.argv = ["check_verify_sync.py", "--only", "jobs"]
            try:
                stderr = io.StringIO()
                stdout = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(stdout):
                    rc = check.main()
                return rc, stdout.getvalue(), stderr.getvalue()
            finally:
                check.VERIFY_YML = old_verify
                check.SPEC_PATH = old_spec
                sys.argv = old_argv

    def _run_paths_check(
        self,
        workflow_text: str,
        *,
        check_only_paths: list[str],
        compiler_paths: list[str],
    ) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            verify = root / "verify.yml"
            spec = root / "verify_sync_spec.json"
            verify.write_text(workflow_text, encoding="utf-8")
            spec.write_text(
                json.dumps(
                    {
                        "check_only_paths": check_only_paths,
                        "compiler_paths": compiler_paths,
                    }
                ),
                encoding="utf-8",
            )

            old_verify = check.VERIFY_YML
            old_spec = check.SPEC_PATH
            check.VERIFY_YML = verify
            check.SPEC_PATH = spec
            old_argv = sys.argv
            sys.argv = ["check_verify_sync.py", "--only", "paths"]
            try:
                stderr = io.StringIO()
                stdout = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(stdout):
                    rc = check.main()
                return rc, stdout.getvalue(), stderr.getvalue()
            finally:
                check.VERIFY_YML = old_verify
                check.SPEC_PATH = old_spec
                sys.argv = old_argv

    def _run_makefile_check(
        self,
        makefile_text: str,
        *,
        expected_checks_commands: list[str],
        required_makefile_check_commands: list[str] | None = None,
        expected_checks_other_commands: list[str] | None = None,
    ) -> tuple[int, str, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            verify = root / "verify.yml"
            spec = root / "verify_sync_spec.json"
            makefile = root / "Makefile"
            verify.write_text("name: verify\njobs:\n  checks:\n    runs-on: ubuntu-latest\n    steps: []\n", encoding="utf-8")
            makefile.write_text(textwrap.dedent(makefile_text).lstrip(), encoding="utf-8")
            spec.write_text(
                json.dumps(
                    {
                        "expected_checks_commands": expected_checks_commands,
                        "required_makefile_check_commands": required_makefile_check_commands or [],
                        "expected_checks_other_commands": expected_checks_other_commands or [],
                    }
                ),
                encoding="utf-8",
            )

            old_verify = check.VERIFY_YML
            old_spec = check.SPEC_PATH
            old_makefile = check.MAKEFILE
            check.VERIFY_YML = verify
            check.SPEC_PATH = spec
            check.MAKEFILE = makefile
            old_argv = sys.argv
            sys.argv = ["check_verify_sync.py", "--only", "makefile"]
            try:
                stderr = io.StringIO()
                stdout = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(stdout):
                    rc = check.main()
                return rc, stdout.getvalue(), stderr.getvalue()
            finally:
                check.VERIFY_YML = old_verify
                check.SPEC_PATH = old_spec
                check.MAKEFILE = old_makefile
                sys.argv = old_argv

    def test_jobs_check_passes_when_order_matches(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps: []
              checks:
                runs-on: ubuntu-latest
                steps: []
            """
        )
        rc, out, err = self._run_jobs_check(workflow, ["changes", "checks"])
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] jobs", out)

    def test_jobs_check_fails_when_order_drifts(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            jobs:
              checks:
                runs-on: ubuntu-latest
                steps: []
              changes:
                runs-on: ubuntu-latest
                steps: []
            """
        )
        rc, _, err = self._run_jobs_check(workflow, ["changes", "checks"])
        self.assertEqual(rc, 1)
        self.assertIn("[FAIL] jobs", err)

    def test_paths_check_fails_when_check_only_path_is_missing_from_triggers(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - 'docs/**'
                  - 'README.md'
                  - 'Compiler/**'
              pull_request:
                paths:
                  - 'docs/**'
                  - 'README.md'
                  - 'Compiler/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - 'Compiler/**'
                        compiler:
                          - 'Compiler/**'
            """
        )
        rc, _, err = self._run_paths_check(
            workflow,
            check_only_paths=["docs/**", "README.md", "AUDIT.md"],
            compiler_paths=["Compiler/**"],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "check_only_paths includes entries missing from on.push.paths: AUDIT.md",
            err,
        )

    def test_paths_check_fails_when_workflow_glob_is_missing_from_triggers(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
              pull_request:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
                        compiler:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
            """
        )
        rc, _, err = self._run_paths_check(
            workflow,
            check_only_paths=[".github/workflows/**"],
            compiler_paths=[".github/workflows/verify.yml", "scripts/**"],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "check_only_paths includes entries missing from on.push.paths: .github/workflows/**",
            err,
        )

    def test_paths_check_fails_when_artifacts_are_missing_from_triggers(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
              pull_request:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
                        compiler:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
            """
        )
        rc, _, err = self._run_paths_check(
            workflow,
            check_only_paths=["artifacts/**"],
            compiler_paths=[".github/workflows/verify.yml", "scripts/**"],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "check_only_paths includes entries missing from on.push.paths: artifacts/**",
            err,
        )

    def test_paths_check_fails_when_artifacts_are_missing_from_triggers(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
              pull_request:
                paths:
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
                        compiler:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
            """
        )
        rc, _, err = self._run_paths_check(
            workflow,
            check_only_paths=["artifacts/**"],
            compiler_paths=[".github/workflows/verify.yml", "scripts/**"],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "check_only_paths includes entries missing from on.push.paths: artifacts/**",
            err,
        )

    def test_paths_check_passes_with_workflow_wildcard_and_explicit_verify_filters(self) -> None:
        workflow = textwrap.dedent(
            """
            name: verify
            on:
              push:
                paths:
                  - '.github/workflows/**'
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
              pull_request:
                paths:
                  - '.github/workflows/**'
                  - '.github/workflows/verify.yml'
                  - 'scripts/**'
            jobs:
              changes:
                runs-on: ubuntu-latest
                steps:
                  - uses: dorny/paths-filter@v3
                    with:
                      filters: |
                        code:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
                        compiler:
                          - '.github/workflows/verify.yml'
                          - 'scripts/**'
            """
        )
        rc, out, err = self._run_paths_check(
            workflow,
            check_only_paths=[".github/workflows/**"],
            compiler_paths=[".github/workflows/verify.yml", "scripts/**"],
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] paths", out)

    def test_makefile_check_fails_when_required_unit_test_command_is_missing(self) -> None:
        rc, _, err = self._run_makefile_check(
            """
            check:
            	python3 scripts/check_verify_sync.py
            	python3 scripts/check_issue_templates.py
            	python3 scripts/check_docs_workflow_sync.py
            """,
            expected_checks_commands=["make check"],
            required_makefile_check_commands=[
                "python3 scripts/check_verify_sync.py",
                "python3 scripts/check_issue_templates.py",
                "python3 scripts/check_docs_workflow_sync.py",
                "python3 -m unittest discover -s scripts -p 'test_*.py' -v",
            ],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "Makefile check target is missing required commands: "
            "python3 -m unittest discover -s scripts -p 'test_*.py' -v",
            err,
        )

    def test_makefile_check_passes_when_required_commands_are_present(self) -> None:
        makefile = """
        check:
        \tpython3 scripts/check_verify_sync.py
        \tpython3 scripts/check_issue_templates.py
        \tpython3 scripts/check_docs_workflow_sync.py
        \tpython3 -m unittest discover -s scripts -p 'test_*.py' -v
        """
        rc, out, err = self._run_makefile_check(
            makefile,
            expected_checks_commands=["make check"],
            required_makefile_check_commands=[
                "python3 scripts/check_verify_sync.py",
                "python3 scripts/check_issue_templates.py",
                "python3 scripts/check_docs_workflow_sync.py",
            ],
        )
        self.assertEqual(rc, 0, err)
        self.assertIn("[PASS] makefile", out)

    def test_makefile_check_fails_when_required_command_is_missing(self) -> None:
        makefile = """
        check:
        \tpython3 scripts/check_verify_sync.py
        \tpython3 scripts/check_issue_templates.py
        """
        rc, _, err = self._run_makefile_check(
            makefile,
            expected_checks_commands=["make check"],
            required_makefile_check_commands=[
                "python3 scripts/check_verify_sync.py",
                "python3 scripts/check_issue_templates.py",
                "python3 scripts/check_docs_workflow_sync.py",
            ],
        )
        self.assertEqual(rc, 1)
        self.assertIn(
            "Makefile check target is missing required commands: python3 scripts/check_docs_workflow_sync.py",
            err,
        )


if __name__ == "__main__":
    unittest.main()
