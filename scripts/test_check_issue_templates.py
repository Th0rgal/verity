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

import check_issue_templates as check


class IssueTemplateContaminationTests(unittest.TestCase):
    def test_find_log_artifacts_empty_for_clean_template(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            path = Path(td) / "clean.yml"
            path.write_text(
                "name: Test\nbody:\n  - type: textarea\n    id: goal\n",
                encoding="utf-8",
            )
            self.assertEqual(check._find_log_artifacts(path), [])

    def test_find_log_artifacts_reports_timestamped_runner_line(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            path = Path(td) / "dirty.yml"
            path.write_text(
                "name: Test\n"
                "2026-03-04T16:26:36.0017766Z Current runner version: '2.331.0'\n",
                encoding="utf-8",
            )
            findings = check._find_log_artifacts(path)
            self.assertEqual(len(findings), 1)
            self.assertIn("timestamped runner log line", findings[0])

    def test_main_fails_on_contaminated_template(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            templates = root / ".github" / "ISSUE_TEMPLATE"
            templates.mkdir(parents=True, exist_ok=True)
            (templates / "trust-reduction.yml").write_text(
                "name: Test\n##[group]Run actions/checkout@v4\n",
                encoding="utf-8",
            )

            old_root = check.ROOT
            old_default = check.DEFAULT_TEMPLATES_DIR
            old_argv = sys.argv
            check.ROOT = root
            check.DEFAULT_TEMPLATES_DIR = templates
            sys.argv = ["check_issue_templates.py"]
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    rc = check.main()
            finally:
                check.ROOT = old_root
                check.DEFAULT_TEMPLATES_DIR = old_default
                sys.argv = old_argv

            self.assertEqual(rc, 1)
            self.assertIn("contamination check failed", stderr.getvalue())

    def test_main_passes_on_clean_templates(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as td:
            root = Path(td)
            templates = root / ".github" / "ISSUE_TEMPLATE"
            templates.mkdir(parents=True, exist_ok=True)
            (templates / "compiler-enhancement.yml").write_text(
                "name: Compiler Enhancement\ndescription: Propose a feature.\n",
                encoding="utf-8",
            )

            old_root = check.ROOT
            old_default = check.DEFAULT_TEMPLATES_DIR
            old_argv = sys.argv
            check.ROOT = root
            check.DEFAULT_TEMPLATES_DIR = templates
            sys.argv = ["check_issue_templates.py"]
            try:
                stdout = io.StringIO()
                with redirect_stdout(stdout):
                    rc = check.main()
            finally:
                check.ROOT = old_root
                check.DEFAULT_TEMPLATES_DIR = old_default
                sys.argv = old_argv

            self.assertEqual(rc, 0)
            self.assertIn("check passed", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
