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


class CheckIssueTemplatesTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent)
        self.root = Path(self.tempdir.name)
        self.templates = self.root / ".github" / "ISSUE_TEMPLATE"
        self.templates.mkdir(parents=True, exist_ok=True)

        self.old_root = check.ROOT
        self.old_default = check.DEFAULT_TEMPLATES_DIR
        check.ROOT = self.root
        check.DEFAULT_TEMPLATES_DIR = self.templates

    def tearDown(self) -> None:
        check.ROOT = self.old_root
        check.DEFAULT_TEMPLATES_DIR = self.old_default
        self.tempdir.cleanup()

    def test_find_log_artifacts_empty_for_clean_template(self) -> None:
        path = self.templates / "clean.yml"
        path.write_text(
            "name: Test\nbody:\n  - type: textarea\n    id: goal\n",
            encoding="utf-8",
        )
        self.assertEqual(check._find_log_artifacts(path), [])

    def test_find_log_artifacts_reports_timestamped_runner_line(self) -> None:
        path = self.templates / "dirty.yml"
        path.write_text(
            "name: Test\n"
            "2026-03-04T16:26:36.0017766Z Current runner version: '2.331.0'\n",
            encoding="utf-8",
        )
        findings = check._find_log_artifacts(path)
        self.assertEqual(len(findings), 1)
        self.assertIn("timestamped runner log line", findings[0])

    def test_check_issue_templates_passes_for_valid_form(self) -> None:
        (self.templates / "valid.yml").write_text(
            """
name: Test Form
description: desc
title: "[Test]: "
labels: [enhancement]
body:
  - type: markdown
    attributes:
      value: hi
""".strip()
            + "\n",
            encoding="utf-8",
        )

        self.assertEqual(check.check_issue_templates(self.templates), 0)

    def test_check_form_rejects_about_and_missing_description(self) -> None:
        path = self.templates / "bad.yml"
        path.write_text(
            """
name: Test Form
about: old key
title: "[Test]: "
labels: [enhancement]
body:
  - type: markdown
    attributes:
      value: hi
""".strip()
            + "\n",
            encoding="utf-8",
        )

        issues = check._check_form(path)
        self.assertIn("missing required key(s): description", issues)
        self.assertIn("disallowed key(s): about", issues)

    def test_check_issue_templates_fails_when_no_forms_exist(self) -> None:
        self.assertEqual(check.check_issue_templates(self.templates), 1)

    def test_check_issue_templates_ignores_config_yml(self) -> None:
        (self.templates / "config.yml").write_text(
            "blank_issues_enabled: false\n",
            encoding="utf-8",
        )
        self.assertEqual(check.check_issue_templates(self.templates), 1)

    def test_check_issue_templates_handles_non_repo_path_on_failure(self) -> None:
        path = self.templates / "bad.yml"
        path.write_text(
            "name: Bad\n",
            encoding="utf-8",
        )
        self.assertEqual(check.check_issue_templates(self.templates), 1)

    def test_main_fails_on_contaminated_template(self) -> None:
        (self.templates / "trust-reduction.yml").write_text(
            """
name: Test
description: desc
title: "[Test]: "
labels: [cleanup]
body:
  - type: markdown
    attributes:
      value: "##[group]Run actions/checkout@v4"
""".strip()
            + "\n",
            encoding="utf-8",
        )

        old_argv = sys.argv
        sys.argv = ["check_issue_templates.py"]
        try:
            stderr = io.StringIO()
            with redirect_stderr(stderr):
                rc = check.main()
        finally:
            sys.argv = old_argv

        self.assertEqual(rc, 1)
        self.assertIn("validation failed", stderr.getvalue())

    def test_main_passes_on_clean_templates(self) -> None:
        (self.templates / "compiler-enhancement.yml").write_text(
            """
name: Compiler Enhancement
description: Propose a feature.
title: "[Compiler]: "
labels: [enhancement]
body:
  - type: textarea
    id: goal
""".strip()
            + "\n",
            encoding="utf-8",
        )

        old_argv = sys.argv
        sys.argv = ["check_issue_templates.py"]
        try:
            stdout = io.StringIO()
            with redirect_stdout(stdout):
                rc = check.main()
        finally:
            sys.argv = old_argv

        self.assertEqual(rc, 0)
        self.assertIn("issue templates OK", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
