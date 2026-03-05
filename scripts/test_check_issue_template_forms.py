#!/usr/bin/env python3
from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import check_issue_template_forms as check


class CheckIssueTemplateFormsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        self.forms_dir = self.root / ".github" / "ISSUE_TEMPLATE"
        self.forms_dir.mkdir(parents=True, exist_ok=True)

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def test_passes_for_valid_form(self) -> None:
        (self.forms_dir / "valid.yml").write_text(
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

        self.assertEqual(check.check_issue_template_forms(self.forms_dir), 0)

    def test_rejects_about_and_missing_description(self) -> None:
        path = self.forms_dir / "bad.yml"
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

    def test_fails_when_no_forms_exist(self) -> None:
        self.assertEqual(check.check_issue_template_forms(self.forms_dir), 1)

    def test_ignores_config_yml(self) -> None:
        (self.forms_dir / "config.yml").write_text(
            "blank_issues_enabled: false\n",
            encoding="utf-8",
        )
        self.assertEqual(check.check_issue_template_forms(self.forms_dir), 1)

    def test_handles_non_repo_path_on_failure(self) -> None:
        path = self.forms_dir / "bad.yml"
        path.write_text(
            "name: Bad\n",
            encoding="utf-8",
        )
        self.assertEqual(check.check_issue_template_forms(self.forms_dir), 1)


if __name__ == "__main__":
    unittest.main()
