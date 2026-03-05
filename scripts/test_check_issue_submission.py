#!/usr/bin/env python3
from __future__ import annotations

import unittest

import check_issue_submission as check


class CheckIssueSubmissionTests(unittest.TestCase):
    def test_detects_template_title_and_body_placeholders(self) -> None:
        findings = check.detect_invalid_issue(
            "[Compiler Enhancement]",
            "## Goal\n<What compiler feature or improvement>\n",
        )
        self.assertTrue(any("title matches" in finding for finding in findings))
        self.assertTrue(any("unresolved template placeholders" in finding for finding in findings))

    def test_detects_ci_log_dump(self) -> None:
        findings = check.detect_invalid_issue(
            "Build canceled",
            "2026-03-04T16:26:36.0017766Z Current runner version: '2.331.0'",
        )
        self.assertTrue(any("CI/GitHub Actions logs" in finding for finding in findings))

    def test_accepts_filled_issue(self) -> None:
        findings = check.detect_invalid_issue(
            "Compiler: tuple return lowering mismatch",
            "\n".join(
                [
                    "Goal: support tuple return values in branch lowering.",
                    "Motivation: enables ABI-compatible wrappers.",
                    "Solution: add tuple expansion in IR lowering and update codegen tests.",
                ]
            ),
        )
        self.assertEqual(findings, [])

    def test_accepts_single_timestamp_reference(self) -> None:
        findings = check.detect_invalid_issue(
            "Compiler: regression on 0.8.33",
            "Observed since 2026-03-04T16:26:36 in nightly build; no CI logs attached.",
        )
        self.assertEqual(findings, [])

if __name__ == "__main__":
    unittest.main()
