#!/usr/bin/env python3
from __future__ import annotations

import io
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_axioms


class CheckAxiomsLocationTests(unittest.TestCase):
    def test_parse_axiom_entries(self) -> None:
        text = (
            "### 1. `a1`\n\n"
            "**Location**: `Compiler/Foo.lean:12`\n\n"
            "### 2. `a2` (private)\n\n"
            "**Location**: `Verity/Bar.lean:34`\n"
        )
        self.assertEqual(
            check_axioms.parse_axiom_entries(text),
            [("a1", "Compiler/Foo.lean", 12), ("a2", "Verity/Bar.lean", 34)],
        )

    def test_parse_active_axiom_count(self) -> None:
        self.assertEqual(check_axioms.parse_active_axiom_count("- Active axioms: 2\n"), 2)
        self.assertIsNone(check_axioms.parse_active_axiom_count("no summary line"))

    def test_discover_repo_axioms_ignores_comments_and_strings(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Verity").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "A.lean").write_text(
                "\n".join(
                    [
                        "-- axiom commented_out : True",
                        "/- axiom in_block_comment : True -/",
                        'def s := "axiom in_string"',
                        "axiom real_axiom : True",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )

            old_root = check_axioms.ROOT
            try:
                check_axioms.ROOT = root
                discovered = check_axioms.discover_repo_axioms()
            finally:
                check_axioms.ROOT = old_root

        self.assertEqual(discovered, {"real_axiom": ("Compiler/A.lean", 4)})

    def test_main_reports_missing_registry_entries_and_count_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Verity").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "A.lean").write_text(
                "axiom documented_axiom : True\naxiom missing_axiom : True\n",
                encoding="utf-8",
            )
            (root / "AXIOMS.md").write_text(
                "\n".join(
                    [
                        "### 1. `documented_axiom`",
                        "",
                        "**Location**: `Compiler/A.lean:1`",
                        "",
                        "## Trust Summary",
                        "",
                        "- Active axioms: 1",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )

            stderr = io.StringIO()
            old_root = check_axioms.ROOT
            try:
                check_axioms.ROOT = root
                with redirect_stderr(stderr), self.assertRaises(SystemExit):
                    check_axioms.main([])
            finally:
                check_axioms.ROOT = old_root

        err = stderr.getvalue()
        self.assertIn("missing_axiom: declared in Compiler/A.lean:2 but missing from AXIOMS.md", err)
        self.assertIn("AXIOMS.md trust summary says Active axioms: 1, but source has 2", err)


class CheckAxiomsReportTests(unittest.TestCase):
    def test_parse_axiom_output(self) -> None:
        text = (
            "'Foo.bar' depends on axioms: [propext, keccak256_first_4_bytes]\n"
            "'Baz.qux' does not depend on any axioms\n"
        )
        self.assertEqual(
            check_axioms.parse_axiom_output(text),
            {
                "Foo.bar": ["propext", "keccak256_first_4_bytes"],
                "Baz.qux": [],
            },
        )

    def test_classify_axioms_separates_forbidden_and_unexpected(self) -> None:
        axiom_map = {
            "Foo.bar": ["propext", "keccak256_first_4_bytes", "mysteryAx"],
            "Baz.qux": ["sorryAx"],
        }
        builtin, documented, forbidden, unexpected = check_axioms.classify_axioms(axiom_map)
        self.assertEqual(builtin, {"propext"})
        self.assertEqual(documented, {"keccak256_first_4_bytes"})
        self.assertEqual(forbidden, {"sorryAx"})
        self.assertEqual(unexpected, {"mysteryAx": ["Foo.bar"]})

    def test_run_report_check_passes_and_writes_output_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            output = Path(tmpdir) / "axiom-report.md"
            old_output = os.environ.get("AXIOM_REPORT_FILE")
            os.environ["AXIOM_REPORT_FILE"] = str(output)
            stdout = io.StringIO()
            stderr = io.StringIO()
            try:
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check_axioms.run_report_check(
                        "'Foo.bar' depends on axioms: [propext, keccak256_first_4_bytes]\n"
                    )
            finally:
                if old_output is None:
                    os.environ.pop("AXIOM_REPORT_FILE", None)
                else:
                    os.environ["AXIOM_REPORT_FILE"] = old_output

            self.assertEqual(rc, 0)
            self.assertIn("## Result: PASS", stdout.getvalue())
            self.assertIn("Report written to", stderr.getvalue())
            self.assertTrue(output.exists())

    def test_run_report_check_fails_on_unexpected_axioms(self) -> None:
        stdout = io.StringIO()
        with redirect_stdout(stdout):
            rc = check_axioms.run_report_check("'Foo.bar' depends on axioms: [mysteryAx]\n")
        self.assertEqual(rc, 1)
        self.assertIn("## Result: FAIL", stdout.getvalue())
        self.assertIn("mysteryAx", stdout.getvalue())

    def test_main_report_mode_reads_log(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            log = Path(tmpdir) / "axioms.log"
            log.write_text("'Foo.bar' does not depend on any axioms\n", encoding="utf-8")
            stdout = io.StringIO()
            with redirect_stdout(stdout):
                rc = check_axioms.main(["--log", str(log)])
        self.assertEqual(rc, 0)
        self.assertIn("Total theorems checked: 1", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
