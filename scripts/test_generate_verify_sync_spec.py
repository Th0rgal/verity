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

import generate_verify_sync_spec as generate


class GenerateVerifySyncSpecTests(unittest.TestCase):
    def test_check_passes_when_json_matches_source(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            spec_path = Path(td) / "verify_sync_spec.json"
            spec_path.write_text(generate._render_spec(), encoding="utf-8")

            old_path = generate.SPEC_PATH
            old_argv = sys.argv
            generate.SPEC_PATH = spec_path
            try:
                sys.argv = ["generate_verify_sync_spec.py", "--check"]
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = generate.main()
                self.assertEqual(rc, 0)
                self.assertIn("up to date", stdout.getvalue())
            finally:
                generate.SPEC_PATH = old_path
                sys.argv = old_argv

    def test_check_fails_when_json_is_stale(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            spec_path = Path(td) / "verify_sync_spec.json"
            spec_path.write_text("{}\n", encoding="utf-8")

            old_path = generate.SPEC_PATH
            old_argv = sys.argv
            generate.SPEC_PATH = spec_path
            try:
                sys.argv = ["generate_verify_sync_spec.py", "--check"]
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = generate.main()
                self.assertEqual(rc, 1)
                self.assertIn("stale", stderr.getvalue())
            finally:
                generate.SPEC_PATH = old_path
                sys.argv = old_argv


if __name__ == "__main__":
    unittest.main()
