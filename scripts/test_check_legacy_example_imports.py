#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_legacy_example_imports as guard


class LegacyExampleImportGuardTests(unittest.TestCase):
    def _run_check(
        self,
        *,
        files: dict[str, str],
        allowlist: str,
    ) -> tuple[int, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Verity").mkdir(parents=True, exist_ok=True)
            for rel, content in files.items():
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding="utf-8")

            allowlist_path = root / "scripts" / "legacy_example_import_allowlist.txt"
            allowlist_path.parent.mkdir(parents=True, exist_ok=True)
            allowlist_path.write_text(allowlist, encoding="utf-8")

            old_root = guard.ROOT
            old_allowlist_path = guard.ALLOWLIST_PATH
            old_scan_roots = guard.SCAN_ROOTS
            old_extra_scan = guard.EXTRA_SCAN_FILES
            guard.ROOT = root
            guard.ALLOWLIST_PATH = allowlist_path
            guard.SCAN_ROOTS = [root / "Compiler", root / "Verity"]
            guard.EXTRA_SCAN_FILES = []
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    rc = guard.main()
                return rc, stderr.getvalue()
            finally:
                guard.ROOT = old_root
                guard.ALLOWLIST_PATH = old_allowlist_path
                guard.SCAN_ROOTS = old_scan_roots
                guard.EXTRA_SCAN_FILES = old_extra_scan

    def test_rejects_non_allowlisted_import(self) -> None:
        rc, stderr = self._run_check(
            files={"Compiler/Main.lean": "import Verity.Examples.Counter\n"},
            allowlist="",
        )
        self.assertEqual(rc, 1)
        self.assertIn("unexpected legacy migrated-contract import", stderr)

    def test_accepts_allowlisted_import(self) -> None:
        rc, stderr = self._run_check(
            files={"Verity/All.lean": "import Verity.Examples.Counter\n"},
            allowlist="Verity/All.lean: Counter\n",
        )
        self.assertEqual(rc, 0, stderr)

    def test_fails_on_stale_allowlist_module(self) -> None:
        rc, stderr = self._run_check(
            files={"Verity/All.lean": "def ok := 1\n"},
            allowlist="Verity/All.lean: Counter\n",
        )
        self.assertEqual(rc, 1)
        self.assertIn("stale allowlist module", stderr)

    def test_ignores_comment_and_string_decoys(self) -> None:
        rc, stderr = self._run_check(
            files={
                "Compiler/Main.lean": (
                    "-- import Verity.Examples.Counter\n"
                    'def msg := "import Verity.Examples.Counter"\n'
                )
            },
            allowlist="",
        )
        self.assertEqual(rc, 0, stderr)

    def test_rejects_unknown_module_in_allowlist(self) -> None:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tmpdir:
            root = Path(tmpdir)
            allowlist_path = root / "scripts" / "legacy_example_import_allowlist.txt"
            allowlist_path.parent.mkdir(parents=True, exist_ok=True)
            allowlist_path.write_text("Verity/All.lean: NotMigrated\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                guard.parse_allowlist(allowlist_path)


if __name__ == "__main__":
    unittest.main()
