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

import check_issue_1060_integrity as guard


class Issue1060IntegrityTests(unittest.TestCase):
    def _run_check(self, payload: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent) as tmpdir:
            root = Path(tmpdir)
            ledger = root / "artifacts" / "issue_1060_progress.json"
            ledger.parent.mkdir(parents=True, exist_ok=True)
            ledger.write_text(payload, encoding="utf-8")

            old_root = guard.ROOT
            old_ledger = guard.LEDGER
            guard.ROOT = root
            guard.LEDGER = ledger
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    rc = guard.main()
                return rc, stderr.getvalue()
            finally:
                guard.ROOT = old_root
                guard.LEDGER = old_ledger

    def test_passes_with_all_items_open(self) -> None:
        import json

        payload = json.dumps({
            "issue": "#1060",
            "pr": "#1065",
            "baseline_sorry": 0,
            "items": {
                item: {
                    "status": "open",
                    "acceptance_criteria": [],
                    "files_changed": [],
                    "verification_commands": [],
                    "verification_results": [],
                    "evidence": {"theorems": [], "tests": []},
                    "obligation_delta": {"removed_sorries": []},
                    "notes": "",
                }
                for item in guard.ROADMAP_ITEMS
            },
        })
        rc, stderr = self._run_check(payload)
        self.assertEqual(rc, 0, stderr)

    def test_fails_when_complete_semantic_item_has_no_theorem(self) -> None:
        entries = {}
        for item in guard.ROADMAP_ITEMS:
            entries[item] = {
                "status": "open",
                "acceptance_criteria": [],
                "files_changed": [],
                "verification_commands": [],
                "verification_results": [],
                "evidence": {"theorems": [], "tests": []},
                "obligation_delta": {"removed_sorries": []},
                "notes": "",
            }

        entries["3.2"] = {
            "status": "complete",
            "acceptance_criteria": ["Bridge theorem exists"],
            "files_changed": ["Verity/Examples/MacroContracts.lean"],
            "verification_commands": ["lake build"],
            "verification_results": ["pass"],
            "evidence": {"theorems": [], "tests": [{"name": "bridge test"}]},
            "obligation_delta": {"removed_sorries": []},
            "notes": "",
        }

        import json
        payload = json.dumps({
            "issue": "#1060",
            "pr": "#1065",
            "baseline_sorry": 0,
            "items": entries,
        })
        rc, stderr = self._run_check(payload)
        self.assertEqual(rc, 1)
        self.assertIn("complete but has no theorem evidence", stderr)

    def test_fails_when_multiple_active_items(self) -> None:
        import json

        entries = {
            item: {
                "status": "open",
                "acceptance_criteria": [],
                "files_changed": [],
                "verification_commands": [],
                "verification_results": [],
                "evidence": {"theorems": [], "tests": []},
                "obligation_delta": {"removed_sorries": []},
                "notes": "",
            }
            for item in guard.ROADMAP_ITEMS
        }
        entries["2.2"]["status"] = "partial"
        entries["2.3"]["status"] = "in_progress"

        payload = json.dumps({
            "issue": "#1060",
            "pr": "#1065",
            "baseline_sorry": 0,
            "items": entries,
        })
        rc, stderr = self._run_check(payload)
        self.assertEqual(rc, 1)
        self.assertIn("at most one roadmap item may be active", stderr)

    def test_fails_when_active_item_result_lacks_run_marker(self) -> None:
        import json

        entries = {
            item: {
                "status": "open",
                "acceptance_criteria": [],
                "files_changed": [],
                "verification_commands": [],
                "verification_results": [],
                "evidence": {"theorems": [], "tests": []},
                "obligation_delta": {"removed_sorries": []},
                "notes": "",
            }
            for item in guard.ROADMAP_ITEMS
        }
        entries["2.2"] = {
            "status": "partial",
            "acceptance_criteria": ["criterion"],
            "files_changed": ["Verity/Core/Free/TypedIRCompilerCorrectness.lean"],
            "verification_commands": ["lake build"],
            "verification_results": ["pass: lake build"],
            "evidence": {"theorems": [], "tests": ["test"]},
            "obligation_delta": {"removed_sorries": []},
            "notes": "",
        }

        payload = json.dumps({
            "issue": "#1060",
            "pr": "#1065",
            "baseline_sorry": 0,
            "items": entries,
        })
        rc, stderr = self._run_check(payload)
        self.assertEqual(rc, 1)
        self.assertIn("run_id=<...> or artifact_sha256=<...>", stderr)


if __name__ == "__main__":
    unittest.main()
