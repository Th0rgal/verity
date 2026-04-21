#!/usr/bin/env python3
"""Tests for generate_evmyullean_fork_audit.py."""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import generate_evmyullean_fork_audit as audit


def _manifest(url: str, rev: str, input_rev: str) -> dict[str, object]:
    return {
        "packages": [
            {
                "name": "evmyul",
                "url": url,
                "rev": rev,
                "inputRev": input_rev,
            }
        ]
    }


class ForkAuditValidationTests(unittest.TestCase):
    def test_validate_audit_requires_pinned_commit_to_match_audited_tip(self) -> None:
        fork_audit = deepcopy(audit.FORK_AUDIT)
        fork_audit["pinned_commit"] = fork_audit["commits"][0]["sha"]
        with patch.object(audit, "FORK_AUDIT", fork_audit):
            with self.assertRaisesRegex(RuntimeError, "must match the audited fork tip"):
                audit._validate_audit()

    def test_cross_check_manifest_pin_checks_all_tracked_manifests(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            main_manifest = root / "lake-manifest.json"
            package_manifest = root / "packages" / "verity-compiler" / "lake-manifest.json"
            package_manifest.parent.mkdir(parents=True)
            expected_url = audit.FORK_AUDIT["fork_url"] + ".git"
            expected_rev = audit.FORK_AUDIT["pinned_commit"]
            main_manifest.write_text(
                json.dumps(_manifest(expected_url, expected_rev, expected_rev)),
                encoding="utf-8",
            )
            package_manifest.write_text(
                json.dumps(_manifest(expected_url, "0" * 40, expected_rev)),
                encoding="utf-8",
            )
            with patch.object(audit, "ROOT", root), \
                 patch.object(audit, "LAKE_MANIFESTS", [main_manifest, package_manifest]):
                with self.assertRaisesRegex(RuntimeError, "packages/verity-compiler/lake-manifest.json pins"):
                    audit._cross_check_manifest_pin()

    def test_cross_check_manifest_pin_checks_input_rev(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = root / "lake-manifest.json"
            expected_url = audit.FORK_AUDIT["fork_url"] + ".git"
            expected_rev = audit.FORK_AUDIT["pinned_commit"]
            manifest.write_text(
                json.dumps(_manifest(expected_url, expected_rev, "0" * 40)),
                encoding="utf-8",
            )
            with patch.object(audit, "ROOT", root), \
                 patch.object(audit, "LAKE_MANIFESTS", [manifest]):
                with self.assertRaisesRegex(RuntimeError, "inputRev"):
                    audit._cross_check_manifest_pin()


if __name__ == "__main__":
    unittest.main()
