#!/usr/bin/env python3
from __future__ import annotations

import io
import json
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_verification_status_doc


class VerificationStatusDocTests(unittest.TestCase):
    def _run_check(self, *, artifact_payload: dict, status_body: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            artifact = root / "artifacts" / "verification_status.json"
            status = root / "docs" / "VERIFICATION_STATUS.md"
            artifact.parent.mkdir(parents=True, exist_ok=True)
            status.parent.mkdir(parents=True, exist_ok=True)
            artifact.write_text(json.dumps(artifact_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            status.write_text(status_body, encoding="utf-8")

            old_artifact = check_verification_status_doc.ARTIFACT
            old_status = check_verification_status_doc.STATUS_DOC
            old_collect_covered = check_verification_status_doc.collect_covered
            old_load_exclusions = check_verification_status_doc.load_exclusions
            check_verification_status_doc.ARTIFACT = artifact
            check_verification_status_doc.STATUS_DOC = status
            check_verification_status_doc.collect_covered = lambda: {
                "Counter": {"a"},
                "ReentrancyExample": {"r1", "r2"},
            }
            check_verification_status_doc.load_exclusions = lambda: {"Counter": {"b"}}
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    try:
                        check_verification_status_doc.main()
                        return 0, stderr.getvalue()
                    except ValueError as exc:
                        print(exc, file=sys.stderr)
                        return 1, stderr.getvalue()
                    except SystemExit as exc:
                        return int(exc.code), stderr.getvalue()
            finally:
                check_verification_status_doc.ARTIFACT = old_artifact
                check_verification_status_doc.STATUS_DOC = old_status
                check_verification_status_doc.collect_covered = old_collect_covered
                check_verification_status_doc.load_exclusions = old_load_exclusions

    def test_matching_doc_passes(self) -> None:
        artifact = {
            "schema_version": 1,
            "theorems": {
                "total": 7,
                "categories": 2,
                "per_contract": {"Counter": 2, "ReentrancyExample": 5},
                "covered": 3,
                "coverage_percent": 43,
                "excluded": 1,
                "proven": 7,
                "stdlib": 0,
                "non_stdlib_total": 7,
            },
            "tests": {
                "foundry_functions": 10,
                "suites": 2,
                "property_functions": 3,
                "differential_total": 10000,
            },
            "proofs": {"axioms": 1, "sorry": 0},
            "codebase": {"core_lines": 1, "example_contracts": 2},
            "toolchain": {"lean": "lean", "solc": "0.8.33"},
        }
        status = textwrap.dedent(
            """
            # Verification Status

            | Contract | Properties | Status | Location |
            |----------|------------|--------|----------|
            | Counter | 2 | Complete | `Contracts/Counter/Proofs/` |
            | ReentrancyExample | 5 | Complete | `Contracts/ReentrancyExample/Contract.lean` |
            | CryptoHash | 0 | No specs | `Contracts/CryptoHash/Contract.lean` |
            | **Total** | **7** | **✅ 100%** | — |

            > **Note**: Stdlib (0 internal proof-automation properties) is excluded from the Layer 1 contracts table above but included in overall coverage statistics (7 total properties).

            | Contract | Coverage | Exclusions |
            |----------|----------|------------|
            | Counter | 50% (1/2) | 1 proof-only |
            | ReentrancyExample | 40% (2/5) | 0 proof-only |
            | Stdlib | 0% (0/0) | 0 proof-only |

            **Status**: 43% coverage (3/7), 1 remaining exclusions all proof-only

            - **Total Properties**: 7
            - **Covered**: 3
            - **Excluded**: 1 (all proof-only)

            0 `sorry` remaining across `Compiler/**/*.lean` and `Verity/**/*.lean` proof modules.
            """
        )
        rc, stderr = self._run_check(artifact_payload=artifact, status_body=status)
        self.assertEqual(rc, 0, stderr)

    def test_stale_covered_bullet_fails(self) -> None:
        artifact = {
            "schema_version": 1,
            "theorems": {
                "total": 7,
                "categories": 2,
                "per_contract": {"Counter": 2, "ReentrancyExample": 5},
                "covered": 3,
                "coverage_percent": 43,
                "excluded": 1,
                "proven": 7,
                "stdlib": 0,
                "non_stdlib_total": 7,
            },
            "tests": {
                "foundry_functions": 10,
                "suites": 2,
                "property_functions": 3,
                "differential_total": 10000,
            },
            "proofs": {"axioms": 1, "sorry": 0},
            "codebase": {"core_lines": 1, "example_contracts": 2},
            "toolchain": {"lean": "lean", "solc": "0.8.33"},
        }
        status = textwrap.dedent(
            """
            # Verification Status

            | Contract | Properties | Status | Location |
            |----------|------------|--------|----------|
            | Counter | 2 | Complete | `Contracts/Counter/Proofs/` |
            | ReentrancyExample | 5 | Complete | `Contracts/ReentrancyExample/Contract.lean` |
            | CryptoHash | 0 | No specs | `Contracts/CryptoHash/Contract.lean` |
            | **Total** | **7** | **✅ 100%** | — |

            > **Note**: Stdlib (0 internal proof-automation properties) is excluded from the Layer 1 contracts table above but included in overall coverage statistics (7 total properties).

            | Contract | Coverage | Exclusions |
            |----------|----------|------------|
            | Counter | 50% (1/2) | 1 proof-only |
            | ReentrancyExample | 40% (2/5) | 0 proof-only |
            | Stdlib | 0% (0/0) | 0 proof-only |

            **Status**: 43% coverage (3/7), 1 remaining exclusions all proof-only

            - **Total Properties**: 7
            - **Covered**: 2
            - **Excluded**: 1 (all proof-only)

            0 `sorry` remaining across `Compiler/**/*.lean` and `Verity/**/*.lean` proof modules.
            """
        )
        rc, stderr = self._run_check(artifact_payload=artifact, status_body=status)
        self.assertEqual(rc, 1)
        self.assertIn("covered bullet says 2, expected 3", stderr)
