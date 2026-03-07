#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_bridge_coverage_sync as check


class BridgeCoverageSyncTests(unittest.TestCase):
    def _write_fixture_tree(self, root: Path, *, arithmetic_profile: str) -> None:
        bridge_lemmas = root / "Compiler" / "Proofs" / "YulGeneration" / "Backends" / "EvmYulLeanBridgeLemmas.lean"
        bridge_lemmas.parent.mkdir(parents=True, exist_ok=True)
        bridge_lemmas.write_text(
            textwrap.dedent(
                """
                @[simp] theorem evalBuiltinCall_add_bridge := by
                @[simp] theorem evalBuiltinCall_sub_bridge := by
                @[simp] theorem evalBuiltinCall_mul_bridge := by
                @[simp] theorem evalBuiltinCall_div_bridge := by
                @[simp] theorem evalBuiltinCall_mod_bridge := by
                @[simp] theorem evalBuiltinCall_lt_bridge := by
                @[simp] theorem evalBuiltinCall_gt_bridge := by
                @[simp] theorem evalBuiltinCall_eq_bridge := by
                @[simp] theorem evalBuiltinCall_iszero_bridge := by
                @[simp] theorem evalBuiltinCall_and_bridge := by
                @[simp] theorem evalBuiltinCall_or_bridge := by
                @[simp] theorem evalBuiltinCall_xor_bridge := by
                @[simp] theorem evalBuiltinCall_not_bridge := by
                @[simp] theorem evalBuiltinCall_shl_bridge := by
                @[simp] theorem evalBuiltinCall_shr_bridge := by
                """
            ),
            encoding="utf-8",
        )
        (root / "AUDIT.md").write_text(
            "15 universal pure bridge theorems are now proven. "
            "All pure bridge cases are now covered by universal symbolic lemmas.\n",
            encoding="utf-8",
        )
        (root / "AXIOMS.md").write_text(
            "The EVMYulLean bridge currently has universal equivalence lemmas for 15 of them "
            "(`add`, `sub`, `mul`, `div`, `mod`, `lt`, `gt`, `eq`, `iszero`, `and`, `or`, `xor`, `not`, `shl`, `shr`) "
            "with no remaining pure builtins relying only on concrete bridge checks.\n",
            encoding="utf-8",
        )
        arithmetic_path = root / "docs" / "ARITHMETIC_PROFILE.md"
        arithmetic_path.parent.mkdir(parents=True, exist_ok=True)
        arithmetic_path.write_text(arithmetic_profile, encoding="utf-8")
        interpreter = root / "docs" / "INTERPRETER_FEATURE_MATRIX.md"
        interpreter.write_text(
            "15 are discharged by universal symbolic lemmas, and none still require concrete-only regression coverage.\n",
            encoding="utf-8",
        )
        end_to_end = root / "Compiler" / "Proofs" / "EndToEnd.lean"
        end_to_end.parent.mkdir(parents=True, exist_ok=True)
        end_to_end.write_text(
            "replacement coverage: universal bridge lemmas for all pure bridged builtins.\n",
            encoding="utf-8",
        )

    def _run_check(self, *, arithmetic_profile: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(root, arithmetic_profile=arithmetic_profile)

            old_root = check.ROOT
            old_bridge = check.BRIDGE_LEMMAS
            old_targets = check.TARGET_FILES
            check.ROOT = root
            check.BRIDGE_LEMMAS = root / "Compiler" / "Proofs" / "YulGeneration" / "Backends" / "EvmYulLeanBridgeLemmas.lean"
            check.TARGET_FILES = {
                "AUDIT": root / "AUDIT.md",
                "AXIOMS": root / "AXIOMS.md",
                "ARITHMETIC_PROFILE": root / "docs" / "ARITHMETIC_PROFILE.md",
                "INTERPRETER_FEATURE_MATRIX": root / "docs" / "INTERPRETER_FEATURE_MATRIX.md",
                "END_TO_END": root / "Compiler" / "Proofs" / "EndToEnd.lean",
            }
            try:
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check.main()
                return rc, stdout.getvalue() + stderr.getvalue()
            finally:
                check.ROOT = old_root
                check.BRIDGE_LEMMAS = old_bridge
                check.TARGET_FILES = old_targets

    def test_matching_bridge_docs_pass(self) -> None:
        rc, output = self._run_check(
            arithmetic_profile=(
                "universal bridge lemmas for 15 pure builtins: `add`, `sub`, `mul`, `div`, `mod`, "
                "`lt`, `gt`, `eq`, `iszero`, `and`, `or`, `xor`, `not`, `shl`, and `shr`\n"
                "concrete bridge smoke tests are no longer needed for any pure builtin\n"
                "15/15 pure EVMYulLean-backed builtins have universal bridge lemmas.\n"
            )
        )
        self.assertEqual(rc, 0, output)
        self.assertIn("15/15 pure builtins universally bridged", output)

    def test_stale_bridge_docs_fail(self) -> None:
        rc, output = self._run_check(
            arithmetic_profile=(
                "universal bridge lemmas for 12 pure builtins: `add`, `sub`, `mul`, `div`, `mod`, "
                "`lt`, `gt`, `eq`, `iszero`, `and`, `or`, and `xor`\n"
                "concrete bridge smoke tests for `not`, `shl`, and `shr`\n"
                "12/15 pure EVMYulLean-backed builtins have universal bridge lemmas; `not`, `shl`, and `shr` still rely on concrete smoke tests.\n"
            )
        )
        self.assertEqual(rc, 1)
        self.assertIn("docs/ARITHMETIC_PROFILE.md is out of sync", output)

    def test_no_remaining_pure_builtin_coverage_is_supported(self) -> None:
        expected = check.expected_snippets(check.PURE_BUILTINS, [])
        self.assertIn(
            "All pure bridge cases are now covered by universal symbolic lemmas.",
            expected["AUDIT"],
        )
        self.assertIn(
            "concrete bridge smoke tests are no longer needed for any pure builtin",
            expected["ARITHMETIC_PROFILE"],
        )
        self.assertIn(
            "15/15 pure EVMYulLean-backed builtins have universal bridge lemmas.",
            expected["ARITHMETIC_PROFILE"],
        )
        self.assertIn(
            "and none still require concrete-only regression coverage",
            expected["INTERPRETER_FEATURE_MATRIX"],
        )
        self.assertIn(
            "replacement coverage: universal bridge lemmas for all pure bridged builtins.",
            expected["END_TO_END"],
        )


if __name__ == "__main__":
    unittest.main()
