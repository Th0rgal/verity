#!/usr/bin/env python3
"""Tests for check_lean_hygiene.py.

Validates the four hygiene checks using temporary fixture trees:
1. Debug command detection (#eval, #check, #print, #reduce)
2. allowUnsafeReducibility count enforcement
3. Sorry allowlist (per-file caps, unexpected-file detection)
4. native_decide exclusion from proof files
"""
from __future__ import annotations

import io
import sys
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from typing import Any
from unittest.mock import patch

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_lean_hygiene as hygiene


class LineStartsWithCommandTests(unittest.TestCase):
    def test_exact_match(self) -> None:
        self.assertTrue(hygiene.line_starts_with_command("#eval", "#eval"))

    def test_with_argument(self) -> None:
        self.assertTrue(hygiene.line_starts_with_command("#eval Nat", "#eval"))

    def test_leading_whitespace(self) -> None:
        self.assertTrue(hygiene.line_starts_with_command("  #check Nat", "#check"))

    def test_no_match(self) -> None:
        self.assertFalse(hygiene.line_starts_with_command("-- #eval Nat", "#eval"))

    def test_prefix_not_matched(self) -> None:
        self.assertFalse(hygiene.line_starts_with_command("#evaluate", "#eval"))


class HygieneFixtureTestBase(unittest.TestCase):
    """Base class that builds a temporary fixture tree and patches ROOT."""

    def setUp(self) -> None:
        import tempfile

        self._tmpdir_obj = tempfile.TemporaryDirectory()
        self.root = Path(self._tmpdir_obj.name)

        # Proof directories
        (self.root / "Compiler" / "Proofs").mkdir(parents=True)
        (self.root / "Verity" / "Proofs").mkdir(parents=True)
        (self.root / "Contracts").mkdir(parents=True)

        # Default: one allowUnsafeReducibility so check 2 passes
        self._unsafe_file = self.root / "Compiler" / "Unsafe.lean"
        self._unsafe_file.write_text(
            "set_option allowUnsafeReducibility true\n", encoding="utf-8"
        )

        # Patch ROOT so the script operates on the fixture
        self._root_patcher = patch.object(hygiene, "ROOT", self.root)
        self._root_patcher.start()

    def tearDown(self) -> None:
        self._root_patcher.stop()
        self._tmpdir_obj.cleanup()

    def _run_main(self) -> tuple[int, str]:
        """Run hygiene.main() capturing output. Returns (exit_code, combined_output)."""
        stdout = io.StringIO()
        stderr = io.StringIO()
        try:
            with redirect_stdout(stdout), redirect_stderr(stderr):
                hygiene.main()
            return 0, stdout.getvalue() + stderr.getvalue()
        except SystemExit as e:
            return e.code or 0, stdout.getvalue() + stderr.getvalue()


class DebugCommandTests(HygieneFixtureTestBase):
    """Check 1: debug commands in proof files."""

    def test_eval_in_proof_file_detected(self) -> None:
        proof = self.root / "Compiler" / "Proofs" / "Foo.lean"
        proof.write_text("#eval 42\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertNotEqual(rc, 0)
        self.assertIn("#eval", output)

    def test_check_in_proof_file_detected(self) -> None:
        proof = self.root / "Verity" / "Proofs" / "Bar.lean"
        proof.write_text("#check Nat\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertNotEqual(rc, 0)
        self.assertIn("#check", output)

    def test_debug_in_comment_ignored(self) -> None:
        proof = self.root / "Compiler" / "Proofs" / "Ok.lean"
        proof.write_text("-- #eval 42\ntheorem foo := rfl\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)

    def test_debug_outside_proof_dirs_ignored(self) -> None:
        non_proof = self.root / "Compiler" / "Debug.lean"
        non_proof.write_text("#eval 42\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)

    def test_clean_proof_passes(self) -> None:
        proof = self.root / "Compiler" / "Proofs" / "Clean.lean"
        proof.write_text("theorem foo := rfl\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)
        self.assertIn("0 debug commands", output)


class UnsafeReducibilityTests(HygieneFixtureTestBase):
    """Check 2: allowUnsafeReducibility count."""

    def test_exactly_one_passes(self) -> None:
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)
        self.assertIn("1 allowUnsafeReducibility", output)

    def test_zero_fails(self) -> None:
        self._unsafe_file.write_text("-- no unsafe here\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertNotEqual(rc, 0)
        self.assertIn("Expected 1 allowUnsafeReducibility", output)

    def test_two_fails(self) -> None:
        extra = self.root / "Verity" / "Extra.lean"
        extra.write_text(
            "set_option allowUnsafeReducibility true\n", encoding="utf-8"
        )
        rc, output = self._run_main()
        self.assertNotEqual(rc, 0)
        self.assertIn("Expected 1 allowUnsafeReducibility, found 2", output)

    def test_lake_dir_excluded(self) -> None:
        lake = self.root / ".lake" / "packages" / "lib" / "Hack.lean"
        lake.parent.mkdir(parents=True)
        lake.write_text(
            "set_option allowUnsafeReducibility true\n", encoding="utf-8"
        )
        # Still exactly 1 from the base fixture
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)


class SorryAllowlistTests(HygieneFixtureTestBase):
    """Check 3: sorry allowlist enforcement."""

    BRIDGE_PATH = (
        "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean"
    )

    # The 4 pinned theorem names that are allowed to contain sorry
    PINNED_THEOREMS = [
        "sdiv_int256_eq_uint256Sdiv",
        "smod_int256_eq_uint256Smod",
        "sar_int256_eq_uint256Sar",
        "signextend_uint256_eq",
    ]

    def _make_bridge_file(self, theorems: list[str]) -> None:
        """Write a bridge lemmas file with sorry'd theorems."""
        bridge = self.root / Path(self.BRIDGE_PATH)
        bridge.parent.mkdir(parents=True, exist_ok=True)
        lines = []
        for thm in theorems:
            lines.append(f"private theorem {thm} (a b : Nat) : True := by")
            lines.append("  sorry")
        bridge.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def test_sorry_in_pinned_theorems_passes(self) -> None:
        self._make_bridge_file(self.PINNED_THEOREMS)
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)
        self.assertIn("4 sorry", output)

    def test_sorry_in_pinned_theorems_within_cap(self) -> None:
        self._make_bridge_file(self.PINNED_THEOREMS[:3])
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)
        self.assertIn("3 sorry", output)

    def test_sorry_exceeding_cap_fails(self) -> None:
        # 4 pinned + 1 extra = 5 sorrys, cap is 4
        extra = self.PINNED_THEOREMS + ["extra_fake_theorem"]
        self._make_bridge_file(extra)
        rc, output = self._run_main()
        self.assertNotEqual(rc, 0)
        self.assertIn("found 5 sorry (cap is 4)", output)

    def test_sorry_in_non_pinned_theorem_fails(self) -> None:
        # Replace one pinned theorem with an unpinned one
        swapped = self.PINNED_THEOREMS[:4] + ["rogue_theorem_xyz"]
        self._make_bridge_file(swapped)
        rc, output = self._run_main()
        self.assertNotEqual(rc, 0)
        self.assertIn("non-pinned theorems", output)
        self.assertIn("rogue_theorem_xyz", output)

    def test_sorry_swap_detected(self) -> None:
        # Same count (5), but one theorem swapped — must fail
        swapped = self.PINNED_THEOREMS[:4] + ["different_sorry_theorem"]
        self._make_bridge_file(swapped)
        rc, output = self._run_main()
        self.assertNotEqual(rc, 0)
        self.assertIn("different_sorry_theorem", output)

    def test_sorry_in_non_allowlisted_file_fails(self) -> None:
        rogue = self.root / "Compiler" / "Rogue.lean"
        rogue.write_text("sorry\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertNotEqual(rc, 0)
        self.assertIn("non-allowlisted files", output)

    def test_sorry_in_comment_ignored(self) -> None:
        lean_file = self.root / "Compiler" / "Commented.lean"
        lean_file.write_text("-- sorry this is a comment\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)

    def test_sorry_in_string_ignored(self) -> None:
        lean_file = self.root / "Compiler" / "Stringy.lean"
        lean_file.write_text('def msg := "sorry not sorry"\n', encoding="utf-8")
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)

    def test_no_sorry_passes(self) -> None:
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)
        self.assertIn("0 sorry", output)

    def test_lake_sorry_excluded(self) -> None:
        lake = self.root / ".lake" / "packages" / "lib" / "Oops.lean"
        lake.parent.mkdir(parents=True)
        lake.write_text("sorry\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)


class NativeDecideTests(HygieneFixtureTestBase):
    """Check 4: native_decide in proof files."""

    def test_native_decide_in_proof_detected(self) -> None:
        proof = self.root / "Compiler" / "Proofs" / "Theorem.lean"
        proof.write_text("theorem foo := by native_decide\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertNotEqual(rc, 0)
        self.assertIn("native_decide", output)

    def test_native_decide_in_test_file_ignored(self) -> None:
        test = self.root / "Compiler" / "Proofs" / "FooTest.lean"
        test.write_text("theorem foo := by native_decide\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)

    def test_native_decide_in_profile_file_ignored(self) -> None:
        profile = self.root / "Compiler" / "Proofs" / "BarProfile.lean"
        profile.write_text("theorem foo := by native_decide\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)

    def test_native_decide_outside_proof_dirs_ignored(self) -> None:
        lib = self.root / "Compiler" / "Lib.lean"
        lib.write_text("theorem foo := by native_decide\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertEqual(rc, 0, output)

    def test_native_decide_in_contracts_detected(self) -> None:
        contract = self.root / "Contracts" / "ERC20.lean"
        contract.write_text("theorem foo := by native_decide\n", encoding="utf-8")
        rc, output = self._run_main()
        self.assertNotEqual(rc, 0)
        self.assertIn("native_decide", output)


if __name__ == "__main__":
    unittest.main()
