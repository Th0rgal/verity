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
                @[simp] theorem evalBuiltinCall_addmod_bridge := by
                @[simp] theorem evalBuiltinCall_mulmod_bridge := by
                @[simp] theorem evalBuiltinCall_exp_bridge := by
                @[simp] theorem evalBuiltinCall_sdiv_bridge := by
                @[simp] theorem evalBuiltinCall_smod_bridge := by
                @[simp] theorem evalBuiltinCall_lt_bridge := by
                @[simp] theorem evalBuiltinCall_gt_bridge := by
                @[simp] theorem evalBuiltinCall_slt_bridge := by
                @[simp] theorem evalBuiltinCall_sgt_bridge := by
                @[simp] theorem evalBuiltinCall_eq_bridge := by
                @[simp] theorem evalBuiltinCall_iszero_bridge := by
                @[simp] theorem evalBuiltinCall_and_bridge := by
                @[simp] theorem evalBuiltinCall_or_bridge := by
                @[simp] theorem evalBuiltinCall_xor_bridge := by
                @[simp] theorem evalBuiltinCall_not_bridge := by
                @[simp] theorem evalBuiltinCall_shl_bridge := by
                @[simp] theorem evalBuiltinCall_shr_bridge := by
                @[simp] theorem evalBuiltinCall_sar_bridge := by
                @[simp] theorem evalBuiltinCall_signextend_bridge := by
                @[simp] theorem evalBuiltinCall_byte_bridge := by
                """
            ),
            encoding="utf-8",
        )
        (root / "TRUST_ASSUMPTIONS.md").write_text(
            "25 universal pure bridge theorems are now proven. "
            "All pure bridge cases are now covered by universal symbolic lemmas.\n",
            encoding="utf-8",
        )
        (root / "AXIOMS.md").write_text(
            "The EVMYulLean bridge currently has universal equivalence lemmas for 25 of them "
            "(`add`, `sub`, `mul`, `div`, `mod`, `addmod`, `mulmod`, `exp`, `sdiv`, `smod`, "
            "`lt`, `gt`, `slt`, `sgt`, `eq`, `iszero`, `and`, `or`, `xor`, `not`, `shl`, `shr`, "
            "`sar`, `signextend`, `byte`), "
            "with no remaining pure builtins relying only on concrete bridge checks.\n",
            encoding="utf-8",
        )
        arithmetic_path = root / "docs" / "ARITHMETIC_PROFILE.md"
        arithmetic_path.parent.mkdir(parents=True, exist_ok=True)
        arithmetic_path.write_text(arithmetic_profile, encoding="utf-8")
        interpreter = root / "docs" / "INTERPRETER_FEATURE_MATRIX.md"
        interpreter.write_text(
            "25 are discharged by universal symbolic lemmas, "
            "and none still require concrete-only regression coverage.\n",
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
                "TRUST_ASSUMPTIONS": root / "TRUST_ASSUMPTIONS.md",
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
                "universal bridge lemmas for 25 pure builtins: `add`, `sub`, `mul`, `div`, `mod`, "
                "`addmod`, `mulmod`, `exp`, `sdiv`, `smod`, `lt`, `gt`, `slt`, `sgt`, `eq`, `iszero`, "
                "`and`, `or`, `xor`, `not`, `shl`, `shr`, `sar`, `signextend`, and `byte`\n"
                "concrete bridge smoke tests are no longer needed for any pure builtin\n"
                "25/25 pure EVMYulLean-backed builtins have universal bridge lemmas.\n"
            )
        )
        self.assertEqual(rc, 0, output)
        self.assertIn("25/25 pure builtins universally bridged", output)

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
            expected["TRUST_ASSUMPTIONS"],
        )
        self.assertIn(
            "concrete bridge smoke tests are no longer needed for any pure builtin",
            expected["ARITHMETIC_PROFILE"],
        )
        self.assertIn(
            "25/25 pure EVMYulLean-backed builtins have universal bridge lemmas.",
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

    def test_extract_admitted_builtins_detects_sorry(self) -> None:
        text = textwrap.dedent("""\
            private theorem exp_core (a b : Nat) : sorry_free := by
              exact trivial

            @[simp] theorem evalBuiltinCall_exp_bridge := by
              exact exp_core

            private theorem slt_core (a b : Nat) : sorry_dep := by
              sorry

            @[simp] theorem evalBuiltinCall_slt_bridge := by
              exact slt_core

            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        admitted = check.extract_admitted_builtins(text)
        self.assertEqual(admitted, ["slt"])

    def test_extract_admitted_detects_inline_by_sorry(self) -> None:
        """Inline ``by sorry`` on the same line should be detected."""
        text = textwrap.dedent("""\
            private theorem exp_core := by sorry

            @[simp] theorem evalBuiltinCall_exp_bridge := by
              exact exp_core

            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        admitted = check.extract_admitted_builtins(text)
        self.assertEqual(admitted, ["exp"])

    def test_extract_admitted_detects_local_helper_sorry(self) -> None:
        """A ``local theorem`` helper with sorry should admit the next bridge."""
        text = textwrap.dedent("""\
            local theorem sar_core := by
              sorry

            @[simp] theorem evalBuiltinCall_sar_bridge := by
              exact sar_core

            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        admitted = check.extract_admitted_builtins(text)
        self.assertEqual(admitted, ["sar"])

    def test_extract_admitted_treats_opaque_as_boundary(self) -> None:
        """An ``opaque`` helper with sorry should not be merged into the prior bridge."""
        text = textwrap.dedent("""\
            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial

            opaque sar_core : True := by
              sorry

            @[simp] theorem evalBuiltinCall_sar_bridge := by
              exact sar_core
        """)
        admitted = check.extract_admitted_builtins(text)
        self.assertEqual(admitted, ["sar"])

    def test_extract_admitted_ignores_sorry_in_comments(self) -> None:
        """Sorry in comments or doc comments should not trigger detection."""
        text = textwrap.dedent("""\
            -- sorry this is a comment
            /-- **Status**: sorry — needs proof -/
            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        admitted = check.extract_admitted_builtins(text)
        self.assertEqual(admitted, [])

    def test_extract_admitted_ignores_sorry_in_block_comments(self) -> None:
        """Sorry in regular block comments (/- ... -/) should not trigger detection."""
        text = textwrap.dedent("""\
            /- This uses sorry as a placeholder -/
            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        admitted = check.extract_admitted_builtins(text)
        self.assertEqual(admitted, [])

    def test_extract_admitted_ignores_sorry_in_multiline_block_comments(self) -> None:
        """Sorry in multi-line regular block comments should not trigger detection."""
        text = textwrap.dedent("""\
            /- This block comment
               mentions sorry
               across multiple lines -/
            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        admitted = check.extract_admitted_builtins(text)
        self.assertEqual(admitted, [])

    def test_extract_admitted_ignores_sorry_in_nested_block_comments(self) -> None:
        """Nested Lean block comments should not leak sorry into the scan."""
        text = textwrap.dedent("""\
            /- outer
               /- inner -/
               sorry
            -/
            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        admitted = check.extract_admitted_builtins(text)
        self.assertEqual(admitted, [])

    def test_extract_universal_ignores_commented_theorem_text(self) -> None:
        text = textwrap.dedent("""\
            /- @[simp] theorem evalBuiltinCall_exp_bridge := by
              exact trivial
            -/
            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        universal = check.extract_universal_builtins(text)
        self.assertEqual(universal, ["add"])

    def test_extract_admitted_keeps_comment_markers_inside_strings(self) -> None:
        text = textwrap.dedent("""\
            private theorem byte_status : String := "INT256_MIN/-1 overflow"

            private theorem byte_core := by
              sorry

            @[simp] theorem evalBuiltinCall_byte_bridge := by
              exact byte_core
        """)
        admitted = check.extract_admitted_builtins(text)
        self.assertEqual(admitted, ["byte"])

    def test_admitted_qualifier_generates_parenthetical(self) -> None:
        q = check._admitted_qualifier(["exp", "slt", "sgt"])
        self.assertEqual(q, " (22 fully proven, 3 with sorry-dependent core equivalences)")

    def test_admitted_qualifier_uses_count_parameter(self) -> None:
        q = check._admitted_qualifier(["exp", "slt"], count=20)
        self.assertEqual(q, " (18 fully proven, 2 with sorry-dependent core equivalences)")

    def test_admitted_qualifier_empty_when_none(self) -> None:
        self.assertEqual(check._admitted_qualifier([]), "")

    def test_snippets_include_qualifier_when_admitted(self) -> None:
        admitted = ["exp", "slt"]
        expected = check.expected_snippets(check.PURE_BUILTINS, [], admitted=admitted)
        self.assertIn(
            "25 universal pure bridge theorems (23 fully proven, 2 with sorry-dependent core equivalences)",
            expected["TRUST_ASSUMPTIONS"],
        )
        self.assertIn(
            "25/25 pure EVMYulLean-backed builtins have universal bridge lemmas"
            " (23 fully proven, 2 with sorry-dependent core equivalences).",
            expected["ARITHMETIC_PROFILE"],
        )

    def test_snippets_no_qualifier_when_no_admitted(self) -> None:
        expected = check.expected_snippets(check.PURE_BUILTINS, [], admitted=[])
        trust = expected["TRUST_ASSUMPTIONS"]
        self.assertTrue(
            any("25 universal pure bridge theorems" in s and "sorry" not in s for s in trust),
            f"Expected unqualified theorem count in TRUST_ASSUMPTIONS, got: {trust}",
        )

    def test_matching_bridge_docs_with_admitted_pass(self) -> None:
        """End-to-end test: fixture with sorry-dependent lemmas and qualified docs."""
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            bridge_lemmas = root / "Compiler" / "Proofs" / "YulGeneration" / "Backends" / "EvmYulLeanBridgeLemmas.lean"
            bridge_lemmas.parent.mkdir(parents=True, exist_ok=True)
            # Two builtins with sorry (exp, slt), rest fully proven
            lines = []
            for name in check.PURE_BUILTINS:
                if name in ("exp", "slt"):
                    lines.append(f"private theorem {name}_core := by")
                    lines.append("  sorry")
                lines.append(f"@[simp] theorem evalBuiltinCall_{name}_bridge := by")
                lines.append(f"  exact {name}_core")
            bridge_lemmas.write_text("\n".join(lines) + "\n", encoding="utf-8")

            (root / "TRUST_ASSUMPTIONS.md").write_text(
                "25 universal pure bridge theorems"
                " (23 fully proven, 2 with sorry-dependent core equivalences). "
                "All pure bridge cases are now covered by universal symbolic lemmas.\n",
                encoding="utf-8",
            )
            (root / "AXIOMS.md").write_text(
                "The EVMYulLean bridge currently has universal equivalence lemmas for 25 of them "
                "(`add`, `sub`, `mul`, `div`, `mod`, `addmod`, `mulmod`, `exp`, `sdiv`, `smod`, "
                "`lt`, `gt`, `slt`, `sgt`, `eq`, `iszero`, `and`, `or`, `xor`, `not`, `shl`, `shr`, "
                "`sar`, `signextend`, `byte`), "
                "with no remaining pure builtins relying only on concrete bridge checks.\n",
                encoding="utf-8",
            )
            (root / "docs").mkdir(parents=True, exist_ok=True)
            (root / "docs" / "ARITHMETIC_PROFILE.md").write_text(
                "universal bridge lemmas for 25 pure builtins: `add`, `sub`, `mul`, `div`, `mod`, "
                "`addmod`, `mulmod`, `exp`, `sdiv`, `smod`, `lt`, `gt`, `slt`, `sgt`, `eq`, `iszero`, "
                "`and`, `or`, `xor`, `not`, `shl`, `shr`, `sar`, `signextend`, and `byte`\n"
                "concrete bridge smoke tests are no longer needed for any pure builtin\n"
                "25/25 pure EVMYulLean-backed builtins have universal bridge lemmas"
                " (23 fully proven, 2 with sorry-dependent core equivalences).\n",
                encoding="utf-8",
            )
            (root / "docs" / "INTERPRETER_FEATURE_MATRIX.md").write_text(
                "25 are discharged by universal symbolic lemmas, "
                "and none still require concrete-only regression coverage.\n",
                encoding="utf-8",
            )
            (root / "Compiler" / "Proofs" / "EndToEnd.lean").write_text(
                "replacement coverage: universal bridge lemmas for all pure bridged builtins.\n",
                encoding="utf-8",
            )

            old_root = check.ROOT
            old_bridge = check.BRIDGE_LEMMAS
            old_targets = check.TARGET_FILES
            check.ROOT = root
            check.BRIDGE_LEMMAS = bridge_lemmas
            check.TARGET_FILES = {
                "TRUST_ASSUMPTIONS": root / "TRUST_ASSUMPTIONS.md",
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
                output = stdout.getvalue() + stderr.getvalue()
                self.assertEqual(rc, 0, output)
                self.assertIn("admitted (sorry-dependent): exp, slt", output)
            finally:
                check.ROOT = old_root
                check.BRIDGE_LEMMAS = old_bridge
                check.TARGET_FILES = old_targets


if __name__ == "__main__":
    unittest.main()
