#!/usr/bin/env python3
"""Tests for generate_evmyullean_adapter_report.py.

Validates bridge-lemma sorry detection, builtin extraction, fail-fast
on missing files, and end-to-end report consistency with the repo.
"""
from __future__ import annotations

import json
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest.mock import patch

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import generate_evmyullean_adapter_report as gen


class ParseBridgeLemmasTests(unittest.TestCase):
    """Tests for _parse_bridge_lemmas sorry detection."""

    def _write_lemma_file(self, text: str) -> Path:
        self._tmpdir = tempfile.TemporaryDirectory()
        p = Path(self._tmpdir.name) / "BridgeLemmas.lean"
        p.write_text(textwrap.dedent(text), encoding="utf-8")
        return p

    def tearDown(self) -> None:
        if hasattr(self, "_tmpdir"):
            self._tmpdir.cleanup()

    def test_detects_sorry_dependent_lemma(self) -> None:
        p = self._write_lemma_file("""\
            private theorem exp_core := by
              sorry

            @[simp] theorem evalBuiltinCall_exp_bridge := by
              exact exp_core

            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertIn("exp", all_lemmas)
        self.assertIn("add", all_lemmas)
        self.assertEqual(admitted, ["exp"])

    def test_no_sorry_means_no_admitted(self) -> None:
        p = self._write_lemma_file("""\
            @[simp] theorem evalBuiltinCall_add_bridge := by exact trivial
            @[simp] theorem evalBuiltinCall_sub_bridge := by exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(len(all_lemmas), 2)
        self.assertEqual(admitted, [])

    def test_detects_inline_by_sorry(self) -> None:
        """Inline ``by sorry`` on the same line should be detected."""
        p = self._write_lemma_file("""\
            private theorem exp_core := by sorry

            @[simp] theorem evalBuiltinCall_exp_bridge := by
              exact exp_core

            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(admitted, ["exp"])

    def test_detects_local_helper_sorry(self) -> None:
        """A ``local theorem`` helper with sorry should admit the next bridge."""
        p = self._write_lemma_file("""\
            local theorem sar_core := by
              sorry

            @[simp] theorem evalBuiltinCall_sar_bridge := by
              exact sar_core

            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertIn("sar", all_lemmas)
        self.assertEqual(admitted, ["sar"])

    def test_treats_opaque_helper_as_declaration_boundary(self) -> None:
        """An ``opaque`` helper with sorry should admit the following bridge."""
        p = self._write_lemma_file("""\
            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial

            opaque sar_core : True := by
              sorry

            @[simp] theorem evalBuiltinCall_sar_bridge := by
              exact sar_core
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertIn("add", all_lemmas)
        self.assertIn("sar", all_lemmas)
        self.assertEqual(admitted, ["sar"])

    def test_ignores_sorry_in_comments(self) -> None:
        """Sorry in comments or doc comments should not trigger detection."""
        p = self._write_lemma_file("""\
            -- sorry this is a comment
            /-- **Status**: sorry — needs proof -/
            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(admitted, [])

    def test_ignores_sorry_in_nested_block_comments(self) -> None:
        """Nested Lean block comments should not leak sorry into the scan."""
        p = self._write_lemma_file("""\
            /- outer
               /- inner -/
               sorry
            -/
            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(admitted, [])

    def test_ignores_bridge_theorem_names_inside_comments(self) -> None:
        """Commented theorem names must not count as universal bridge lemmas."""
        p = self._write_lemma_file("""\
            /-
            theorem evalBuiltinCall_fake_bridge := by
              exact trivial
            -/
            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(all_lemmas, ["add"])
        self.assertEqual(admitted, [])

    def test_missing_file_raises(self) -> None:
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", Path("/nonexistent/BridgeLemmas.lean")):
            with self.assertRaises(FileNotFoundError):
                gen._parse_bridge_lemmas()


class ParseLookupPrimOpTests(unittest.TestCase):
    """Tests for _parse_lookup_primop extraction."""

    def test_extracts_builtin_names(self) -> None:
        text = textwrap.dedent("""\
            def lookupPrimOp (name : String) : Option PrimOp :=
              match name with
              | "add" => some .ADD
              | "sub" => some .SUB
              | "mul" => some .MUL
              | _ => none

            def evalPureBuiltinViaEvmYulLean := sorry
        """)
        result = gen._parse_lookup_primop(text)
        self.assertEqual(result, ["add", "mul", "sub"])

    def test_ignores_commented_match_arms(self) -> None:
        text = textwrap.dedent("""\
            def lookupPrimOp (name : String) : Option PrimOp :=
              match name with
              | "add" => some .ADD
              /-
              | "fake" => some .FAKE
              -/
              -- | "also_fake" => some .ALSO_FAKE
              | _ => none

            def evalPureBuiltinViaEvmYulLean := sorry
        """)
        result = gen._parse_lookup_primop(text)
        self.assertEqual(result, ["add"])

    def test_missing_block_raises(self) -> None:
        with self.assertRaises(ValueError):
            gen._parse_lookup_primop("no markers here")


class ParsePureBridgeTests(unittest.TestCase):
    """Tests for _parse_pure_bridge extraction."""

    def test_extracts_pure_builtins(self) -> None:
        text = textwrap.dedent("""\
            def evalPureBuiltinViaEvmYulLean (name : String) (args : List Nat) : Option Nat :=
              match name, args with
              | "add", [a, b] => some (a + b)
              | "sub", [a, b] => some (a - b)
              | _, _ => none

            def evalBuiltinCallViaEvmYulLean := sorry
        """)
        result = gen._parse_pure_bridge(text)
        self.assertEqual(result, ["add", "sub"])

    def test_ignores_commented_match_arms(self) -> None:
        text = textwrap.dedent("""\
            def evalPureBuiltinViaEvmYulLean (name : String) (args : List Nat) : Option Nat :=
              match name, args with
              | "add", [a, b] => some (a + b)
              /-
              | "fake", [a, b] => some (a + b)
              -/
              -- | "also_fake", [a, b] => some (a + b)
              | _, _ => none

            def evalBuiltinCallViaEvmYulLean := sorry
        """)
        result = gen._parse_pure_bridge(text)
        self.assertEqual(result, ["add"])


class ParseBridgeTestsTests(unittest.TestCase):
    """Tests for _parse_bridge_tests extraction."""

    def _write_test_file(self, text: str) -> Path:
        self._tmpdir = tempfile.TemporaryDirectory()
        p = Path(self._tmpdir.name) / "BridgeTest.lean"
        p.write_text(textwrap.dedent(text), encoding="utf-8")
        return p

    def tearDown(self) -> None:
        if hasattr(self, "_tmpdir"):
            self._tmpdir.cleanup()

    def test_counts_bridge_equivalence_examples(self) -> None:
        p = self._write_test_file("""\
            -- preamble
            example := verityEvalBuiltin "add" [1, 2] = bridgeEval "add" [1, 2] := by native_decide
            example := verityEvalBuiltin "sub" [5, 3] = bridgeEval "sub" [5, 3] := by native_decide
        """)
        with patch.object(gen, "BRIDGE_TEST_FILE", p):
            builtins, count = gen._parse_bridge_tests()
        self.assertEqual(count, 2)
        self.assertIn("add", builtins)
        self.assertIn("sub", builtins)

    def test_skips_non_bridge_examples(self) -> None:
        p = self._write_test_file("""\
            -- preamble
            example := verityEvalBuiltin "add" [1, 2] = 3 := by native_decide
        """)
        with patch.object(gen, "BRIDGE_TEST_FILE", p):
            builtins, count = gen._parse_bridge_tests()
        self.assertEqual(count, 0)
        self.assertEqual(builtins, [])

    def test_mismatched_builtins_not_counted(self) -> None:
        """A block where verity and bridge sides test different builtins
        does not credit either builtin and is not counted as a bridge test.

        Previously the block was counted toward the concrete-test total even
        when the two sides referenced unrelated builtins; this inflated the
        tally with blocks that did not actually assert any bridge equivalence.
        Now only blocks where the intersection of referenced builtins is
        non-empty are counted as concrete bridge tests.
        """
        p = self._write_test_file("""\
            -- preamble
            example := verityEvalBuiltin "add" [1, 2] = bridgeEval "sub" [1, 2] := by native_decide
        """)
        with patch.object(gen, "BRIDGE_TEST_FILE", p):
            builtins, count = gen._parse_bridge_tests()
        # Mismatched blocks no longer count toward the concrete-test total.
        self.assertEqual(count, 0)
        self.assertNotIn("add", builtins)
        self.assertNotIn("sub", builtins)

    def test_mentions_without_bridge_equality_not_counted(self) -> None:
        """Separate facts about both evaluators are not bridge equivalences."""
        p = self._write_test_file("""\
            -- preamble
            example : (verityEvalBuiltin "add" [1, 2] = 3) ∧
                (bridgeEval "add" [1, 2] = 4) := by native_decide
        """)
        with patch.object(gen, "BRIDGE_TEST_FILE", p):
            builtins, count = gen._parse_bridge_tests()
        self.assertEqual(count, 0)
        self.assertEqual(builtins, [])

    def test_rejects_non_direct_bridge_equality(self) -> None:
        """Only direct evaluator-to-evaluator equalities count as bridge tests."""
        p = self._write_test_file("""\
            -- preamble
            example : verityEvalBuiltin "add" [1, 2] = bridgeEval "add" [1, 2] + 1 := by native_decide
        """)
        with patch.object(gen, "BRIDGE_TEST_FILE", p):
            builtins, count = gen._parse_bridge_tests()
        self.assertEqual(count, 0)
        self.assertEqual(builtins, [])

    def test_reversed_bridge_equality_counted(self) -> None:
        p = self._write_test_file("""\
            -- preamble
            example : bridgeEval "add" [1, 2] = verityEvalBuiltin "add" [1, 2] := by native_decide
        """)
        with patch.object(gen, "BRIDGE_TEST_FILE", p):
            builtins, count = gen._parse_bridge_tests()
        self.assertEqual(count, 1)
        self.assertEqual(builtins, ["add"])

    def test_ignores_commented_bridge_examples(self) -> None:
        p = self._write_test_file("""\
            /-
            example := verityEvalBuiltin "fake" [1, 2] = bridgeEval "fake" [1, 2] := by native_decide
            -/
            -- example := verityEvalBuiltin "also_fake" [1, 2] = bridgeEval "also_fake" [1, 2] := by native_decide
            example := verityEvalBuiltin "add" [1, 2] = bridgeEval "add" [1, 2] := by native_decide
        """)
        with patch.object(gen, "BRIDGE_TEST_FILE", p):
            builtins, count = gen._parse_bridge_tests()
        self.assertEqual(count, 1)
        self.assertEqual(builtins, ["add"])

    def test_preserves_comment_markers_inside_string_literals(self) -> None:
        p = self._write_test_file("""\
            example := "INT256_MIN/-1 overflow" = "INT256_MIN/-1 overflow" := by native_decide
            example := verityEvalBuiltin "add" [1, 2] = bridgeEval "add" [1, 2] := by native_decide
        """)
        with patch.object(gen, "BRIDGE_TEST_FILE", p):
            builtins, count = gen._parse_bridge_tests()
        self.assertEqual(count, 1)
        self.assertEqual(builtins, ["add"])

    def test_missing_file_raises(self) -> None:
        with patch.object(gen, "BRIDGE_TEST_FILE", Path("/nonexistent/BridgeTest.lean")):
            with self.assertRaises(FileNotFoundError):
                gen._parse_bridge_tests()


class ParseCorrectnessProofsTests(unittest.TestCase):
    """Tests for _parse_correctness_proofs."""

    def _write_correctness_file(self, text: str) -> Path:
        self._tmpdir = tempfile.TemporaryDirectory()
        p = Path(self._tmpdir.name) / "AdapterCorrectness.lean"
        p.write_text(textwrap.dedent(text), encoding="utf-8")
        return p

    def tearDown(self) -> None:
        if hasattr(self, "_tmpdir"):
            self._tmpdir.cleanup()

    def test_extracts_assign_and_for_theorems(self) -> None:
        p = self._write_correctness_file("""\
            theorem assign_equiv_let : True := by
              trivial
            theorem for_init_hoisting : True := by
              trivial
        """)
        with patch.object(gen, "CORRECTNESS_FILE", p), \
             patch.object(gen, "ROOT", Path(self._tmpdir.name)):
            result = gen._parse_correctness_proofs()
        self.assertIn("assign_to_let", result)
        self.assertIn("for_init_hoisting", result)
        self.assertIn("proven", result["assign_to_let"])
        self.assertIn("proven", result["for_init_hoisting"])

    def test_marks_correctness_family_sorry_when_body_contains_sorry(self) -> None:
        p = self._write_correctness_file("""\
            theorem assign_equiv_let : True := by
              trivial
            theorem for_init_hoisting : True := by
              sorry
        """)
        with patch.object(gen, "CORRECTNESS_FILE", p), \
             patch.object(gen, "ROOT", Path(self._tmpdir.name)):
            result = gen._parse_correctness_proofs()
        self.assertIn("proven", result["assign_to_let"])
        self.assertIn("sorry", result["for_init_hoisting"])

    def test_empty_theorems_raises(self) -> None:
        p = self._write_correctness_file("""\
            -- no theorems here, just comments
            def helper := 42
        """)
        with patch.object(gen, "CORRECTNESS_FILE", p), \
             patch.object(gen, "ROOT", Path(self._tmpdir.name)):
            with self.assertRaises(ValueError, msg="No correctness theorems found"):
                gen._parse_correctness_proofs()

    def test_ignores_theorems_inside_block_comments(self) -> None:
        p = self._write_correctness_file("""\
            /-
            theorem assign_equiv_let := by
              trivial
            theorem for_init_hoisting := by
              trivial
            -/
            def helper := 42
        """)
        with patch.object(gen, "CORRECTNESS_FILE", p), \
             patch.object(gen, "ROOT", Path(self._tmpdir.name)):
            with self.assertRaises(ValueError, msg="No correctness theorems found"):
                gen._parse_correctness_proofs()

    def test_missing_file_raises(self) -> None:
        with patch.object(gen, "CORRECTNESS_FILE", Path("/nonexistent/Correctness.lean")):
            with self.assertRaises(FileNotFoundError):
                gen._parse_correctness_proofs()


class ExtractBlockTests(unittest.TestCase):
    """Tests for _extract_block."""

    def test_extracts_between_markers(self) -> None:
        text = "before\ndef foo\n  line1\n  line2\ndef bar\n  baz"
        lines = gen._extract_block(text, "def foo", "def bar")
        self.assertIn("def foo", "\n".join(lines))
        self.assertNotIn("def bar", "\n".join(lines))

    def test_missing_start_raises(self) -> None:
        with self.assertRaises(ValueError):
            gen._extract_block("some text", "MISSING_START", "end")

    def test_missing_end_raises(self) -> None:
        with self.assertRaises(ValueError):
            gen._extract_block("start marker here", "start marker", "MISSING_END")


class RepoArtifactConsistencyTests(unittest.TestCase):
    """End-to-end: the generated report matches the checked-in artifact."""

    def test_artifact_is_up_to_date(self) -> None:
        report = gen.build_report()
        rendered = json.dumps(report, sort_keys=True, indent=2) + "\n"
        existing = gen.DEFAULT_OUTPUT.read_text(encoding="utf-8")
        self.assertEqual(
            existing,
            rendered,
            "Adapter report artifact is stale. Regenerate with:\n"
            "  python3 scripts/generate_evmyullean_adapter_report.py",
        )

    def test_admitted_lemmas_are_subset_of_universal(self) -> None:
        report = gen.build_report()
        universal = set(report["universal_bridge_lemmas"])
        admitted = set(report["admitted_bridge_lemmas"])
        self.assertTrue(
            admitted <= universal,
            f"Admitted lemmas not in universal set: {admitted - universal}",
        )

    def test_fully_proven_equals_universal_minus_admitted(self) -> None:
        report = gen.build_report()
        universal = set(report["universal_bridge_lemmas"])
        admitted = set(report["admitted_bridge_lemmas"])
        fully_proven = set(report["fully_proven_bridge_lemmas"])
        self.assertEqual(
            fully_proven,
            universal - admitted,
            "fully_proven_bridge_lemmas must equal universal minus admitted",
        )

    def test_concrete_bridge_inventory_preserved_when_universal_lemmas_exist(self) -> None:
        report = gen.build_report()
        concrete = set(report["concrete_bridge_tests"])
        universal = set(report["universal_bridge_lemmas"])
        concrete_only = set(report["concrete_only_bridge_tests"])

        self.assertTrue(concrete, "concrete bridge inventory should list the tested builtins")
        self.assertEqual(
            concrete_only,
            concrete - universal,
            "concrete_only_bridge_tests must equal concrete_bridge_tests minus universal_bridge_lemmas",
        )
        self.assertGreaterEqual(
            report["concrete_test_count"],
            len(concrete),
            "concrete test count should cover at least the distinct concretely tested builtins",
        )

    def test_nonzero_bridge_test_count_requires_nonempty_inventory(self) -> None:
        with patch.object(gen, "_parse_bridge_tests", return_value=([], 1)):
            with self.assertRaisesRegex(ValueError, "credited no builtins"):
                gen.build_report()

    def test_context_lifted_bridge_lemmas_present(self) -> None:
        report = gen.build_report()
        context = report.get("context_lifted_bridge_lemmas", [])
        self.assertTrue(
            context,
            "context_lifted_bridge_lemmas should be non-empty",
        )
        # Every context-lifted bridge should be a real bridged builtin.
        bridged = set(report.get("bridged_builtins", []))
        for b in context:
            self.assertIn(
                b, bridged,
                f"context-lifted bridge {b!r} not in bridged_builtins",
            )

    def test_fallthrough_lemmas_match_unbridged(self) -> None:
        report = gen.build_report()
        fallthrough = set(report.get("fallthrough_lemmas", []))
        unbridged = set(report.get("unbridged_builtins", []))
        self.assertEqual(
            fallthrough,
            unbridged,
            "fallthrough_lemmas should match unbridged_builtins",
        )

    def test_bridged_builtins_cover_all_proven_and_admitted(self) -> None:
        report = gen.build_report()
        bridged = set(report.get("bridged_builtins", []))
        universal = set(report["universal_bridge_lemmas"])
        self.assertTrue(
            universal <= bridged,
            f"Universal bridge lemmas not in bridged set: {universal - bridged}",
        )

    def test_scalar_parameter_body_closure_is_tracked(self) -> None:
        report = gen.build_report()
        phase4 = report["phase4_retarget"]
        self.assertEqual(
            phase4["genParamLoads_scalar_bridged"],
            "proven (scalar calldata parameters)",
        )
        self.assertEqual(
            phase4["genStaticTypeLoads_calldataload_bridged"],
            "proven (static scalar calldata leaves)",
        )
        self.assertEqual(
            phase4["genParamLoads_static_scalar_bridged"],
            "proven (static scalar calldata parameters)",
        )
        self.assertEqual(
            phase4["compileStmtList_binding_leaf_bridged"],
            "proven (scalar let/assign statement lists)",
        )
        self.assertEqual(
            phase4["compileStmtList_pure_binding_bridged"],
            "proven (pure let/assign statement lists)",
        )
        self.assertEqual(
            phase4["compileStmtList_storage_fragment_bridged"],
            "proven (pure bindings plus single-slot setStorage statement lists)",
        )
        self.assertEqual(
            phase4["compileStmtList_terminator_external_bridged"],
            "proven (external stop/return statement lists)",
        )
        self.assertEqual(
            phase4["compileStmtList_internal_return_bridged"],
            "proven (internal return statement lists)",
        )
        self.assertEqual(
            phase4["compileStmtList_require_bridged"],
            "proven (require statement lists)",
        )
        self.assertEqual(
            phase4["compileStmtList_external_body_fragment_bridged"],
            "proven (mixed external body fragment)",
        )
        self.assertEqual(
            phase4["compileStmtList_internal_body_fragment_bridged"],
            "proven (mixed internal body fragment)",
        )
        self.assertEqual(
            phase4["compileStmtList_external_structured_body_fragment_bridged"],
            "proven (mixed external body fragment plus one ite layer)",
        )
        self.assertEqual(
            phase4["compileStmtList_internal_structured_body_fragment_bridged"],
            "proven (mixed internal body fragment plus one ite layer)",
        )
        self.assertEqual(
            phase4["compileStmtList_external_nested_body_fragment_bridged"],
            "proven (mixed external body fragment plus two ite layers)",
        )
        self.assertEqual(
            phase4["compileStmtList_internal_nested_body_fragment_bridged"],
            "proven (mixed internal body fragment plus two ite layers)",
        )
        self.assertEqual(
            phase4["compileStmtList_external_recursive_body_fragment_bridged"],
            "proven (mixed external body fragment plus recursive ite closure)",
        )
        self.assertEqual(
            phase4["compileStmtList_internal_recursive_body_fragment_bridged"],
            "proven (mixed internal body fragment plus recursive ite closure)",
        )
        self.assertEqual(
            phase4["compileExpr_bridgedSource_leaf"],
            "proven (scalar source-expression leaves)",
        )
        self.assertEqual(
            phase4["compileExpr_bridgedSource"],
            "proven (pure source-expression fragment)",
        )

    def test_missing_retarget_theorem_is_not_reported_proven(self) -> None:
        with tempfile.TemporaryDirectory(dir=gen.ROOT) as tmp:
            retarget = Path(tmp) / "EvmYulLeanRetarget.lean"
            retarget.write_text(
                textwrap.dedent("""\
                    /-- Mentions backends_agree_on_bridged_builtins only in prose. -/
                    theorem other_theorem : True := by trivial
                """),
                encoding="utf-8",
            )
            with patch.object(gen, "RETARGET_FILE", retarget):
                report = gen.build_report()
        phase4 = report["phase4_retarget"]
        self.assertEqual(phase4["status"], "incomplete")
        self.assertEqual(phase4["backends_agree_on_bridged_builtins"], "missing")
        self.assertEqual(phase4["evalYulExpr_evmYulLean_eq_on_bridged"], "missing")
        self.assertEqual(
            phase4["execYulFuelWithBackend_eq_on_bridged_straight_stmts"],
            "missing",
        )
        self.assertEqual(
            phase4["execYulFuelWithBackend_block_eq_on_bridged_straight_stmts"],
            "missing",
        )
        self.assertEqual(
            phase4["execYulFuelWithBackend_if_eq_on_bridged_body"],
            "missing",
        )
        self.assertEqual(
            phase4["execYulFuelWithBackend_switch_eq_on_bridged_cases"],
            "missing",
        )
        self.assertEqual(
            phase4["execYulFuelWithBackend_for_eq_on_bridged_parts"],
            "missing",
        )
        self.assertEqual(
            phase4["execYulFuelWithBackend_eq_on_bridged_target"],
            "missing",
        )
        self.assertEqual(phase4["emitYul_runtimeCode_bridged"], "missing")
        self.assertEqual(
            phase4["emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies"],
            "missing",
        )
        self.assertEqual(
            phase4["yulCodegen_preserves_semantics_evmYulLean"],
            "missing",
        )

    def test_retarget_theorem_name_inside_string_is_not_reported_proven(self) -> None:
        with tempfile.TemporaryDirectory(dir=gen.ROOT) as tmp:
            retarget = Path(tmp) / "EvmYulLeanRetarget.lean"
            retarget.write_text(
                textwrap.dedent('''\
                    def decoy : String :=
                      "theorem backends_agree_on_bridged_builtins : True := by sorry"

                    theorem other_theorem : True := by trivial
                '''),
                encoding="utf-8",
            )
            with patch.object(gen, "RETARGET_FILE", retarget):
                report = gen.build_report()
        phase4 = report["phase4_retarget"]
        self.assertEqual(phase4["status"], "incomplete")
        self.assertEqual(phase4["backends_agree_on_bridged_builtins"], "missing")

    def test_sorry_retarget_theorem_downgrades_phase4_status(self) -> None:
        with tempfile.TemporaryDirectory(dir=gen.ROOT) as tmp:
            retarget = Path(tmp) / "EvmYulLeanRetarget.lean"
            retarget.write_text(
                textwrap.dedent("""\
                    theorem backends_agree_on_bridged_builtins : True := by
                      trivial

                    theorem evalYulExpr_evmYulLean_eq_on_bridged : True := by
                      sorry

                    theorem execYulFuelWithBackend_eq_on_bridged_straight_stmts : True := by
                      trivial

                    theorem execYulFuelWithBackend_block_eq_on_bridged_straight_stmts : True := by
                      trivial

                    theorem execYulFuelWithBackend_if_eq_on_bridged_body : True := by
                      trivial

                    theorem execYulFuelWithBackend_switch_eq_on_bridged_cases : True := by
                      trivial

                    theorem execYulFuelWithBackend_for_eq_on_bridged_parts : True := by
                      trivial

                    theorem execYulFuelWithBackend_eq_on_bridged_target : True := by
                      trivial

                    theorem emitYul_runtimeCode_bridged : True := by
                      trivial

                    theorem emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies : True := by
                      trivial

                    theorem yulCodegen_preserves_semantics_evmYulLean : True := by
                      trivial
                """),
                encoding="utf-8",
            )
            with patch.object(gen, "RETARGET_FILE", retarget):
                with patch.object(gen, "_parse_bridge_lemmas", return_value=(["add"], [])):
                    report = gen.build_report()
        phase4 = report["phase4_retarget"]
        self.assertEqual(phase4["status"], "pointwise")
        self.assertEqual(phase4["backends_agree_on_bridged_builtins"], "proven")
        self.assertEqual(phase4["evalYulExpr_evmYulLean_eq_on_bridged"], "sorry")
        self.assertEqual(
            phase4["execYulFuelWithBackend_eq_on_bridged_straight_stmts"],
            "proven",
        )
        self.assertEqual(
            phase4["execYulFuelWithBackend_block_eq_on_bridged_straight_stmts"],
            "proven",
        )
        self.assertEqual(
            phase4["execYulFuelWithBackend_if_eq_on_bridged_body"],
            "proven",
        )
        self.assertEqual(
            phase4["execYulFuelWithBackend_switch_eq_on_bridged_cases"],
            "proven",
        )
        self.assertEqual(
            phase4["execYulFuelWithBackend_for_eq_on_bridged_parts"],
            "proven",
        )
        self.assertEqual(
            phase4["execYulFuelWithBackend_eq_on_bridged_target"],
            "proven",
        )
        self.assertEqual(
            phase4["emitYul_runtimeCode_bridged"],
            "proven (conditional on bridged IR bodies)",
        )
        self.assertEqual(
            phase4["emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies"],
            "proven (conditional on bridged IR bodies)",
        )
        self.assertEqual(
            phase4["yulCodegen_preserves_semantics_evmYulLean"],
            "proven (conditional on bridged IR bodies)",
        )
        self.assertEqual(phase4["admitted_bridge_dependencies"], [])

    def test_top_level_local_sorry_does_not_downgrade_prior_retarget_theorem(self) -> None:
        with tempfile.TemporaryDirectory(dir=gen.ROOT) as tmp:
            retarget = Path(tmp) / "EvmYulLeanRetarget.lean"
            retarget.write_text(
                textwrap.dedent("""\
                    theorem backends_agree_on_bridged_builtins : True := by
                      trivial

                    local def helper : True := by
                      sorry

                    theorem evalYulExpr_evmYulLean_eq_on_bridged : True := by
                      trivial
                """),
                encoding="utf-8",
            )
            with patch.object(gen, "RETARGET_FILE", retarget):
                with patch.object(gen, "_parse_bridge_lemmas", return_value=(["add"], [])):
                    report = gen.build_report()
        phase4 = report["phase4_retarget"]
        self.assertEqual(phase4["backends_agree_on_bridged_builtins"], "proven")
        self.assertEqual(phase4["evalYulExpr_evmYulLean_eq_on_bridged"], "proven")

    def test_nested_local_theorem_does_not_satisfy_retarget_presence(self) -> None:
        with tempfile.TemporaryDirectory(dir=gen.ROOT) as tmp:
            retarget = Path(tmp) / "EvmYulLeanRetarget.lean"
            retarget.write_text(
                textwrap.dedent("""\
                    theorem wrapper : True := by
                      local theorem backends_agree_on_bridged_builtins : True := by
                        trivial
                      trivial
                """),
                encoding="utf-8",
            )
            with patch.object(gen, "RETARGET_FILE", retarget):
                with patch.object(gen, "_parse_bridge_lemmas", return_value=(["add"], [])):
                    report = gen.build_report()
        phase4 = report["phase4_retarget"]
        self.assertEqual(phase4["backends_agree_on_bridged_builtins"], "missing")
        self.assertEqual(phase4["status"], "incomplete")

    def test_admitted_bridge_deps_downgrade_phase4_status(self) -> None:
        with tempfile.TemporaryDirectory(dir=gen.ROOT) as tmp:
            retarget = Path(tmp) / "EvmYulLeanRetarget.lean"
            retarget.write_text(
                textwrap.dedent("""\
                    theorem backends_agree_on_bridged_builtins : True := by
                      trivial

                    theorem evalYulExpr_evmYulLean_eq_on_bridged : True := by
                      trivial

                    theorem execYulFuelWithBackend_eq_on_bridged_straight_stmts : True := by
                      trivial

                    theorem execYulFuelWithBackend_block_eq_on_bridged_straight_stmts : True := by
                      trivial

                    theorem execYulFuelWithBackend_if_eq_on_bridged_body : True := by
                      trivial

                    theorem execYulFuelWithBackend_switch_eq_on_bridged_cases : True := by
                      trivial

                    theorem execYulFuelWithBackend_for_eq_on_bridged_parts : True := by
                      trivial

                    theorem execYulFuelWithBackend_eq_on_bridged_target : True := by
                      trivial

                    theorem emitYul_runtimeCode_bridged : True := by
                      trivial

                    theorem emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies : True := by
                      trivial

                    theorem yulCodegen_preserves_semantics_evmYulLean : True := by
                      trivial
                """),
                encoding="utf-8",
            )
            with patch.object(gen, "RETARGET_FILE", retarget):
                with patch.object(
                    gen,
                    "_parse_bridge_lemmas",
                    return_value=(["add", "smod", "sar"], ["smod", "sar"]),
                ):
                    report = gen.build_report()
        phase4 = report["phase4_retarget"]
        self.assertEqual(phase4["status"], "incomplete")
        self.assertEqual(phase4["admitted_bridge_dependencies"], ["sar", "smod"])
        self.assertIn("sorry-dependent", phase4["backends_agree_on_bridged_builtins"])
        self.assertIn("smod", phase4["evalYulExpr_evmYulLean_eq_on_bridged"])
        self.assertIn(
            "smod",
            phase4["execYulFuelWithBackend_eq_on_bridged_straight_stmts"],
        )
        self.assertIn(
            "smod",
            phase4["execYulFuelWithBackend_block_eq_on_bridged_straight_stmts"],
        )
        self.assertIn(
            "smod",
            phase4["execYulFuelWithBackend_if_eq_on_bridged_body"],
        )
        self.assertIn(
            "smod",
            phase4["execYulFuelWithBackend_switch_eq_on_bridged_cases"],
        )
        self.assertIn(
            "smod",
            phase4["execYulFuelWithBackend_for_eq_on_bridged_parts"],
        )
        self.assertIn(
            "smod",
            phase4["execYulFuelWithBackend_eq_on_bridged_target"],
        )
        self.assertEqual(
            phase4["emitYul_runtimeCode_bridged"],
            "proven (conditional on bridged IR bodies)",
        )
        self.assertIn(
            "smod",
            phase4["emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies"],
        )
        self.assertIn(
            "smod",
            phase4["yulCodegen_preserves_semantics_evmYulLean"],
        )


class ParseContextBridgeLemmasTests(unittest.TestCase):
    """Tests for _parse_context_bridge_lemmas."""

    def _write_lemma_file(self, text: str) -> Path:
        self._tmpdir = tempfile.TemporaryDirectory()
        p = Path(self._tmpdir.name) / "BridgeLemmas.lean"
        p.write_text(textwrap.dedent(text), encoding="utf-8")
        return p

    def tearDown(self) -> None:
        if hasattr(self, "_tmpdir"):
            self._tmpdir.cleanup()

    def test_extracts_context_bridge_and_fallthrough(self) -> None:
        p = self._write_lemma_file("""\
            @[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_add_bridge := by sorry
            theorem evalBuiltinCallWithBackendContext_evmYulLean_pure_bridge := by sorry
            @[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sload_none := by sorry
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            context, fallthrough = gen._parse_context_bridge_lemmas()
        self.assertEqual(context, ["add"])
        self.assertEqual(fallthrough, ["sload"])

    def test_ignores_commented_theorems(self) -> None:
        p = self._write_lemma_file("""\
            /-
            @[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_fake_bridge := by sorry
            -/
            @[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_add_bridge := by sorry
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            context, fallthrough = gen._parse_context_bridge_lemmas()
        self.assertEqual(context, ["add"])
        self.assertEqual(fallthrough, [])


class ParseBridgedBuiltinsDefsTests(unittest.TestCase):
    """Tests for _parse_bridged_builtins_defs."""

    def _write_lemma_file(self, text: str) -> Path:
        self._tmpdir = tempfile.TemporaryDirectory()
        p = Path(self._tmpdir.name) / "BridgeLemmas.lean"
        p.write_text(textwrap.dedent(text), encoding="utf-8")
        return p

    def tearDown(self) -> None:
        if hasattr(self, "_tmpdir"):
            self._tmpdir.cleanup()

    def test_extracts_bridged_and_unbridged(self) -> None:
        p = self._write_lemma_file("""\
            def bridgedBuiltins : List String :=
              ["add", "sub", "caller"]

            def unbridgedBuiltins : List String := ["sload", "mappingSlot"]
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            bridged, unbridged = gen._parse_bridged_builtins_defs()
        self.assertEqual(bridged, ["add", "caller", "sub"])
        self.assertEqual(unbridged, ["mappingSlot", "sload"])

    def test_missing_defs_return_empty(self) -> None:
        p = self._write_lemma_file("""\
            -- no defs here
            theorem foo := by sorry
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            bridged, unbridged = gen._parse_bridged_builtins_defs()
        self.assertEqual(bridged, [])
        self.assertEqual(unbridged, [])


if __name__ == "__main__":
    unittest.main()
