#!/usr/bin/env python3
"""Tests for generate_evmyullean_native_lowering_report.py.

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

import generate_evmyullean_native_lowering_report as gen


class ParseNativeLoweringCasesTests(unittest.TestCase):
    def test_parse_cases_marks_throw_interpolation_as_gap(self) -> None:
        lines = textwrap.dedent("""\
            def lowerStmtGroupNativeWithSwitchIds : YulStmt -> Except String Unit
              | .comment _ => pure ()
              | .funcDef name _ _ _ =>
                  throw s!"native EVMYulLean statement lowering cannot inline function definition '{name}'"
        """).splitlines()

        self.assertEqual(
            gen._parse_cases(lines),
            {"comment": "supported", "funcDef": "gap"},
        )
        self.assertEqual(
            gen._parse_gap_messages(lines),
            {
                "funcDef": [
                    "native EVMYulLean statement lowering cannot inline function definition '{name}'"
                ]
            },
        )


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

    def test_ignores_nested_bridge_name_inside_proof_body(self) -> None:
        """Indented ``have evalBuiltinCall_X_bridge`` inside a proof must not
        count as a top-level universal bridge lemma."""
        p = self._write_lemma_file("""\
            @[simp] theorem evalBuiltinCall_add_bridge := by
              have inner_theorem_evalBuiltinCall_fake_bridge : True := trivial
              exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(all_lemmas, ["add"])
        self.assertEqual(admitted, [])

    def test_indented_theorem_not_treated_as_top_level(self) -> None:
        """A ``theorem evalBuiltinCall_X_bridge`` that is not at column 0 with
        only declaration modifiers before it must not be counted."""
        p = self._write_lemma_file("""\
            @[simp] theorem evalBuiltinCall_add_bridge := by
              exact trivial
              -- not a real declaration, just text:
              /- theorem evalBuiltinCall_not_real_bridge -/
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(all_lemmas, ["add"])

    def test_ignores_bridge_theorem_name_inside_string_literal(self) -> None:
        """A ``theorem evalBuiltinCall_X_bridge`` pattern appearing inside a
        Lean string literal (e.g., error message, doc reference) must not be
        counted as a real bridge declaration; otherwise the universal-bridge
        coverage count could be overstated even after an actual theorem is
        removed or renamed."""
        p = self._write_lemma_file('''\
            theorem evalBuiltinCall_add_bridge := by
              exact trivial

            -- A string literal that mentions a theorem-shaped name, which must
            -- NOT be interpreted as a second bridge lemma.
            def diagnosticMessage : String :=
              "theorem evalBuiltinCall_phantom_bridge was removed; see PR #1725"
        ''')
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(all_lemmas, ["add"])
        self.assertEqual(admitted, [])

    def test_ignores_sorry_inside_string_literal(self) -> None:
        p = self._write_lemma_file('''\
            private theorem diagnostic : String := "sorry appears only in text"

            theorem evalBuiltinCall_add_bridge := by
              exact trivial
        ''')
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(all_lemmas, ["add"])
        self.assertEqual(admitted, [])

    def test_marks_each_bridge_that_uses_sorry_helper(self) -> None:
        p = self._write_lemma_file("""\
            private theorem shared_core : True := by
              sorry

            theorem evalBuiltinCall_exp_bridge := by
              exact shared_core

            theorem evalBuiltinCall_sar_bridge := by
              exact shared_core

            theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(all_lemmas, ["add", "exp", "sar"])
        self.assertEqual(admitted, ["exp", "sar"])

    def test_tracks_transitive_admitted_helper_dependencies(self) -> None:
        p = self._write_lemma_file("""\
            private theorem core_sorry : True := by
              sorry

            private theorem wrapped_core : True := by
              exact core_sorry

            theorem evalBuiltinCall_sar_bridge := by
              exact wrapped_core

            theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(all_lemmas, ["add", "sar"])
        self.assertEqual(admitted, ["sar"])

    def test_resets_sorry_helper_at_scope_boundary(self) -> None:
        p = self._write_lemma_file("""\
            namespace Scratch
            private theorem scoped_core : True := by
              sorry
            end Scratch

            theorem evalBuiltinCall_add_bridge := by
              exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            _all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(admitted, [])

    def test_anonymous_instance_is_separate_bridge_boundary(self) -> None:
        p = self._write_lemma_file("""\
            theorem evalBuiltinCall_add_bridge := by
              exact trivial

            instance : Inhabited True := by
              sorry

            theorem evalBuiltinCall_exp_bridge := by
              exact trivial
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            _all_lemmas, admitted = gen._parse_bridge_lemmas()
        self.assertEqual(admitted, ["exp"])


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

    def test_ignores_bridge_equality_inside_string_literal(self) -> None:
        """A bridge-equality pattern appearing inside a Lean string literal
        (e.g., error messages, doc strings) must not inflate the test count."""
        p = self._write_test_file('''\
            example :=
              let msg := "example := verityEvalBuiltin \\"fake\\" [1, 2] = bridgeEval \\"fake\\" [1, 2] := by native_decide"
              True := by native_decide
            example := verityEvalBuiltin "add" [1, 2] = bridgeEval "add" [1, 2] := by native_decide
        ''')
        with patch.object(gen, "BRIDGE_TEST_FILE", p):
            builtins, count = gen._parse_bridge_tests()
        self.assertEqual(count, 1)
        self.assertEqual(builtins, ["add"])


class ParseCorrectnessProofsTests(unittest.TestCase):
    """Tests for _parse_correctness_proofs."""

    def _write_correctness_file(self, text: str) -> Path:
        self._tmpdir = tempfile.TemporaryDirectory()
        p = Path(self._tmpdir.name) / "NativeHarness.lean"
        p.write_text(textwrap.dedent(text), encoding="utf-8")
        return p

    def tearDown(self) -> None:
        if hasattr(self, "_tmpdir"):
            self._tmpdir.cleanup()

    def test_reports_present_native_harness_markers(self) -> None:
        p = self._write_correctness_file("""\
            def lowerRuntimeContractNative := 1
            inductive NativeGeneratedSelectorHitSuccessBridge where
              | done
        """)
        with patch.object(gen, "CORRECTNESS_FILE", p), \
             patch.object(gen, "ROOT", Path(self._tmpdir.name)):
            result = gen._parse_correctness_proofs()
        self.assertEqual(result["runtime_lowering"], "present")
        self.assertEqual(result["dispatcher_tail"], "present")

    def test_missing_native_harness_markers_report_missing(self) -> None:
        p = self._write_correctness_file("""\
            def helper := 42
        """)
        with patch.object(gen, "CORRECTNESS_FILE", p), \
             patch.object(gen, "ROOT", Path(self._tmpdir.name)):
            result = gen._parse_correctness_proofs()
        self.assertEqual(result["runtime_lowering"], "missing")
        self.assertEqual(result["dispatcher_tail"], "missing")

    def test_missing_file_reports_missing(self) -> None:
        """The native harness status is fail-closed when the source file is absent."""
        with patch.object(gen, "CORRECTNESS_FILE", Path("/nonexistent/Correctness.lean")):
            result = gen._parse_correctness_proofs()
        self.assertEqual(result["runtime_lowering"], "missing")
        self.assertEqual(result["dispatcher_tail"], "missing")


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
            "Native lowering report artifact is stale. Regenerate with:\n"
            "  python3 scripts/generate_evmyullean_native_lowering_report.py",
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

    def test_concrete_bridge_inventory_matches_reported_count(self) -> None:
        report = gen.build_report()
        concrete = set(report["concrete_bridge_tests"])
        universal = set(report["universal_bridge_lemmas"])
        concrete_only = set(report["concrete_only_bridge_tests"])

        self.assertEqual(
            concrete_only,
            concrete - universal,
            "concrete_only_bridge_tests must equal concrete_bridge_tests minus universal_bridge_lemmas",
        )
        self.assertEqual(
            report["concrete_test_count"],
            len(concrete),
            "concrete test count should match the distinct concretely tested builtins",
        )

    def test_nonzero_bridge_test_count_requires_nonempty_inventory(self) -> None:
        with patch.object(gen, "_parse_bridge_tests", return_value=([], 1)):
            with self.assertRaisesRegex(ValueError, "credited no builtins"):
                gen.build_report()

    def test_native_context_bridge_lemmas_present(self) -> None:
        report = gen.build_report()
        context = report.get("native_context_bridge_lemmas", [])
        self.assertTrue(
            context,
            "native_context_bridge_lemmas should be non-empty",
        )
        # Every native context bridge should be a real bridged builtin.
        bridged = set(report.get("bridged_builtins", []))
        for b in context:
            self.assertIn(
                b, bridged,
                f"native context bridge {b!r} not in bridged_builtins",
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

    def test_removed_transition_payload_is_absent(self) -> None:
        report = gen.build_report()
        self.assertNotIn("phase4_" + "retarget", report)

    def test_schema_version_current(self) -> None:
        report = gen.build_report()
        self.assertEqual(report["schema_version"], 8)


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
            @[simp] theorem evalBuiltinCall_add_bridge := by sorry
            theorem evalBuiltinCall_pure_bridge := by sorry
            @[simp] theorem evalBuiltinCall_sload_none := by sorry
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            context, fallthrough = gen._parse_context_bridge_lemmas()
        self.assertEqual(context, ["add"])
        self.assertEqual(fallthrough, ["sload"])

    def test_ignores_commented_theorems(self) -> None:
        p = self._write_lemma_file("""\
            /-
            @[simp] theorem evalBuiltinCall_fake_bridge := by sorry
            -/
            @[simp] theorem evalBuiltinCall_add_bridge := by sorry
        """)
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            context, fallthrough = gen._parse_context_bridge_lemmas()
        self.assertEqual(context, ["add"])
        self.assertEqual(fallthrough, [])

    def test_ignores_string_literal_theorem_text(self) -> None:
        p = self._write_lemma_file('''\
            def msg : String :=
              "theorem evalBuiltinCall_fake_bridge := by sorry"

            @[simp] theorem evalBuiltinCall_add_bridge := by sorry
        ''')
        with patch.object(gen, "BRIDGE_LEMMAS_FILE", p):
            context, fallthrough = gen._parse_context_bridge_lemmas()
        self.assertEqual(context, ["add"])
        self.assertEqual(fallthrough, [])

    def test_ignores_nested_local_context_theorem(self) -> None:
        p = self._write_lemma_file("""\
            theorem wrapper : True := by
              local theorem evalBuiltinCall_fake_bridge : True := by
                trivial
              trivial

            @[simp] theorem evalBuiltinCall_add_bridge := by sorry
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
        with patch.object(gen, "BRIDGE_PREDICATES_FILE", p):
            bridged, unbridged = gen._parse_bridged_builtins_defs()
        self.assertEqual(bridged, ["add", "caller", "sub"])
        self.assertEqual(unbridged, ["mappingSlot", "sload"])

    def test_missing_defs_return_empty(self) -> None:
        p = self._write_lemma_file("""\
            -- no defs here
            theorem foo := by sorry
        """)
        with patch.object(gen, "BRIDGE_PREDICATES_FILE", p):
            bridged, unbridged = gen._parse_bridged_builtins_defs()
        self.assertEqual(bridged, [])
        self.assertEqual(unbridged, [])


if __name__ == "__main__":
    unittest.main()
