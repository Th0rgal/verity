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
            theorem assign_equiv_let := by sorry
            theorem for_init_hoisting := by sorry
        """)
        with patch.object(gen, "CORRECTNESS_FILE", p), \
             patch.object(gen, "ROOT", Path(self._tmpdir.name)):
            result = gen._parse_correctness_proofs()
        self.assertIn("assign_to_let", result)
        self.assertIn("for_init_hoisting", result)

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


if __name__ == "__main__":
    unittest.main()
