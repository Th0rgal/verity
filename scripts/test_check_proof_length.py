#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_proof_length


class MeasureProofsTests(unittest.TestCase):
    def _write_lean(self, content: str) -> Path:
        """Write Lean content to a temp file and return its path."""
        f = tempfile.NamedTemporaryFile(suffix=".lean", mode="w", delete=False)
        f.write(textwrap.dedent(content))
        f.close()
        return Path(f.name)

    def test_short_proof(self) -> None:
        path = self._write_lean(
            """\
            theorem short_one : True := by
              trivial
            """
        )
        results = check_proof_length.measure_proofs(path)
        self.assertEqual(len(results), 1)
        name, _, length = results[0]
        self.assertEqual(name, "short_one")
        self.assertLessEqual(length, 5)

    def test_long_proof_detected(self) -> None:
        body = "\n".join(f"  step{i}" for i in range(60))
        path = self._write_lean(
            f"theorem long_one : True := by\n{body}\n\ndef other := 1\n"
        )
        results = check_proof_length.measure_proofs(path)
        names = {r[0] for r in results}
        self.assertIn("long_one", names)
        for name, _, length in results:
            if name == "long_one":
                self.assertGreater(length, 50)

    def test_proof_ends_at_next_theorem(self) -> None:
        path = self._write_lean(
            """\
            theorem first : True := by
              trivial

            theorem second : True := by
              trivial
            """
        )
        results = check_proof_length.measure_proofs(path)
        self.assertEqual(len(results), 2)
        self.assertEqual(results[0][0], "first")
        self.assertEqual(results[1][0], "second")

    def test_proof_ends_at_partial_def(self) -> None:
        path = self._write_lean(
            """\
            theorem before_partial : True := by
              trivial

            partial def recursiveHelper : Nat -> Nat
              | 0 => 0
              | n + 1 => recursiveHelper n
            """
        )
        results = check_proof_length.measure_proofs(path)
        self.assertEqual(len(results), 1)
        name, _, length = results[0]
        self.assertEqual(name, "before_partial")
        self.assertLessEqual(length, 5)

    def test_lemma_detected(self) -> None:
        path = self._write_lean(
            """\
            lemma my_lemma : True := by
              trivial
            """
        )
        results = check_proof_length.measure_proofs(path)
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0][0], "my_lemma")

    def test_private_theorem_detected(self) -> None:
        path = self._write_lean(
            """\
            private theorem helper : True := by
              trivial
            """
        )
        results = check_proof_length.measure_proofs(path)
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0][0], "helper")

    def test_commented_theorem_ignored(self) -> None:
        path = self._write_lean(
            """\
            -- theorem not_real : True := by
            --   sorry

            theorem real_one : True := by
              trivial
            """
        )
        results = check_proof_length.measure_proofs(path)
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0][0], "real_one")

    def test_block_comment_theorem_ignored(self) -> None:
        path = self._write_lean(
            """\
            /-
            theorem fake : True := by
              sorry
            -/

            theorem real : True := by
              trivial
            """
        )
        results = check_proof_length.measure_proofs(path)
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0][0], "real")

    def test_proof_ends_at_end_keyword(self) -> None:
        path = self._write_lean(
            """\
            namespace Foo

            theorem inside : True := by
              trivial

            end Foo
            """
        )
        results = check_proof_length.measure_proofs(path)
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0][0], "inside")

    def test_empty_file(self) -> None:
        path = self._write_lean("")
        results = check_proof_length.measure_proofs(path)
        self.assertEqual(results, [])

    def test_no_theorems(self) -> None:
        path = self._write_lean(
            """\
            def myDef := 42

            structure Foo where
              x : Nat
            """
        )
        results = check_proof_length.measure_proofs(path)
        self.assertEqual(results, [])


class AllowlistTests(unittest.TestCase):
    def test_allowlist_entries_are_strings(self) -> None:
        for entry in check_proof_length.ALLOWLIST:
            self.assertIsInstance(entry, str)
            self.assertTrue(len(entry) > 0)


if __name__ == "__main__":
    unittest.main()
