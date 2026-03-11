from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_layer2_boundary_sync as check


class Layer2BoundarySyncTests(unittest.TestCase):
    def _write_fixture_tree(self, root: Path, *, use_expected: bool, add_forbidden: bool) -> None:
        expected = check.expected_snippets()
        forbidden = check.forbidden_snippets()
        for label, path in check.TARGETS.items():
            target = root / path.relative_to(check.ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            parts: list[str] = []
            if use_expected:
                parts.extend(expected.get(label, []))
            if add_forbidden:
                parts.extend(forbidden.get(label, []))
            if not parts:
                parts.append(f"{label} placeholder")
            target.write_text("\n".join(parts) + "\n", encoding="utf-8")

    def _run_check(self, *, use_expected: bool, add_forbidden: bool) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(root, use_expected=use_expected, add_forbidden=add_forbidden)

            old_root = check.ROOT
            old_targets = check.TARGETS
            check.ROOT = root
            check.TARGETS = {
                label: root / path.relative_to(old_root)
                for label, path in old_targets.items()
            }
            try:
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check.main()
                return rc, stdout.getvalue() + stderr.getvalue()
            finally:
                check.ROOT = old_root
                check.TARGETS = old_targets

    def test_matching_docs_pass(self) -> None:
        rc, output = self._run_check(use_expected=True, add_forbidden=False)
        self.assertEqual(rc, 0, output)
        self.assertIn("layer2 boundary sync passed", output)

    def test_missing_required_snippet_fails(self) -> None:
        rc, output = self._run_check(use_expected=False, add_forbidden=False)
        self.assertEqual(rc, 1)
        self.assertIn("missing `there is not yet a single generic theorem saying", output)

    def test_forbidden_overclaim_fails(self) -> None:
        rc, output = self._run_check(use_expected=True, add_forbidden=True)
        self.assertEqual(rc, 1)
        self.assertIn("still over-claims the Layer 2 boundary", output)

    def test_detects_stale_axiom_count_language(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(root, use_expected=True, add_forbidden=False)
            target = root / check.TARGETS["ROOT_README"].relative_to(check.ROOT)
            target.write_text(
                target.read_text(encoding="utf-8").replace(
                    "There are currently 2 documented Lean axioms in total: 1 selector axiom and 1 generic non-core Layer 2 axiom.",
                    "There are currently 3 documented Lean axioms in total: 1 selector axiom, 1 generic non-core Layer 2 axiom, and 1 Layer 3 dispatch bridge axiom.",
                ),
                encoding="utf-8",
            )

            old_root = check.ROOT
            old_targets = check.TARGETS
            check.ROOT = root
            check.TARGETS = {
                label: root / path.relative_to(old_root)
                for label, path in old_targets.items()
            }
            try:
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check.main()
                output = stdout.getvalue() + stderr.getvalue()
            finally:
                check.ROOT = old_root
                check.TARGETS = old_targets

        self.assertEqual(rc, 1)
        self.assertIn("There are currently 3 documented Lean axioms in total", output)

    def test_compiler_proofs_readme_stale_axiom_wording_is_forbidden(self) -> None:
        forbidden = check.forbidden_snippets()
        self.assertIn("COMPILER_PROOFS_README", forbidden)
        self.assertIn(
            "it still depends on 2 documented axioms in `Compiler.Proofs.IRGeneration.Function`",
            forbidden["COMPILER_PROOFS_README"],
        )

    def test_repository_docs_are_currently_in_sync(self) -> None:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = check.main()
        output = stdout.getvalue() + stderr.getvalue()
        self.assertEqual(rc, 0, output)


if __name__ == "__main__":
    unittest.main()
