from __future__ import annotations

import io
import json
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_low_level_call_boundary_sync as check


class LowLevelCallBoundarySyncTests(unittest.TestCase):
    def _write_fixture_tree(
        self,
        root: Path,
        *,
        proof_status: str,
        basic_status: str,
        fuel_status: str,
        edsl_doc: str,
        compiler_doc: str,
        solidity_guide: str,
    ) -> None:
        matrix = {
            "expr_features": [
                {
                    "feature": feature,
                    "proof_status": proof_status,
                    "SpecInterpreter_basic": basic_status,
                    "SpecInterpreter_fuel": fuel_status,
                }
                for feature in ("call", "staticcall", "delegatecall")
            ]
        }
        feature_matrix = root / "artifacts" / "interpreter_feature_matrix.json"
        feature_matrix.parent.mkdir(parents=True, exist_ok=True)
        feature_matrix.write_text(json.dumps(matrix), encoding="utf-8")

        edsl_path = root / "docs-site" / "content" / "edsl-api-reference.mdx"
        edsl_path.parent.mkdir(parents=True, exist_ok=True)
        edsl_path.write_text(edsl_doc, encoding="utf-8")

        compiler_path = root / "docs-site" / "content" / "compiler.mdx"
        compiler_path.parent.mkdir(parents=True, exist_ok=True)
        compiler_path.write_text(compiler_doc, encoding="utf-8")

        guide_path = root / "docs-site" / "content" / "guides" / "solidity-to-verity.mdx"
        guide_path.parent.mkdir(parents=True, exist_ok=True)
        guide_path.write_text(solidity_guide, encoding="utf-8")

    def _run_check(
        self,
        *,
        proof_status: str,
        basic_status: str,
        fuel_status: str,
        edsl_doc: str,
        compiler_doc: str,
        solidity_guide: str,
    ) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(
                root,
                proof_status=proof_status,
                basic_status=basic_status,
                fuel_status=fuel_status,
                edsl_doc=edsl_doc,
                compiler_doc=compiler_doc,
                solidity_guide=solidity_guide,
            )

            old_root = check.ROOT
            old_matrix = check.FEATURE_MATRIX
            old_targets = check.TARGET_FILES
            check.ROOT = root
            check.FEATURE_MATRIX = root / "artifacts" / "interpreter_feature_matrix.json"
            check.TARGET_FILES = {
                "EDSL_API": root / "docs-site" / "content" / "edsl-api-reference.mdx",
                "COMPILER_DOC": root / "docs-site" / "content" / "compiler.mdx",
                "SOLIDITY_GUIDE": root / "docs-site" / "content" / "guides" / "solidity-to-verity.mdx",
            }
            try:
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check.main()
                return rc, stdout.getvalue() + stderr.getvalue()
            finally:
                check.ROOT = old_root
                check.FEATURE_MATRIX = old_matrix
                check.TARGET_FILES = old_targets

    def test_boundary_note_required_when_calls_not_modeled(self) -> None:
        note = textwrap.dedent(
            """
            They are not yet modeled by the current proof interpreters.
            low-level call plumbing and returndata behavior remain a compiler-and-testing trust boundary rather than a proved semantic feature today.
            their runtime semantics are still outside the current proof-interpreter model.
            call success / returndata mechanics remain validated by differential testing and tracked under issue `#1332`.
            Those low-level call mechanics compile, but they are still outside the current proof-interpreter semantics; see issue `#1332`.
            """
        )
        rc, output = self._run_check(
            proof_status="not_modeled",
            basic_status="fallback_zero",
            fuel_status="fallback_zero",
            edsl_doc=note,
            compiler_doc=note,
            solidity_guide=note,
        )
        self.assertEqual(rc, 0, output)
        self.assertIn("boundary note required", output)

    def test_missing_boundary_note_fails_when_calls_not_modeled(self) -> None:
        rc, output = self._run_check(
            proof_status="not_modeled",
            basic_status="fallback_zero",
            fuel_status="fallback_zero",
            edsl_doc="low-level calls exist\n",
            compiler_doc="low-level calls compile\n",
            solidity_guide="use low-level call result checks\n",
        )
        self.assertEqual(rc, 1)
        self.assertIn("edsl-api-reference.mdx is out of sync", output)

    def test_boundary_note_not_required_once_calls_are_fully_modeled(self) -> None:
        rc, output = self._run_check(
            proof_status="proved",
            basic_status="supported",
            fuel_status="supported",
            edsl_doc="low-level calls exist\n",
            compiler_doc="low-level calls compile\n",
            solidity_guide="use low-level call result checks\n",
        )
        self.assertEqual(rc, 0, output)
        self.assertIn("boundary note not required", output)

    def test_repository_docs_are_currently_in_sync(self) -> None:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = check.main()
        output = stdout.getvalue() + stderr.getvalue()
        self.assertEqual(rc, 0, output)


if __name__ == "__main__":
    unittest.main()
