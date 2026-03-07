#!/usr/bin/env python3
"""Keep low-level call docs aligned with the interpreter feature matrix."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FEATURE_MATRIX = ROOT / "artifacts" / "interpreter_feature_matrix.json"
TARGET_FILES = {
    "EDSL_API": ROOT / "docs-site" / "content" / "edsl-api-reference.mdx",
    "COMPILER_DOC": ROOT / "docs-site" / "content" / "compiler.mdx",
    "SOLIDITY_GUIDE": ROOT / "docs-site" / "content" / "guides" / "solidity-to-verity.mdx",
}


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def load_feature_matrix(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def low_level_calls_need_boundary_note(matrix: dict) -> bool:
    expr_features = {
        entry["feature"]: entry
        for entry in matrix.get("expr_features", [])
        if entry.get("feature") in {"call", "staticcall", "delegatecall"}
    }
    if len(expr_features) != 3:
        raise ValueError("interpreter feature matrix is missing one or more low-level call entries")

    for entry in expr_features.values():
        if entry.get("proof_status") != "proved":
            return True
        if entry.get("SpecInterpreter_basic") != "supported":
            return True
        if entry.get("SpecInterpreter_fuel") != "supported":
            return True
    return False


def expected_snippets(needs_boundary_note: bool) -> dict[str, list[str]]:
    if not needs_boundary_note:
        return {label: [] for label in TARGET_FILES}

    return {
        "EDSL_API": [
            "They are not yet modeled by the current proof interpreters.",
            "low-level call plumbing and returndata behavior remain a compiler-and-testing trust boundary rather than a proved semantic feature today.",
        ],
        "COMPILER_DOC": [
            "their runtime semantics are still outside the current proof-interpreter model.",
            "call success / returndata mechanics remain validated by differential testing and tracked under issue `#1332`.",
        ],
        "SOLIDITY_GUIDE": [
            "Those low-level call mechanics compile, but they are still outside the current proof-interpreter semantics;",
            "see issue `#1332`",
        ],
    }


def main() -> int:
    if not FEATURE_MATRIX.exists():
        print(f"Missing: {FEATURE_MATRIX.relative_to(ROOT)}", file=sys.stderr)
        return 1

    try:
        matrix = load_feature_matrix(FEATURE_MATRIX)
        needs_boundary_note = low_level_calls_need_boundary_note(matrix)
    except (json.JSONDecodeError, ValueError) as exc:
        print(f"{FEATURE_MATRIX.relative_to(ROOT)}: {exc}", file=sys.stderr)
        return 1

    errors: list[str] = []
    expected = expected_snippets(needs_boundary_note)
    for label, path in TARGET_FILES.items():
        if not path.exists():
            errors.append(f"Missing: {path.relative_to(ROOT)}")
            continue
        normalized = normalize_ws(path.read_text(encoding="utf-8"))
        for snippet in expected[label]:
            if normalize_ws(snippet) not in normalized:
                errors.append(
                    f"{path.relative_to(ROOT)} is out of sync with low-level call proof boundary: missing `{snippet}`"
                )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    status = "required" if needs_boundary_note else "not required"
    print(f"low-level call boundary sync passed: boundary note {status}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
