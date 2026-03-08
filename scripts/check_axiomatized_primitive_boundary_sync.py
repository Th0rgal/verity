#!/usr/bin/env python3
"""Keep axiomatized-primitive boundary docs aligned with the interpreter feature matrix."""

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
AXIOMATIZED_EXPR_FEATURES = {"keccak256"}


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def load_feature_matrix(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def axiomatized_primitives_need_boundary_note(matrix: dict) -> bool:
    expr_features = {
        entry["feature"]: entry
        for entry in matrix.get("expr_features", [])
        if entry.get("feature") in AXIOMATIZED_EXPR_FEATURES
    }
    if expr_features.keys() != AXIOMATIZED_EXPR_FEATURES:
        raise ValueError("interpreter feature matrix is missing one or more axiomatized primitive entries")

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
            "`Expr.keccak256` also remains an explicit proof boundary today: the compiler supports it directly, but the current proof stack still treats it as an axiomatized primitive instead of a fully modeled operation.",
            "archive `--trust-report` and use `--deny-axiomatized-primitives` for proof-strict runs (see issue `#1411`).",
        ],
        "COMPILER_DOC": [
            "The `keccak256` intrinsic also compiles, but it remains axiomatized in the current proof stack rather than fully modeled end to end.",
            "archive `--trust-report` and add `--deny-axiomatized-primitives` if the selected contracts must stay inside the proved subset (see issue `#1411`).",
        ],
        "SOLIDITY_GUIDE": [
            "Raw `keccak256` hashing also compiles through the typed intrinsic surface, but it still relies on an explicit axiom in the current proof stack.",
            "archive `--trust-report`, and use `--deny-axiomatized-primitives` when the translated contract must stay inside the proved subset (see issue `#1411`).",
        ],
    }


def main() -> int:
    if not FEATURE_MATRIX.exists():
        print(f"Missing: {FEATURE_MATRIX.relative_to(ROOT)}", file=sys.stderr)
        return 1

    try:
        matrix = load_feature_matrix(FEATURE_MATRIX)
        needs_boundary_note = axiomatized_primitives_need_boundary_note(matrix)
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
                    f"{path.relative_to(ROOT)} is out of sync with axiomatized-primitive proof boundary: missing `{snippet}`"
                )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    status = "required" if needs_boundary_note else "not required"
    print(f"axiomatized-primitive boundary sync passed: boundary note {status}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
