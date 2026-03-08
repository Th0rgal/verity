#!/usr/bin/env python3
"""Keep linear-memory boundary docs aligned with the interpreter feature matrix."""

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
MEMORY_EXPR_FEATURES = {"mload", "returndataOptionalBoolAt"}
MEMORY_STMT_FEATURES = {"mstore", "calldatacopy", "returndataCopy"}


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def load_feature_matrix(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def linear_memory_needs_boundary_note(matrix: dict) -> bool:
    expr_features = {
        entry["feature"]: entry
        for entry in matrix.get("expr_features", [])
        if entry.get("feature") in MEMORY_EXPR_FEATURES
    }
    stmt_features = {
        entry["feature"]: entry
        for entry in matrix.get("stmt_features", [])
        if entry.get("feature") in MEMORY_STMT_FEATURES
    }
    if expr_features.keys() != MEMORY_EXPR_FEATURES:
        raise ValueError("interpreter feature matrix is missing one or more linear-memory expression entries")
    if stmt_features.keys() != MEMORY_STMT_FEATURES:
        raise ValueError("interpreter feature matrix is missing one or more linear-memory statement entries")

    for entry in expr_features.values():
        if entry.get("proof_status") != "proved":
            return True
        if entry.get("SpecInterpreter_basic") != "supported":
            return True
        if entry.get("SpecInterpreter_fuel") != "supported":
            return True
    for entry in stmt_features.values():
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
            "First-class linear-memory forms (`Expr.mload`, `Stmt.mstore`, `Stmt.calldatacopy`, `Stmt.returndataCopy`, `Expr.returndataOptionalBoolAt`) also compile today, but they are still only partially modeled by the current proof interpreters.",
            "treat them as an explicit memory/ABI trust boundary, archive `--trust-report`, and use `--deny-linear-memory-mechanics` for proof-strict runs (see issue `#1411`).",
        ],
        "COMPILER_DOC": [
            "Memory-oriented intrinsics (`mload`, `mstore`, `calldatacopy`, `returndataCopy`, `returndataOptionalBoolAt`) compile, but the current proof interpreters still model them only partially.",
            "surface that boundary with `--trust-report` / `--deny-linear-memory-mechanics`; the remaining gap is tracked under issue `#1411`.",
        ],
        "SOLIDITY_GUIDE": [
            "Manual ABI or memory plumbing (`mload` / `mstore` / copy-based payload handling) compiles, but it is still outside the fully proved interpreter semantics today.",
            "use `--deny-linear-memory-mechanics` if the translated contract must stay inside the proved subset (see issue `#1411`).",
        ],
    }


def main() -> int:
    if not FEATURE_MATRIX.exists():
        print(f"Missing: {FEATURE_MATRIX.relative_to(ROOT)}", file=sys.stderr)
        return 1

    try:
        matrix = load_feature_matrix(FEATURE_MATRIX)
        needs_boundary_note = linear_memory_needs_boundary_note(matrix)
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
                    f"{path.relative_to(ROOT)} is out of sync with linear-memory proof boundary: missing `{snippet}`"
                )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    status = "required" if needs_boundary_note else "not required"
    print(f"linear-memory boundary sync passed: boundary note {status}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
