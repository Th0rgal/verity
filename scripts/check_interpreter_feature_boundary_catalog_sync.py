#!/usr/bin/env python3
"""Keep the interpreter proof-boundary category note aligned with the feature matrix."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FEATURE_MATRIX = ROOT / "artifacts" / "interpreter_feature_matrix.json"
TARGET_DOC = ROOT / "docs" / "INTERPRETER_FEATURE_MATRIX.md"

RUNTIME_INTROSPECTION = ("blockNumber", "contractAddress", "chainid")
PARTIAL_LINEAR_MEMORY = ("mload", "mstore", "returndataOptionalBoolAt")
NOT_MODELED_LOW_LEVEL = (
    "keccak256",
    "call",
    "staticcall",
    "delegatecall",
    "calldatacopy",
    "returndataCopy",
    "revertReturndata",
    "rawLog",
    "externalCallBind",
    "ecm",
)


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def load_feature_matrix(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def feature_status_map(matrix: dict) -> dict[str, str]:
    status_map: dict[str, str] = {}
    for section in ("expr_features", "stmt_features"):
        entries = matrix.get(section)
        if not isinstance(entries, list):
            raise ValueError(f"interpreter feature matrix is missing {section}")
        for entry in entries:
            feature = entry.get("feature")
            status = entry.get("proof_status")
            if not isinstance(feature, str):
                raise ValueError(f"{section} entry is missing string feature name")
            if not isinstance(status, str):
                raise ValueError(f"{section} entry `{feature}` is missing proof_status")
            status_map[feature] = status
    return status_map


def ensure_statuses(status_map: dict[str, str], features: tuple[str, ...], expected: str, label: str) -> None:
    missing = [feature for feature in features if feature not in status_map]
    if missing:
        raise ValueError(f"interpreter feature matrix is missing {label} entries: {', '.join(missing)}")
    mismatched = [feature for feature in features if status_map[feature] != expected]
    if mismatched:
        rendered = ", ".join(f"{feature}={status_map[feature]}" for feature in mismatched)
        raise ValueError(f"{label} drifted from expected `{expected}` status: {rendered}")


def expected_snippets(matrix: dict) -> tuple[str, str]:
    status_map = feature_status_map(matrix)
    ensure_statuses(status_map, RUNTIME_INTROSPECTION, "partial", "runtime introspection")
    ensure_statuses(status_map, PARTIAL_LINEAR_MEMORY, "partial", "single-word linear memory")
    ensure_statuses(status_map, NOT_MODELED_LOW_LEVEL, "not_modeled", "not-modeled proof-boundary")

    partial_snippet = (
        "Partially modeled features currently include runtime introspection "
        "(`blockNumber`, `contractAddress`, `chainid`) and single-word linear-memory forms "
        "(`mload`, `mstore`, `returndataOptionalBoolAt`)."
    )
    not_modeled_snippet = (
        "Fully not-modeled features currently include `keccak256`, low-level call / returndata "
        "plumbing (`call`, `staticcall`, `delegatecall`, `calldatacopy`, `returndataCopy`, "
        "`revertReturndata`), event emission (`rawLog`), and external call modules "
        "(`externalCallBind`, `ecm`)."
    )
    return partial_snippet, not_modeled_snippet


def main() -> int:
    if not FEATURE_MATRIX.exists():
        print(f"Missing: {FEATURE_MATRIX.relative_to(ROOT)}", file=sys.stderr)
        return 1
    if not TARGET_DOC.exists():
        print(f"Missing: {TARGET_DOC.relative_to(ROOT)}", file=sys.stderr)
        return 1

    try:
        matrix = load_feature_matrix(FEATURE_MATRIX)
        snippets = expected_snippets(matrix)
    except (json.JSONDecodeError, ValueError) as exc:
        print(f"{FEATURE_MATRIX.relative_to(ROOT)}: {exc}", file=sys.stderr)
        return 1

    normalized_doc = normalize_ws(TARGET_DOC.read_text(encoding="utf-8"))
    errors: list[str] = []
    for snippet in snippets:
        if normalize_ws(snippet) not in normalized_doc:
            errors.append(
                f"{TARGET_DOC.relative_to(ROOT)} is out of sync with interpreter proof-boundary categories: "
                f"missing `{snippet}`"
            )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print("interpreter feature boundary catalog sync passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
