#!/usr/bin/env python3
"""Keep builtin-bridge docs aligned with the interpreter feature matrix artifact."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FEATURE_MATRIX = ROOT / "artifacts" / "interpreter_feature_matrix.json"
TARGET_DOC = ROOT / "docs" / "INTERPRETER_FEATURE_MATRIX.md"
PURE_BUILTINS = [
    "add",
    "sub",
    "mul",
    "div",
    "mod",
    "lt",
    "gt",
    "eq",
    "iszero",
    "and",
    "or",
    "xor",
    "not",
    "shl",
    "shr",
]
DELEGATED_BUILTINS = [
    "sload",
    "caller",
    "address",
    "timestamp",
    "chainid",
    "calldataload",
    "mappingSlot",
]
EXPECTED_BUILTINS = PURE_BUILTINS + DELEGATED_BUILTINS


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def load_feature_matrix(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def validate_builtin_features(matrix: dict) -> list[dict]:
    builtin_features = matrix.get("builtin_features")
    if not isinstance(builtin_features, list):
        raise ValueError("interpreter feature matrix is missing builtin_features")

    found_names = [entry.get("feature") for entry in builtin_features]
    if found_names != EXPECTED_BUILTINS:
        raise ValueError(
            "builtin feature list is out of sync: "
            f"expected {EXPECTED_BUILTINS}, found {found_names}"
        )

    for entry in builtin_features:
        feature = entry["feature"]
        if feature in PURE_BUILTINS:
            if entry.get("verity_path") != "supported":
                raise ValueError(f"{feature} should have verity_path=supported")
            if entry.get("evmyullean_bridge") != "supported":
                raise ValueError(f"{feature} should have evmyullean_bridge=supported")
            if entry.get("agreement_proved") is not True:
                raise ValueError(f"{feature} should have agreement_proved=true")
        else:
            if entry.get("verity_path") != "supported":
                raise ValueError(f"{feature} should have verity_path=supported")
            if entry.get("evmyullean_bridge") != "delegated":
                raise ValueError(f"{feature} should have evmyullean_bridge=delegated")
            if entry.get("agreement_proved") is not False:
                raise ValueError(f"{feature} should have agreement_proved=false")

    return builtin_features


def expected_doc_snippets(builtin_features: list[dict]) -> list[str]:
    total = len(builtin_features)
    proved = sum(1 for entry in builtin_features if entry["agreement_proved"])
    remaining = total - proved
    return [
        f"{proved}/{total} builtins have bridge agreement coverage between Verity and EVMYulLean evaluation paths.",
        f"{proved} are discharged by universal symbolic lemmas in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean`, and none still require concrete-only regression coverage.",
        f"The remaining {remaining} are state-dependent or Verity-specific helpers that remain on the Verity evaluation path.",
        "| `address` | ok | del | -- |",
        "| `timestamp` | ok | del | -- |",
    ]


def main() -> int:
    if not FEATURE_MATRIX.exists():
        print(f"Missing: {FEATURE_MATRIX.relative_to(ROOT)}", file=sys.stderr)
        return 1
    if not TARGET_DOC.exists():
        print(f"Missing: {TARGET_DOC.relative_to(ROOT)}", file=sys.stderr)
        return 1

    try:
        matrix = load_feature_matrix(FEATURE_MATRIX)
        builtin_features = validate_builtin_features(matrix)
    except (json.JSONDecodeError, ValueError) as exc:
        print(f"{FEATURE_MATRIX.relative_to(ROOT)}: {exc}", file=sys.stderr)
        return 1

    normalized = normalize_ws(TARGET_DOC.read_text(encoding="utf-8"))
    errors: list[str] = []
    for snippet in expected_doc_snippets(builtin_features):
        if normalize_ws(snippet) not in normalized:
            errors.append(
                f"{TARGET_DOC.relative_to(ROOT)} is out of sync with builtin bridge coverage: missing `{snippet}`"
            )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    proved = sum(1 for entry in builtin_features if entry["agreement_proved"])
    print(
        "builtin bridge matrix sync passed: "
        f"{proved}/{len(builtin_features)} builtins covered; delegated remainder: "
        f"{', '.join(DELEGATED_BUILTINS)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
