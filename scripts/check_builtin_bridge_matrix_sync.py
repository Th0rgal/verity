#!/usr/bin/env python3
"""Keep builtin-bridge docs aligned with the interpreter feature matrix artifact."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FEATURE_MATRIX = ROOT / "artifacts" / "interpreter_feature_matrix.json"
TARGET_DOC = ROOT / "docs" / "INTERPRETER_FEATURE_MATRIX.md"
PROVED_BUILTINS = [
    "add",
    "sub",
    "mul",
    "div",
    "mod",
    "addmod",
    "mulmod",
    "exp",
    "sdiv",
    "smod",
    "lt",
    "gt",
    "slt",
    "sgt",
    "eq",
    "iszero",
    "and",
    "or",
    "xor",
    "not",
    "shl",
    "shr",
    "sar",
    "signextend",
    "byte",
]
# Builtins whose bridge theorems transitively depend on sorry'd core lemmas.
ADMITTED_BUILTINS = ["exp", "sar", "signextend"]
CONCRETE_ONLY_BUILTINS: list[str] = []
PURE_BUILTINS = PROVED_BUILTINS + CONCRETE_ONLY_BUILTINS
DELEGATED_BUILTINS = [
    "sload",
    "caller",
    "address",
    "callvalue",
    "timestamp",
    "chainid",
    "calldataload",
    "calldatasize",
    "number",
    "blobbasefee",
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
        if entry.get("verity_path") != "supported":
            raise ValueError(f"{feature} should have verity_path=supported")
        if feature in PROVED_BUILTINS:
            if entry.get("evmyullean_bridge") != "supported":
                raise ValueError(f"{feature} should have evmyullean_bridge=supported")
            if entry.get("agreement_proved") is not True:
                raise ValueError(f"{feature} should have agreement_proved=true")
            # Admitted builtins must be flagged; fully proved must not be.
            if feature in ADMITTED_BUILTINS:
                if entry.get("sorry_dependent") is not True:
                    raise ValueError(f"{feature} should have sorry_dependent=true")
            else:
                if entry.get("sorry_dependent", False) is not False:
                    raise ValueError(f"{feature} should not have sorry_dependent=true")
        elif feature in CONCRETE_ONLY_BUILTINS:
            if entry.get("evmyullean_bridge") != "supported":
                raise ValueError(f"{feature} should have evmyullean_bridge=supported")
            if entry.get("agreement_proved") is not False:
                raise ValueError(f"{feature} should have agreement_proved=false (concrete-only)")
            if entry.get("sorry_dependent", False) is not False:
                raise ValueError(f"{feature} is concrete-only and must not have sorry_dependent=true")
        elif feature in DELEGATED_BUILTINS:
            if entry.get("evmyullean_bridge") != "delegated":
                raise ValueError(f"{feature} should have evmyullean_bridge=delegated")
            if entry.get("agreement_proved") is not False:
                raise ValueError(f"{feature} should have agreement_proved=false")
            if entry.get("sorry_dependent", False) is not False:
                raise ValueError(f"{feature} is delegated and must not have sorry_dependent=true")

    return builtin_features


def _sorry_qualifier(builtin_features: list[dict]) -> str:
    """Return parenthetical qualifier for sorry-dependent bridge proofs."""
    admitted = sum(1 for e in builtin_features if e.get("sorry_dependent") is True)
    if admitted == 0:
        return ""
    proved_total = sum(1 for e in builtin_features if e["agreement_proved"])
    fully = proved_total - admitted
    return f" ({fully} fully proven, {admitted} with sorry-dependent core equivalences)"


def expected_doc_snippets(builtin_features: list[dict]) -> list[str]:
    total = len(builtin_features)
    proved = sum(1 for entry in builtin_features if entry["agreement_proved"])
    delegated = len(DELEGATED_BUILTINS)
    qualifier = _sorry_qualifier(builtin_features)
    snippets = [
        f"{proved}/{total} builtins have universal bridge agreement proofs between Verity and EVMYulLean evaluation paths{qualifier}.",
        f"{proved} are discharged by universal symbolic lemmas in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean`",
    ]
    if CONCRETE_ONLY_BUILTINS:
        concrete_only = len(CONCRETE_ONLY_BUILTINS)
        concrete_names = ", ".join(f"`{b}`" for b in CONCRETE_ONLY_BUILTINS)
        snippets.append(f"{concrete_only} additional builtins ({concrete_names}) are evaluated via EVMYulLean and validated by concrete")
    else:
        snippets.append("and none still require concrete-only regression coverage")
    snippets.extend([
        f"The remaining {delegated} are state-dependent or Verity-specific helpers that remain on the Verity evaluation path.",
        "| `address` | ok | del | -- |",
        "| `timestamp` | ok | del | -- |",
    ])
    return snippets


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
    admitted = sum(1 for entry in builtin_features if entry.get("sorry_dependent") is True)
    admitted_str = f"; admitted (sorry-dependent): {', '.join(ADMITTED_BUILTINS)}" if admitted else ""
    print(
        "builtin bridge matrix sync passed: "
        f"{proved}/{len(builtin_features)} builtins proved{admitted_str}; "
        f"concrete-only: {', '.join(CONCRETE_ONLY_BUILTINS)}; "
        f"delegated: {', '.join(DELEGATED_BUILTINS)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
