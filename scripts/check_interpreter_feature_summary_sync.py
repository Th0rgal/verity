#!/usr/bin/env python3
"""Keep interpreter feature summary docs aligned with the machine-readable matrix."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FEATURE_MATRIX = ROOT / "artifacts" / "interpreter_feature_matrix.json"
TARGET_DOC = ROOT / "docs" / "INTERPRETER_FEATURE_MATRIX.md"
DISPLAY_NAME_OVERRIDES = {
    "externalCall_expr": "externalCall",
}
PROOF_STATUS_ORDER = ("proved", "assumed", "partial", "not_modeled")


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def load_feature_matrix(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def display_name(feature: str) -> str:
    return DISPLAY_NAME_OVERRIDES.get(feature, feature)


def summarize(entries: list[dict]) -> list[str]:
    by_status = {status: [] for status in PROOF_STATUS_ORDER}
    for entry in entries:
        status = entry.get("proof_status")
        feature = entry.get("feature")
        if status not in by_status:
            raise ValueError(f"unexpected proof status `{status}` for `{feature}`")
        if not isinstance(feature, str):
            raise ValueError("feature matrix entry is missing string feature name")
        by_status[status].append(display_name(feature))

    summary: list[str] = []
    for status in PROOF_STATUS_ORDER:
        names = by_status[status]
        count = len(names)
        if count == 0:
            summary.append("0")
            continue
        if status == "not_modeled" or count <= 5:
            rendered_names = ", ".join(f"`{name}`" for name in names)
            summary.append(f"{count} ({rendered_names})")
        else:
            summary.append(str(count))
    return summary


def expected_summary_rows(matrix: dict) -> list[str]:
    expr_features = matrix.get("expr_features")
    stmt_features = matrix.get("stmt_features")
    builtin_features = matrix.get("builtin_features")
    if not isinstance(expr_features, list):
        raise ValueError("interpreter feature matrix is missing expr_features")
    if not isinstance(stmt_features, list):
        raise ValueError("interpreter feature matrix is missing stmt_features")
    if not isinstance(builtin_features, list):
        raise ValueError("interpreter feature matrix is missing builtin_features")

    builtins_proved = sum(1 for entry in builtin_features if entry.get("agreement_proved") is True)
    builtins_remaining = sum(1 for entry in builtin_features if entry.get("agreement_proved") is False)
    if builtins_proved + builtins_remaining != len(builtin_features):
        raise ValueError("builtin_features contains non-boolean agreement_proved values")

    expr_cells = summarize(expr_features)
    stmt_cells = summarize(stmt_features)
    builtin_row = f"| Builtins (agreement) | {builtins_proved} | 0 | 0 | {builtins_remaining} (delegated) |"
    return [
        f"| Expression features | {' | '.join(expr_cells)} |",
        f"| Statement features | {' | '.join(stmt_cells)} |",
        builtin_row,
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
        expected_rows = expected_summary_rows(matrix)
    except (json.JSONDecodeError, ValueError) as exc:
        print(f"{FEATURE_MATRIX.relative_to(ROOT)}: {exc}", file=sys.stderr)
        return 1

    normalized_doc = normalize_ws(TARGET_DOC.read_text(encoding="utf-8"))
    errors: list[str] = []
    for row in expected_rows:
        if normalize_ws(row) not in normalized_doc:
            errors.append(
                f"{TARGET_DOC.relative_to(ROOT)} is out of sync with interpreter feature summary: missing `{row}`"
            )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print("interpreter feature summary sync passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
