#!/usr/bin/env python3
"""Validate parity-pack identity metrics from a generated diff report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict


ONLY_IN_VERITY_KINDS = {
    "file_missing_in_solc",
    "scope_missing_in_solc",
    "missing_in_solc",
}
ONLY_IN_SOLIDITY_KINDS = {
    "file_missing_in_verity",
    "scope_missing_in_verity",
    "missing_in_verity",
}
HASH_MISMATCH_KINDS = {"line_mismatch"}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", required=True, help="Path to yul identity diff report JSON")
    parser.add_argument("--max-only-in-verity", type=int, default=0)
    parser.add_argument("--max-only-in-solidity", type=int, default=0)
    parser.add_argument("--max-hash-mismatch", type=int, default=0)
    parser.add_argument("--format", choices=["text", "markdown"], default="text")
    return parser.parse_args()


def load_report(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise SystemExit(f"Report not found: {path}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"Invalid JSON in report {path}: {exc}") from exc


def metric_counts(report: dict) -> Dict[str, int]:
    by_kind = report.get("summary", {}).get("byKind", {})
    if not isinstance(by_kind, dict):
        raise SystemExit("Invalid report: summary.byKind must be an object")

    def sum_kinds(kinds: set[str]) -> int:
        return sum(int(by_kind.get(kind, 0)) for kind in kinds)

    return {
        "onlyInVerity": sum_kinds(ONLY_IN_VERITY_KINDS),
        "onlyInSolidity": sum_kinds(ONLY_IN_SOLIDITY_KINDS),
        "hashMismatch": sum_kinds(HASH_MISMATCH_KINDS),
    }


def print_metrics(metrics: Dict[str, int], fmt: str) -> None:
    if fmt == "markdown":
        print("### Parity Pack Metrics")
        print("| Metric | Count |")
        print("| :-- | --: |")
        print(f"| `onlyInVerity` | {metrics['onlyInVerity']} |")
        print(f"| `onlyInSolidity` | {metrics['onlyInSolidity']} |")
        print(f"| `hashMismatch` | {metrics['hashMismatch']} |")
    else:
        print(
            "Parity pack metrics: "
            f"onlyInVerity={metrics['onlyInVerity']} "
            f"onlyInSolidity={metrics['onlyInSolidity']} "
            f"hashMismatch={metrics['hashMismatch']}"
        )


def main() -> int:
    args = parse_args()
    report = load_report(Path(args.report))
    metrics = metric_counts(report)
    print_metrics(metrics, args.format)

    violations = []
    if metrics["onlyInVerity"] > args.max_only_in_verity:
        violations.append(
            f"onlyInVerity={metrics['onlyInVerity']} exceeds max {args.max_only_in_verity}"
        )
    if metrics["onlyInSolidity"] > args.max_only_in_solidity:
        violations.append(
            f"onlyInSolidity={metrics['onlyInSolidity']} exceeds max {args.max_only_in_solidity}"
        )
    if metrics["hashMismatch"] > args.max_hash_mismatch:
        violations.append(
            f"hashMismatch={metrics['hashMismatch']} exceeds max {args.max_hash_mismatch}"
        )

    if violations:
        for line in violations:
            print(f"ERROR: {line}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
