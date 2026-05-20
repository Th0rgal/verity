#!/usr/bin/env python3
"""Generate/check deterministic EVMYulLean capability report artifact.

Usage:
    python3 scripts/generate_evmyullean_capability_report.py
    python3 scripts/generate_evmyullean_capability_report.py --check
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from evmyullean_capability import (
    BUILTINS_FILE,
    EVMYULLEAN_OVERLAP_BUILTINS,
    EVMYULLEAN_UNSUPPORTED_BUILTINS,
    VERITY_HELPER_BUILTINS,
    extract_found_builtins,
)
from property_utils import ROOT

NATIVE_LOWERING_FILE = (
    ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Backends" / "EvmYulLeanNativeLowering.lean"
)
DEFAULT_OUTPUT = ROOT / "artifacts" / "evmyullean_capability_report.json"
DEFAULT_UNSUPPORTED_OUTPUT = ROOT / "artifacts" / "evmyullean_unsupported_nodes.json"


def extract_native_lowering_gaps() -> list[dict[str, str]]:
    if not NATIVE_LOWERING_FILE.exists():
        raise FileNotFoundError(
            f"Missing native lowering file: {NATIVE_LOWERING_FILE.relative_to(ROOT)}"
        )

    branch_re = re.compile(r"^\s*\|\s*\.(?P<node>[A-Za-z0-9_]+)\b")
    gap_re = re.compile(r'(?:\.error|throw)\s+(?:s!)?"(?P<reason>[^"]+)"')

    current_node: str | None = None
    gaps: list[dict[str, str]] = []
    for line in NATIVE_LOWERING_FILE.read_text(encoding="utf-8").splitlines():
        branch_match = branch_re.match(line)
        if branch_match:
            current_node = branch_match.group("node")
            continue

        gap_match = gap_re.search(line)
        if gap_match and current_node:
            gap = {"node": current_node, "reason": gap_match.group("reason")}
            if gap not in gaps:
                gaps.append(gap)
            current_node = None

    return gaps


def build_report() -> dict[str, object]:
    if not BUILTINS_FILE.exists():
        raise FileNotFoundError(f"Missing builtins file: {BUILTINS_FILE.relative_to(ROOT)}")

    found = sorted(extract_found_builtins(BUILTINS_FILE))
    found_set = set(found)
    allowed_set = EVMYULLEAN_OVERLAP_BUILTINS | VERITY_HELPER_BUILTINS

    unknown = sorted(found_set - allowed_set)
    unsupported_present = sorted(found_set & EVMYULLEAN_UNSUPPORTED_BUILTINS)
    native_lowering_gaps = extract_native_lowering_gaps()

    return {
        "schema_version": 2,
        "builtins_file": str(BUILTINS_FILE.relative_to(ROOT)),
        "status": "ok" if not unknown and not unsupported_present else "error",
        "found_builtins": found,
        "allowed_overlap_builtins": sorted(EVMYULLEAN_OVERLAP_BUILTINS),
        "allowed_verity_helpers": sorted(VERITY_HELPER_BUILTINS),
        "unsupported_builtins": sorted(EVMYULLEAN_UNSUPPORTED_BUILTINS),
        "unknown_builtins_present": unknown,
        "unsupported_builtins_present": unsupported_present,
        "native_lowering_file": str(NATIVE_LOWERING_FILE.relative_to(ROOT)),
        "native_lowering_status": "partial" if native_lowering_gaps else "complete",
        "unsupported_native_lowering_nodes": native_lowering_gaps,
    }


def write_report(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def build_unsupported_nodes_report(payload: dict[str, object]) -> dict[str, object]:
    return {
        "schema_version": 1,
        "source_report": str(DEFAULT_OUTPUT.relative_to(ROOT)),
        "native_lowering_file": payload["native_lowering_file"],
        "nodes": payload["unsupported_native_lowering_nodes"],
        "count": len(payload["unsupported_native_lowering_nodes"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output artifact path (default: artifacts/evmyullean_capability_report.json)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail if output artifact is missing or stale",
    )
    parser.add_argument(
        "--unsupported-output",
        type=Path,
        default=DEFAULT_UNSUPPORTED_OUTPUT,
        help="Unsupported-node artifact path (default: artifacts/evmyullean_unsupported_nodes.json)",
    )
    args = parser.parse_args()

    payload = build_report()
    rendered = json.dumps(payload, sort_keys=True, indent=2) + "\n"
    unsupported_payload = build_unsupported_nodes_report(payload)
    unsupported_rendered = json.dumps(unsupported_payload, sort_keys=True, indent=2) + "\n"

    if args.check:
        if not args.output.exists():
            print(f"Missing capability artifact: {args.output}", file=sys.stderr)
            return 1
        existing = args.output.read_text(encoding="utf-8")
        if existing != rendered:
            print(
                "EVMYulLean capability report is stale. Regenerate with:\n"
                "  python3 scripts/generate_evmyullean_capability_report.py",
                file=sys.stderr,
            )
            return 1
        if not args.unsupported_output.exists():
            print(f"Missing unsupported-node artifact: {args.unsupported_output}", file=sys.stderr)
            return 1
        existing_unsupported = args.unsupported_output.read_text(encoding="utf-8")
        if existing_unsupported != unsupported_rendered:
            print(
                "EVMYulLean unsupported-node report is stale. Regenerate with:\n"
                "  python3 scripts/generate_evmyullean_capability_report.py",
                file=sys.stderr,
            )
            return 1
        print(f"EVMYulLean capability report is up to date: {args.output}")
        print(f"EVMYulLean unsupported-node report is up to date: {args.unsupported_output}")
        return 0

    write_report(args.output, payload)
    write_report(args.unsupported_output, unsupported_payload)
    print(f"Wrote EVMYulLean capability report: {args.output}")
    print(f"Wrote EVMYulLean unsupported-node report: {args.unsupported_output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
