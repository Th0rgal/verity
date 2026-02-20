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

from property_utils import ROOT

BUILTINS_FILE = ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Builtins.lean"
ADAPTER_FILE = ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Backends" / "EvmYulLeanAdapter.lean"
DEFAULT_OUTPUT = ROOT / "artifacts" / "evmyullean_capability_report.json"

BUILTIN_NAME_RE = re.compile(r'func\s*=\s*"([^"]+)"')

EVMYULLEAN_OVERLAP_BUILTINS = {
    "add",
    "and",
    "calldataload",
    "caller",
    "div",
    "eq",
    "gt",
    "iszero",
    "lt",
    "mod",
    "mul",
    "not",
    "or",
    "shl",
    "shr",
    "sload",
    "sub",
    "xor",
}

VERITY_HELPER_BUILTINS = {"mappingSlot"}

EVMYULLEAN_UNSUPPORTED_BUILTINS = {
    "create",
    "create2",
    "extcodecopy",
    "extcodehash",
    "extcodesize",
}


def extract_adapter_gaps() -> list[dict[str, str]]:
    if not ADAPTER_FILE.exists():
        raise FileNotFoundError(f"Missing adapter file: {ADAPTER_FILE.relative_to(ROOT)}")

    branch_re = re.compile(r"^\s*\|\s*\.(?P<node>[A-Za-z0-9_]+)\b")
    gap_re = re.compile(r'\.error\s+"adapter gap: (?P<reason>[^"]+)"')

    current_node: str | None = None
    gaps: list[dict[str, str]] = []
    for line in ADAPTER_FILE.read_text(encoding="utf-8").splitlines():
        branch_match = branch_re.match(line)
        if branch_match:
            current_node = branch_match.group("node")
            continue

        gap_match = gap_re.search(line)
        if gap_match and current_node:
            gaps.append({"node": current_node, "reason": gap_match.group("reason")})
            current_node = None

    return gaps


def build_report() -> dict[str, object]:
    if not BUILTINS_FILE.exists():
        raise FileNotFoundError(f"Missing builtins file: {BUILTINS_FILE.relative_to(ROOT)}")

    text = BUILTINS_FILE.read_text(encoding="utf-8")
    found = sorted(set(BUILTIN_NAME_RE.findall(text)))
    found_set = set(found)
    allowed_set = EVMYULLEAN_OVERLAP_BUILTINS | VERITY_HELPER_BUILTINS

    unknown = sorted(found_set - allowed_set)
    unsupported_present = sorted(found_set & EVMYULLEAN_UNSUPPORTED_BUILTINS)
    adapter_gaps = extract_adapter_gaps()

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
        "adapter_file": str(ADAPTER_FILE.relative_to(ROOT)),
        "adapter_lowering_status": "partial" if adapter_gaps else "complete",
        "unsupported_adapter_nodes": adapter_gaps,
    }


def write_report(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8")


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
    args = parser.parse_args()

    payload = build_report()
    rendered = json.dumps(payload, sort_keys=True, indent=2) + "\n"

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
        print(f"EVMYulLean capability report is up to date: {args.output}")
        return 0

    write_report(args.output, payload)
    print(f"Wrote EVMYulLean capability report: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
