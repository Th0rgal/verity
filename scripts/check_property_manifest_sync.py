#!/usr/bin/env python3
"""Check that property_manifest.json is in sync with actual Lean proofs."""

from __future__ import annotations

import sys

from property_utils import extract_manifest_from_proofs, load_manifest


def main() -> None:
    expected = extract_manifest_from_proofs()
    # Convert loaded manifest to list format for comparison
    actual = {k: sorted(v) for k, v in load_manifest().items()}

    problems: list[str] = []
    all_contracts = sorted(set(expected.keys()) | set(actual.keys()))
    for contract in all_contracts:
        exp = expected.get(contract, [])
        act = actual.get(contract, [])
        if not exp and act:
            problems.append(f"{contract}: manifest has entries but proofs missing")
            continue
        if exp and not act:
            problems.append(f"{contract}: missing manifest entries (run extract_property_manifest.py)")
            continue
        exp_set = set(exp)
        act_set = set(act)
        missing = sorted(exp_set - act_set)
        extra = sorted(act_set - exp_set)
        if missing:
            problems.append(f"{contract}: missing {len(missing)} theorem(s) in manifest: {', '.join(missing)}")
        if extra:
            problems.append(f"{contract}: {len(extra)} extra theorem(s) in manifest: {', '.join(extra)}")

    if problems:
        print("Property manifest is out of sync with proofs:", file=sys.stderr)
        for problem in problems:
            print(f"  - {problem}", file=sys.stderr)
        print("", file=sys.stderr)
        print("Run: python3 scripts/extract_property_manifest.py", file=sys.stderr)
        raise SystemExit(1)

    print("Property manifest sync check passed.")


if __name__ == "__main__":
    main()
