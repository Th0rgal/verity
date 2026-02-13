#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "test" / "property_manifest.json"
EXCLUSIONS = ROOT / "test" / "property_exclusions.json"
TEST_DIR = ROOT / "test"

PROPERTY_WITH_NUM_RE = re.compile(
    r"Property\s+\d+[A-Za-z0-9]*(?:-\d+)?\s*:\s*([A-Za-z0-9_']+)(?=\s*(?:\(|$))"
)
PROPERTY_SIMPLE_RE = re.compile(r"Property\s*:\s*([A-Za-z0-9_']+)(?=\s*(?:\(|$))")
FILE_RE = re.compile(r"^Property(.+)\.t\.sol$")


def load_manifest() -> dict[str, set[str]]:
    if not MANIFEST.exists():
        raise SystemExit(f"Missing property manifest: {MANIFEST}")
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    return {contract: set(names) for contract, names in data.items()}


def load_exclusions() -> dict[str, set[str]]:
    if not EXCLUSIONS.exists():
        return {}
    data = json.loads(EXCLUSIONS.read_text(encoding="utf-8"))
    return {contract: set(names) for contract, names in data.items()}


def extract_property_names(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    names: list[str] = []
    for line in text.splitlines():
        match = PROPERTY_WITH_NUM_RE.search(line)
        if match:
            names.append(match.group(1))
            continue
        match = PROPERTY_SIMPLE_RE.search(line)
        if match:
            names.append(match.group(1))
    return names


def collect_covered() -> dict[str, set[str]]:
    covered: dict[str, set[str]] = {}
    for path in sorted(TEST_DIR.glob("Property*.t.sol")):
        match = FILE_RE.match(path.name)
        if not match:
            continue
        contract = match.group(1)
        covered.setdefault(contract, set()).update(extract_property_names(path))
    return covered


def render_report(missing: dict[str, list[str]]) -> str:
    if not missing:
        return "All proof properties are covered by tests or exclusions.\n"
    lines = ["# Property Coverage Gaps", "", "Missing property tests by contract:"]
    for contract in sorted(missing):
        lines.append("")
        lines.append(f"## {contract}")
        for name in missing[contract]:
            lines.append(f"- `{name}`")
    lines.append("")
    lines.append("Suggested tag format in tests:")
    lines.append("- `Property: <theorem_name>`")
    lines.append("- `Property 12: <theorem_name>` (optional numbering)")
    lines.append("- `Property 12-13: <theorem_name>` (optional numbering ranges)")
    lines.append("")
    lines.append("Run this script after updating proofs or tests to keep tracking up to date.")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="Report proof properties missing tests.")
    parser.add_argument("--output", type=str, help="Write report to this file")
    args = parser.parse_args()

    manifest = load_manifest()
    exclusions = load_exclusions()
    covered = collect_covered()

    missing: dict[str, list[str]] = {}
    for contract, names in manifest.items():
        covered_names = covered.get(contract, set())
        excluded_names = exclusions.get(contract, set())
        gaps = sorted(names - covered_names - excluded_names)
        if gaps:
            missing[contract] = gaps

    report = render_report(missing)
    if args.output:
        Path(args.output).write_text(report, encoding="utf-8")
    else:
        print(report, end="")


if __name__ == "__main__":
    main()
