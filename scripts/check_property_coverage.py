#!/usr/bin/env python3
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "test" / "property_manifest.json"
EXCLUSIONS = ROOT / "test" / "property_exclusions.json"
TEST_DIR = ROOT / "test"

PROPERTY_WITH_NUM_RE = re.compile(
    r"Property\s+\d+[A-Za-z]*\s*:\s*([A-Za-z0-9_']+)(?:\s*\(.*\))?\s*$"
)
PROPERTY_SIMPLE_RE = re.compile(
    r"Property\s*:\s*([A-Za-z0-9_']+)(?:\s*\(.*\))?\s*$"
)
FILE_RE = re.compile(r"^Property(.+)\.t\.sol$")


def load_manifest() -> dict[str, set[str]]:
    if not MANIFEST.exists():
        raise SystemExit(f"Missing property manifest: {MANIFEST}")
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    manifest: dict[str, set[str]] = {}
    for contract, names in data.items():
        manifest[contract] = set(names)
    return manifest


def load_exclusions() -> dict[str, set[str]]:
    if not EXCLUSIONS.exists():
        return {}
    data = json.loads(EXCLUSIONS.read_text(encoding="utf-8"))
    exclusions: dict[str, set[str]] = {}
    for contract, names in data.items():
        exclusions[contract] = set(names)
    return exclusions


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


def main() -> None:
    manifest = load_manifest()
    exclusions = load_exclusions()
    covered = collect_covered()

    errors: list[str] = []
    warnings: list[str] = []

    for contract, names in exclusions.items():
        if contract not in manifest:
            errors.append(f"Exclusion contract not in manifest: {contract}")
            continue
        unknown = names - manifest[contract]
        if unknown:
            errors.append(
                f"Exclusions for {contract} include unknown theorem(s): {', '.join(sorted(unknown))}"
            )

    for contract, names in manifest.items():
        covered_names = covered.get(contract, set())
        excluded_names = exclusions.get(contract, set())
        stale = covered_names & excluded_names
        if stale:
            errors.append(
                f"{contract}: exclusions list covered theorem(s): {', '.join(sorted(stale))}"
            )
        missing = names - covered_names - excluded_names
        if missing:
            errors.append(
                f"{contract}: missing property tests for {len(missing)} theorem(s): {', '.join(sorted(missing))}"
            )

    if errors:
        print("Property coverage check failed:", file=sys.stderr)
        for item in errors:
            print(f"  - {item}", file=sys.stderr)
        raise SystemExit(1)

    if warnings:
        for item in warnings:
            print(f"Warning: {item}")

    print("Property coverage check passed.")


if __name__ == "__main__":
    main()
