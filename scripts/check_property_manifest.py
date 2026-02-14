#!/usr/bin/env python3
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "test" / "property_manifest.json"
TEST_DIR = ROOT / "test"

PROPERTY_WITH_NUM_RE = re.compile(
    r"^\s*(?:/\*\*|/\*|\*|//)?\s*Property\s+\d+[A-Za-z0-9]*(?:-\d+)?\s*:\s*([A-Za-z0-9_']+)\s*(?:\([^)]*\))?\s*$"
)
PROPERTY_SIMPLE_RE = re.compile(
    r"^\s*(?:/\*\*|/\*|\*|//)?\s*Property\s*:\s*([A-Za-z0-9_']+)\s*(?:\([^)]*\))?\s*$"
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


def main() -> None:
    manifest = load_manifest()
    missing: list[str] = []
    empty_tags: list[str] = []

    for path in sorted(TEST_DIR.glob("Property*.t.sol")):
        match = FILE_RE.match(path.name)
        if not match:
            continue
        contract = match.group(1)
        if contract not in manifest:
            missing.append(f"{path}: no manifest entry for {contract}")
            continue
        names = extract_property_names(path)
        if not names:
            empty_tags.append(str(path))
            continue
        for name in names:
            if name not in manifest[contract]:
                missing.append(f"{path}: property '{name}' not found in manifest for {contract}")

    if empty_tags:
        missing.append("Property files missing Property tags: " + ", ".join(empty_tags))

    if missing:
        print("Property manifest check failed:", file=sys.stderr)
        for item in missing:
            print(f"  - {item}", file=sys.stderr)
        raise SystemExit(1)

    print("Property manifest check passed.")


if __name__ == "__main__":
    main()
