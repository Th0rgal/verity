#!/usr/bin/env python3
"""Check that property test files reference valid theorems from the manifest."""

from __future__ import annotations

import sys

from property_utils import (
    FILE_RE,
    TEST_DIR,
    extract_property_names,
    load_manifest,
    report_errors,
)


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

    report_errors(missing, "Property manifest check failed")

    print("Property manifest check passed.")


if __name__ == "__main__":
    main()
