#!/usr/bin/env python3
"""Extract theorem names from Lean proof files to generate property manifest."""

import json

from property_utils import ROOT, extract_manifest_from_proofs
OUTPUT = ROOT / "test" / "property_manifest.json"


def main() -> None:
    manifest = extract_manifest_from_proofs()
    OUTPUT.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
