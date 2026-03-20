#!/usr/bin/env python3
"""Regenerate the committed verify workflow sync spec artifact."""

from __future__ import annotations

import argparse
import difflib
import json
import sys
from pathlib import Path

from verify_sync_spec_source import build_spec

ROOT = Path(__file__).resolve().parents[1]
SPEC_PATH = ROOT / "scripts" / "verify_sync_spec.json"


def _render_spec() -> str:
    return json.dumps(build_spec(), indent=2) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail if the committed JSON artifact is stale.",
    )
    args = parser.parse_args()

    rendered = _render_spec()
    current = SPEC_PATH.read_text(encoding="utf-8") if SPEC_PATH.exists() else ""

    if args.check:
        if current == rendered:
            print("verify_sync_spec.json is up to date")
            return 0
        diff = difflib.unified_diff(
            current.splitlines(),
            rendered.splitlines(),
            fromfile=str(SPEC_PATH),
            tofile="generated verify_sync_spec.json",
            lineterm="",
        )
        for line in diff:
            print(line, file=sys.stderr)
        print(
            "verify_sync_spec.json is stale; run python3 scripts/generate_verify_sync_spec.py",
            file=sys.stderr,
        )
        return 1

    SPEC_PATH.write_text(rendered, encoding="utf-8")
    print(f"wrote {SPEC_PATH}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
