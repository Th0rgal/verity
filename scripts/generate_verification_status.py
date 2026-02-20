#!/usr/bin/env python3
"""Generate artifacts/verification_status.json from repository metrics."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_doc_counts import collect_metrics
from property_utils import ROOT


def _normalize(data: dict) -> str:
    """Return deterministic JSON encoding."""
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate verification status artifact consumed by docs checks."
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "artifacts" / "verification_status.json",
        help="Output artifact path.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail if output file is missing or stale; do not write changes.",
    )
    args = parser.parse_args()

    metrics = collect_metrics()
    rendered = _normalize(metrics)
    output = args.output

    if args.check:
        if not output.exists():
            raise SystemExit(f"Missing verification artifact: {output}")
        existing = output.read_text(encoding="utf-8")
        if existing != rendered:
            raise SystemExit(
                f"Stale verification artifact: {output}\n"
                "Run `python3 scripts/generate_verification_status.py`."
            )
        print(f"Verification artifact is up to date: {output}")
        return

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(f"Wrote verification artifact: {output}")


if __name__ == "__main__":
    main()
