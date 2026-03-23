#!/usr/bin/env python3
"""Synchronise sorry-count references with the verification artifact.

Patches:
  - docs/VERIFICATION_STATUS.md  (sorry count in prose)
  - scripts/check_lean_hygiene.py (expected_sorry baseline)

Run after generate_verification_status.py to keep everything in sync.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT
from verification_metrics import load_metrics_from_artifact

ARTIFACT = ROOT / "artifacts" / "verification_status.json"
STATUS_DOC = ROOT / "docs" / "VERIFICATION_STATUS.md"
HYGIENE_SCRIPT = ROOT / "scripts" / "check_lean_hygiene.py"

SORRY_DOC_RE = re.compile(
    r"^(\d+)( `sorry` remaining across `Compiler/\*\*/\*\.lean` and `Verity/\*\*/\*\.lean` proof modules\.)$",
    re.MULTILINE,
)

SORRY_HYGIENE_RE = re.compile(r"^(\s+expected_sorry = )\d+$", re.MULTILINE)


def _patch_file(path: Path, pattern: re.Pattern[str], replacement: str, label: str) -> bool:
    text = path.read_text(encoding="utf-8")
    new_text, n = pattern.subn(replacement, text)
    if n == 0:
        print(f"warning: {label} pattern not found in {path}, skipping", file=sys.stderr)
        return False
    if new_text != text:
        path.write_text(new_text, encoding="utf-8")
        print(f"Updated {label} in {path}")
        return True
    print(f"{label} already up to date in {path}")
    return False


def main() -> None:
    metrics = load_metrics_from_artifact(ARTIFACT)
    sorry_count = metrics["proofs"]["sorry"]

    _patch_file(STATUS_DOC, SORRY_DOC_RE, rf"{sorry_count}\2", f"sorry count ({sorry_count})")
    _patch_file(HYGIENE_SCRIPT, SORRY_HYGIENE_RE, rf"\g<1>{sorry_count}", f"expected_sorry ({sorry_count})")


if __name__ == "__main__":
    main()
