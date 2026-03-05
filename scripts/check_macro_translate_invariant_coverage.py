#!/usr/bin/env python3
"""Check that macro invariant tests cover every `verity_contract` declaration."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from property_utils import ROOT

DEFAULT_CONTRACTS_DIR = ROOT / "Contracts" / "MacroContracts"
DEFAULT_INVARIANT_FILE = ROOT / "Compiler" / "MacroTranslateInvariantTest.lean"

CONTRACT_RE = re.compile(r"\bverity_contract\s+([A-Za-z_][A-Za-z0-9_]*)\s+where\b")
SUITE_ENTRY_RE = re.compile(r"\bContracts\.MacroContracts\.([A-Za-z_][A-Za-z0-9_]*)\.spec\b")


def _collect_contracts(sources: list[Path]) -> set[str]:
    names: set[str] = set()
    for path in sources:
        text = path.read_text(encoding="utf-8")
        names.update(CONTRACT_RE.findall(text))
    return names


def _collect_suite_entries(path: Path) -> set[str]:
    text = path.read_text(encoding="utf-8")
    return set(SUITE_ENTRY_RE.findall(text))


def _check_coverage(contract_sources: list[Path], invariant_suite: Path) -> int:
    declared = _collect_contracts(contract_sources)
    covered = _collect_suite_entries(invariant_suite)

    if not declared:
        print("no verity_contract declarations found", file=sys.stderr)
        return 1

    missing = sorted(declared - covered)
    extra = sorted(covered - declared)

    if not missing and not extra:
        print("macro invariant suite coverage OK")
        return 0

    print("macro invariant suite coverage check failed:", file=sys.stderr)
    for name in missing:
        print(f"  missing in Compiler/MacroTranslateInvariantTest.lean: {name}", file=sys.stderr)
    for name in extra:
        print(f"  unknown in Compiler/MacroTranslateInvariantTest.lean: {name}", file=sys.stderr)
    return 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--contracts-dir",
        default=str(DEFAULT_CONTRACTS_DIR.relative_to(ROOT)),
        help="Directory containing macro contract declarations (default: Contracts/MacroContracts).",
    )
    parser.add_argument(
        "--invariant-suite",
        default=str(DEFAULT_INVARIANT_FILE.relative_to(ROOT)),
        help="Invariant suite file to validate (default: Compiler/MacroTranslateInvariantTest.lean).",
    )
    args = parser.parse_args()

    contracts_dir = ROOT / args.contracts_dir
    invariant_suite = ROOT / args.invariant_suite

    if not contracts_dir.exists() or not contracts_dir.is_dir():
        print(f"contracts directory not found: {contracts_dir}", file=sys.stderr)
        return 1

    if not invariant_suite.exists():
        print(f"invariant suite file not found: {invariant_suite}", file=sys.stderr)
        return 1

    contract_sources = sorted(contracts_dir.glob("*.lean"))
    if not contract_sources:
        print(f"no .lean files found under: {contracts_dir}", file=sys.stderr)
        return 1

    return _check_coverage(contract_sources, invariant_suite)


if __name__ == "__main__":
    raise SystemExit(main())
