#!/usr/bin/env python3
"""Check that macro invariant tests cover every `verity_contract` declaration."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from property_utils import ROOT

DEFAULT_CONTRACTS_DIR = ROOT / "Contracts"
DEFAULT_INVARIANT_FILE = ROOT / "Contracts" / "MacroTranslateInvariantTest.lean"

CONTRACT_RE = re.compile(r"\bverity_contract\s+([A-Za-z_][A-Za-z0-9_]*)\s+where\b")
SUITE_ENTRY_RE = re.compile(
    r"\bContracts(?:\.[A-Za-z_][A-Za-z0-9_]*)*\.([A-Za-z_][A-Za-z0-9_]*)\.spec\b"
)
MACRO_SPECS_DEF_RE = re.compile(
    r"\bprivate\s+def\s+macroSpecs(?:\s*:\s*List\s+CompilationModel)?\s*:=\s*\[",
    re.MULTILINE,
)


def _collect_contracts(sources: list[Path]) -> set[str]:
    names: set[str] = set()
    for path in sources:
        text = path.read_text(encoding="utf-8")
        names.update(CONTRACT_RE.findall(text))
    return names


def _extract_macro_specs_block(text: str) -> str | None:
    match = MACRO_SPECS_DEF_RE.search(text)
    if match is None:
        return None

    # Start at the opening `[` and extract until the matching `]`.
    start = match.end() - 1
    depth = 0
    for idx in range(start, len(text)):
        ch = text[idx]
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                return text[start : idx + 1]
    return None


def _collect_suite_entries(path: Path) -> list[str] | None:
    text = path.read_text(encoding="utf-8")
    block = _extract_macro_specs_block(text)
    if block is None:
        return None
    return SUITE_ENTRY_RE.findall(block)


def _check_coverage(contract_sources: list[Path], invariant_suite: Path) -> int:
    declared = _collect_contracts(contract_sources)
    covered_entries = _collect_suite_entries(invariant_suite)

    if covered_entries is None:
        print(
            "macro invariant suite coverage check failed:",
            file=sys.stderr,
        )
        print(
            "  could not locate `private def macroSpecs : List CompilationModel := [...]`",
            file=sys.stderr,
        )
        return 1

    covered = set(covered_entries)

    if not declared:
        print("no verity_contract declarations found", file=sys.stderr)
        return 1

    seen: set[str] = set()
    duplicate_entries: list[str] = []
    for name in covered_entries:
        if name in seen and name not in duplicate_entries:
            duplicate_entries.append(name)
        seen.add(name)

    missing = sorted(declared - covered)
    extra = sorted(covered - declared)

    if not missing and not extra and not duplicate_entries:
        print("macro invariant suite coverage OK")
        return 0

    print("macro invariant suite coverage check failed:", file=sys.stderr)
    for name in duplicate_entries:
        print(
            f"  duplicate macroSpecs entry in Contracts/MacroTranslateInvariantTest.lean: {name}",
            file=sys.stderr,
        )
    for name in missing:
        print(f"  missing in Contracts/MacroTranslateInvariantTest.lean: {name}", file=sys.stderr)
    for name in extra:
        print(f"  unknown in Contracts/MacroTranslateInvariantTest.lean: {name}", file=sys.stderr)
    return 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--contracts-dir",
        default=str(DEFAULT_CONTRACTS_DIR.relative_to(ROOT)),
        help="Directory containing macro contract declarations (default: Contracts).",
    )
    parser.add_argument(
        "--invariant-suite",
        default=str(DEFAULT_INVARIANT_FILE.relative_to(ROOT)),
        help="Invariant suite file to validate (default: Contracts/MacroTranslateInvariantTest.lean).",
    )
    args = parser.parse_args(argv)

    contracts_dir = ROOT / args.contracts_dir
    invariant_suite = ROOT / args.invariant_suite

    if not contracts_dir.exists() or not contracts_dir.is_dir():
        print(f"contracts directory not found: {contracts_dir}", file=sys.stderr)
        return 1

    if not invariant_suite.exists():
        print(f"invariant suite file not found: {invariant_suite}", file=sys.stderr)
        return 1

    contract_sources = sorted(contracts_dir.rglob("*.lean"))
    if not contract_sources:
        print(f"no .lean files found under: {contracts_dir}", file=sys.stderr)
        return 1

    return _check_coverage(contract_sources, invariant_suite)


if __name__ == "__main__":
    raise SystemExit(main())
