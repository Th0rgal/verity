#!/usr/bin/env python3
"""Check that macro round-trip fuzz suite covers every `verity_contract` declaration."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from property_utils import ROOT

DEFAULT_CONTRACTS_DIR = ROOT / "Contracts"
DEFAULT_FUZZ_FILE = ROOT / "Contracts" / "MacroTranslateRoundTripFuzz.lean"
EXCLUDED_CONTRACTS = {
    "StringSmoke",  # ABI-level string support is not yet covered by the numeric-only round-trip fuzz harness
    "StringErrorSmoke",  # String custom-error payloads are covered by dedicated ABI/runtime tests, not the numeric-only fuzz harness
}

CONTRACT_RE = re.compile(r"\bverity_contract\s+([A-Za-z_][A-Za-z0-9_]*)\s+where\b")
SUITE_ENTRY_RE = re.compile(
    r"\bContracts(?:\.[A-Za-z_][A-Za-z0-9_]*)*\.([A-Za-z_][A-Za-z0-9_]*)\.spec\b"
)
MACRO_SPECS_DEF_RE = re.compile(
    r"\bprivate\s+def\s+macroSpecs(?:\s*:\s*List\s+CompilationModel)?\s*:=\s*\[",
    re.MULTILINE,
)


def _collect_contracts_from_text(text: str) -> list[str]:
    names: list[str] = []
    guard_pending = False
    block_comment_depth = 0
    for line in text.splitlines():
        stripped = line.strip()
        if block_comment_depth > 0:
            block_comment_depth += stripped.count("/-")
            block_comment_depth -= stripped.count("-/")
            continue
        if stripped.startswith("/-"):
            block_comment_depth += stripped.count("/-")
            block_comment_depth -= stripped.count("-/")
            if block_comment_depth > 0 or stripped == "":
                continue
            if stripped.endswith("-/"):
                continue
        if stripped == "#guard_msgs in":
            guard_pending = True
            continue
        match = CONTRACT_RE.search(line)
        if guard_pending:
            if not stripped or stripped.startswith("--"):
                continue
            if match is not None:
                guard_pending = False
                continue
            guard_pending = False
        if match is None:
            continue
        names.append(match.group(1))
    return names


def _collect_contracts(sources: list[Path]) -> tuple[set[str], dict[str, list[Path]]]:
    names: set[str] = set()
    locations: dict[str, list[Path]] = {}
    for path in sources:
        text = path.read_text(encoding="utf-8")
        for name in _collect_contracts_from_text(text):
            names.add(name)
            locations.setdefault(name, []).append(path)
    duplicates = {name: paths for name, paths in locations.items() if len(paths) > 1}
    return names, duplicates


def _extract_macro_specs_block(text: str) -> str | None:
    match = MACRO_SPECS_DEF_RE.search(text)
    if match is None:
        return None

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


def _check_coverage(contract_sources: list[Path], fuzz_suite: Path) -> int:
    declared, duplicate_declarations = _collect_contracts(contract_sources)
    covered_entries = _collect_suite_entries(fuzz_suite)

    if covered_entries is None:
        print("macro round-trip fuzz coverage check failed:", file=sys.stderr)
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

    missing = sorted((declared - EXCLUDED_CONTRACTS) - covered)
    extra = sorted(covered - declared)

    if not missing and not extra and not duplicate_entries and not duplicate_declarations:
        print("macro round-trip fuzz coverage OK")
        return 0

    print("macro round-trip fuzz coverage check failed:", file=sys.stderr)
    for name in sorted(duplicate_declarations):
        paths = ", ".join(sorted(str(path) for path in duplicate_declarations[name]))
        print(
            f"  duplicate verity_contract declaration name: {name} ({paths})",
            file=sys.stderr,
        )
    for name in duplicate_entries:
        print(
            f"  duplicate macroSpecs entry in Contracts/MacroTranslateRoundTripFuzz.lean: {name}",
            file=sys.stderr,
        )
    for name in missing:
        print(
            f"  missing in Contracts/MacroTranslateRoundTripFuzz.lean: {name}",
            file=sys.stderr,
        )
    for name in extra:
        print(
            f"  unknown in Contracts/MacroTranslateRoundTripFuzz.lean: {name}",
            file=sys.stderr,
        )
    return 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--contracts-dir",
        default=str(DEFAULT_CONTRACTS_DIR.relative_to(ROOT)),
        help="Directory containing macro contract declarations (default: Contracts).",
    )
    parser.add_argument(
        "--fuzz-suite",
        default=str(DEFAULT_FUZZ_FILE.relative_to(ROOT)),
        help="Round-trip fuzz suite file to validate (default: Contracts/MacroTranslateRoundTripFuzz.lean).",
    )
    args = parser.parse_args(argv)

    contracts_dir = ROOT / args.contracts_dir
    fuzz_suite = ROOT / args.fuzz_suite

    if not contracts_dir.exists() or not contracts_dir.is_dir():
        print(f"contracts directory not found: {contracts_dir}", file=sys.stderr)
        return 1

    if not fuzz_suite.exists():
        print(f"round-trip fuzz suite file not found: {fuzz_suite}", file=sys.stderr)
        return 1

    contract_sources = sorted(contracts_dir.rglob("*.lean"))
    if not contract_sources:
        print(f"no .lean files found under: {contracts_dir}", file=sys.stderr)
        return 1

    return _check_coverage(contract_sources, fuzz_suite)


if __name__ == "__main__":
    raise SystemExit(main())
