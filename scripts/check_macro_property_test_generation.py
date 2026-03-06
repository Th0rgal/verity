#!/usr/bin/env python3
"""Check/sync generated macro-property test stubs.

Usage:
  python3 scripts/check_macro_property_test_generation.py
  python3 scripts/check_macro_property_test_generation.py --check
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

import generate_macro_property_tests as generator
from property_utils import ROOT

DEFAULT_SOURCE = ROOT / "Contracts" / "MacroContracts" / "Core.lean"
DEFAULT_SOURCE_DIR = ROOT / "Contracts" / "MacroContracts"
DEFAULT_OUTPUT_DIR = ROOT / "artifacts" / "macro_property_tests"


def _expected_rendered(
    sources: list[Path],
    selected_contracts: list[str] | None,
) -> dict[str, str]:
    contracts = generator.collect_contracts(sources)
    if not contracts:
        raise SystemExit("no verity_contract declarations found")

    names = selected_contracts or sorted(contracts.keys())
    unknown = [name for name in names if name not in contracts]
    if unknown:
        known = ", ".join(sorted(contracts.keys()))
        raise SystemExit(f"unknown contract(s): {', '.join(unknown)}; known: {known}")

    rendered: dict[str, str] = {}
    for name in names:
        rendered[f"Property{name}.t.sol"] = generator.render_contract_test(contracts[name])
    return rendered


def _collect_existing(output_dir: Path) -> dict[str, str]:
    if not output_dir.exists():
        return {}
    return {
        path.name: path.read_text(encoding="utf-8")
        for path in sorted(output_dir.glob("Property*.t.sol"))
    }


def _check(output_dir: Path, expected: dict[str, str]) -> int:
    existing = _collect_existing(output_dir)
    expected_names = set(expected.keys())
    existing_names = set(existing.keys())

    missing = sorted(expected_names - existing_names)
    extra = sorted(existing_names - expected_names)
    stale = sorted(name for name in expected_names & existing_names if existing[name] != expected[name])

    if not missing and not extra and not stale:
        print(f"macro property-test artifacts are up to date: {output_dir.relative_to(ROOT)}")
        return 0

    print("macro property-test artifact check failed:", file=sys.stderr)
    for name in missing:
        print(f"  missing: {name}", file=sys.stderr)
    for name in extra:
        print(f"  unexpected: {name}", file=sys.stderr)
    for name in stale:
        print(f"  stale: {name}", file=sys.stderr)
    print(
        "regenerate with:\n"
        "  python3 scripts/check_macro_property_test_generation.py",
        file=sys.stderr,
    )
    return 1


def _write(output_dir: Path, expected: dict[str, str]) -> int:
    output_dir.mkdir(parents=True, exist_ok=True)
    for name, content in sorted(expected.items()):
        (output_dir / name).write_text(content, encoding="utf-8")

    for path in sorted(output_dir.glob("Property*.t.sol")):
        if path.name not in expected:
            path.unlink()

    print(
        "wrote macro property-test artifacts "
        f"({len(expected)} file(s)): {output_dir.relative_to(ROOT)}"
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source",
        action="append",
        default=[],
        help=(
            "Lean source path to scan (relative to repo root). "
            "Repeat flag for multiple files. Defaults to Contracts/MacroContracts/**/*.lean."
        ),
    )
    parser.add_argument(
        "--contract",
        action="append",
        default=[],
        help="Only generate/check the named contract (repeatable). Defaults to all discovered contracts.",
    )
    parser.add_argument(
        "--output-dir",
        default=str(DEFAULT_OUTPUT_DIR.relative_to(ROOT)),
        help="Output directory relative to repo root (default: artifacts/macro_property_tests).",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail if generated macro-property artifacts are missing/stale.",
    )
    args = parser.parse_args(argv)

    if args.source:
        source_paths = [ROOT / p for p in args.source]
    else:
        source_paths = generator.discover_macro_contract_sources(DEFAULT_SOURCE_DIR)
        if not source_paths:
            source_paths = [DEFAULT_SOURCE]
    missing_sources = [str(p.relative_to(ROOT)) for p in source_paths if not p.exists()]
    if missing_sources:
        print(
            f"source file(s) not found: {', '.join(missing_sources)}",
            file=sys.stderr,
        )
        return 1

    expected = _expected_rendered(source_paths, args.contract or None)
    output_dir = ROOT / args.output_dir
    if args.check:
        return _check(output_dir, expected)
    return _write(output_dir, expected)


if __name__ == "__main__":
    raise SystemExit(main())
