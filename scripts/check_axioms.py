#!/usr/bin/env python3
"""Validate AXIOMS.md sync and parse PrintAxioms output.

Usage:
    python3 scripts/check_axioms.py
    python3 scripts/check_axioms.py --log axiom-output.log
    lake env lean PrintAxioms.lean 2>&1 | python3 scripts/check_axioms.py --report
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

from property_utils import ROOT, die, report_errors, scrub_lean_code

AXIOM_DECL_RE = re.compile(r"^(?:private |protected )?axiom\s+([A-Za-z_][A-Za-z0-9_']*)\b")

LEAN_BUILTIN_AXIOMS = frozenset([
    "propext",
    "Quot.sound",
    "Classical.choice",
])

DOCUMENTED_AXIOMS = frozenset([
    "keccak256_first_4_bytes",
    "solidityMappingSlot_lt_evmModulus",
    "solidityMappingSlot_add_wordOffset_lt_evmModulus",
])

FORBIDDEN_AXIOMS = frozenset([
    "sorryAx",
])


def parse_axiom_entries(axioms_md_text: str) -> list[tuple[str, str, int]]:
    """Extract ``(axiom_name, relative_path, claimed_line)`` entries from AXIOMS.md."""
    blocks = re.findall(
        r"### \d+\.\s+`([^`]+)`(?:[^\n]*)\n\n"
        r"\*\*Location\*\*:\s*`([^:]+):(\d+)`",
        axioms_md_text,
    )
    return [(name, rel_path, int(line)) for name, rel_path, line in blocks]


def parse_active_axiom_count(axioms_md_text: str) -> int | None:
    """Extract trust-summary active axiom count from AXIOMS.md, if present."""
    match = re.search(r"^- Active axioms:\s*(\d+)\s*$", axioms_md_text, flags=re.MULTILINE)
    if match is None:
        return None
    return int(match.group(1))


def discover_repo_axioms() -> dict[str, tuple[str, int]]:
    """Return all Lean axiom declarations as ``{name: (relative_path, line)}``."""
    discovered: dict[str, tuple[str, int]] = {}
    for subdir in ("Compiler", "Verity"):
        base_dir = ROOT / subdir
        if not base_dir.exists():
            continue
        for lean_file in sorted(base_dir.rglob("*.lean")):
            text = scrub_lean_code(lean_file.read_text(encoding="utf-8"))
            rel_path = str(lean_file.relative_to(ROOT))
            for i, line in enumerate(text.splitlines(), 1):
                match = AXIOM_DECL_RE.match(line)
                if match is None:
                    continue
                name = match.group(1)
                if name in discovered:
                    old_path, old_line = discovered[name]
                    die(
                        f"Duplicate axiom name {name!r}: "
                        f"{old_path}:{old_line} and {rel_path}:{i}"
                    )
                discovered[name] = (rel_path, i)
    return discovered


def run_location_check() -> int:
    axioms_md = ROOT / "AXIOMS.md"
    if not axioms_md.exists():
        die("AXIOMS.md not found")

    text = axioms_md.read_text(encoding="utf-8")
    axiom_blocks = parse_axiom_entries(text)
    if not axiom_blocks:
        die("No axiom location entries found in AXIOMS.md")

    discovered_axioms = discover_repo_axioms()
    documented_names = {name for name, _, _ in axiom_blocks}
    discovered_names = set(discovered_axioms)

    errors: list[str] = []
    checked = 0

    for axiom_name, rel_path, claimed_line in axiom_blocks:
        source_file = ROOT / rel_path
        if not source_file.exists():
            errors.append(f"{axiom_name}: file {rel_path} not found")
            continue

        lines = source_file.read_text(encoding="utf-8").splitlines()
        actual_line = None
        for i, line in enumerate(lines, 1):
            if re.match(rf"^(private |protected )?axiom\s+{re.escape(axiom_name)}\b", line):
                actual_line = i
                break

        if actual_line is None:
            errors.append(
                f"{axiom_name}: not found in {rel_path} "
                f"(AXIOMS.md claims line {claimed_line})"
            )
        elif actual_line != claimed_line:
            errors.append(
                f"{axiom_name}: AXIOMS.md says line {claimed_line} "
                f"but actually at line {actual_line} in {rel_path}"
            )
        else:
            print(f"  OK {axiom_name} at {rel_path}:{actual_line}")
            checked += 1

    missing_from_docs = sorted(discovered_names - documented_names)
    for axiom_name in missing_from_docs:
        rel_path, line = discovered_axioms[axiom_name]
        errors.append(
            f"{axiom_name}: declared in {rel_path}:{line} but missing from AXIOMS.md"
        )

    stale_doc_entries = sorted(documented_names - discovered_names)
    for axiom_name in stale_doc_entries:
        errors.append(f"{axiom_name}: listed in AXIOMS.md but no Lean axiom declaration exists")

    active_count = parse_active_axiom_count(text)
    if active_count is None:
        errors.append("AXIOMS.md: missing '- Active axioms: N' trust summary line")
    elif active_count != len(discovered_axioms):
        errors.append(
            f"AXIOMS.md trust summary says Active axioms: {active_count}, "
            f"but source has {len(discovered_axioms)}"
        )

    report_errors(errors, "Axiom location check failed")
    print(
        f"\nOK: {checked} documented axiom locations are accurate; "
        f"registry is complete and synchronized with {len(discovered_axioms)} source axioms"
    )
    return 0


def parse_axiom_output(text: str) -> dict[str, list[str]]:
    """Parse Lean ``#print axioms`` output into ``{theorem_name: [axioms]}``."""
    results: dict[str, list[str]] = {}

    for line in text.splitlines():
        line = line.strip()
        match = re.match(r"'(.+)' depends on axioms: \[(.+)\]", line)
        if match:
            name = match.group(1)
            axioms = [axiom.strip() for axiom in match.group(2).split(",")]
            results[name] = axioms
            continue

        match = re.match(r"'(.+)' does not depend on any axioms", line)
        if match:
            results[match.group(1)] = []

    return results


def classify_axioms(
    axiom_map: dict[str, list[str]],
) -> tuple[set[str], set[str], set[str], dict[str, list[str]]]:
    """Classify axioms into builtin, documented, forbidden, and unexpected."""
    all_axioms: set[str] = set()
    for axioms in axiom_map.values():
        all_axioms.update(axioms)

    builtin = all_axioms & LEAN_BUILTIN_AXIOMS
    documented = all_axioms & DOCUMENTED_AXIOMS
    forbidden = all_axioms & FORBIDDEN_AXIOMS
    unexpected = all_axioms - LEAN_BUILTIN_AXIOMS - DOCUMENTED_AXIOMS - FORBIDDEN_AXIOMS

    unexpected_usage: dict[str, list[str]] = {}
    for axiom in unexpected:
        unexpected_usage[axiom] = [
            theorem for theorem, axioms in axiom_map.items() if axiom in axioms
        ]

    return builtin, documented, forbidden, unexpected_usage


def generate_report(
    axiom_map: dict[str, list[str]],
    builtin: set[str],
    documented: set[str],
    forbidden: set[str],
    unexpected_usage: dict[str, list[str]],
) -> str:
    """Generate a human-readable axiom dependency report."""
    lines = ["# Axiom Dependency Report", ""]

    total = len(axiom_map)
    axiom_free = sum(1 for axioms in axiom_map.values() if not axioms)
    builtin_only = sum(
        1
        for axioms in axiom_map.values()
        if axioms and all(axiom in LEAN_BUILTIN_AXIOMS for axiom in axioms)
    )
    uses_documented = sum(
        1 for axioms in axiom_map.values() if any(axiom in DOCUMENTED_AXIOMS for axiom in axioms)
    )

    lines.append(f"Total theorems checked: {total}")
    lines.append(f"Axiom-free (pure logic): {axiom_free}")
    lines.append(f"Uses only Lean builtins (propext, Quot.sound, Classical.choice): {builtin_only}")
    lines.append(f"Uses documented project axioms: {uses_documented}")
    lines.append("")

    lines.append("## Lean Builtin Axioms Used")
    for axiom in sorted(builtin - FORBIDDEN_AXIOMS):
        lines.append(f"  - {axiom}")
    lines.append("")

    lines.append("## Documented Project Axioms")
    for axiom in sorted(documented):
        users = [theorem for theorem, axioms in axiom_map.items() if axiom in axioms]
        lines.append(f"  - {axiom} (used by {len(users)} theorems)")
    lines.append("")

    if forbidden:
        lines.append("## FORBIDDEN AXIOMS DETECTED")
        for axiom in sorted(forbidden):
            users = [theorem for theorem, axioms in axiom_map.items() if axiom in axioms]
            lines.append(f"  - {axiom} (used by {len(users)} theorems)")
            for theorem in users[:10]:
                lines.append(f"      {theorem}")
        lines.append("")

    if unexpected_usage:
        lines.append("## UNEXPECTED AXIOMS DETECTED")
        for axiom, users in sorted(unexpected_usage.items()):
            lines.append(f"  - {axiom} (used by {len(users)} theorems)")
            for theorem in users[:10]:
                lines.append(f"      {theorem}")
        lines.append("")

    if not forbidden and not unexpected_usage:
        lines.append("## Result: PASS")
        lines.append("All theorems depend only on Lean builtins and documented project axioms.")
    else:
        lines.append("## Result: FAIL")
        lines.append("Unexpected or forbidden axioms detected.")

    return "\n".join(lines) + "\n"


def run_report_check(text: str) -> int:
    axiom_map = parse_axiom_output(text)
    if not axiom_map:
        print("WARNING: No #print axioms output found. Is the input empty?", file=sys.stderr)
        print("Parsed 0 theorems from input.", file=sys.stderr)
        return 1

    builtin, documented, forbidden, unexpected_usage = classify_axioms(axiom_map)
    report = generate_report(axiom_map, builtin, documented, forbidden, unexpected_usage)
    print(report)

    output_file = os.environ.get("AXIOM_REPORT_FILE")
    if output_file:
        Path(output_file).write_text(report, encoding="utf-8")
        print(f"Report written to {output_file}", file=sys.stderr)

    if forbidden or unexpected_usage:
        return 1
    return 0


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--locations", action="store_true", help="run AXIOMS.md location validation")
    mode.add_argument("--report", action="store_true", help="parse #print axioms output from stdin or --log")
    parser.add_argument("--log", type=Path, help="path to a PrintAxioms output log")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if args.report or args.log is not None:
        if args.log is not None:
            text = args.log.read_text(encoding="utf-8")
        else:
            text = sys.stdin.read()
        return run_report_check(text)

    return run_location_check()


if __name__ == "__main__":
    raise SystemExit(main())
