#!/usr/bin/env python3
"""Validate path safety and Layer-2 bridge universality invariants."""

from __future__ import annotations

import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path, PurePosixPath

from property_utils import ROOT, strip_lean_comments

TARGET = ROOT / "Contracts" / "Proofs" / "SemanticBridge.lean"

THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma)\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)
STATE_PARAM_RE = re.compile(r"\(\s*state\s*:\s*ContractState\s*\)")
SENDER_PARAM_RE = re.compile(r"\(\s*sender\s*:\s*Address\s*\)")

LEGACY_ANTI_PATTERNS: tuple[tuple[str, str], ...] = (
    ("SpecStorage.empty", "fixed empty initial storage"),
    ("test_sender", "fixed concrete sender"),
    ("let initialStorage :=", "local fixed-storage theorem pattern"),
)


def _render_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def _git_tracked_paths() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files"],
        check=True,
        capture_output=True,
        text=True,
    )
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def _collect_case_keys(paths: list[str]) -> dict[str, set[str]]:
    keys: dict[str, set[str]] = defaultdict(set)
    for path_str in paths:
        path = PurePosixPath(path_str)
        for i in range(1, len(path.parts) + 1):
            original = "/".join(path.parts[:i])
            keys[original.lower()].add(original)
    return keys


def _find_case_conflicts(paths: list[str]) -> list[list[str]]:
    conflicts: list[list[str]] = []
    for originals in _collect_case_keys(paths).values():
        if len(originals) > 1:
            conflicts.append(sorted(originals))
    conflicts.sort()
    return conflicts


def _collect_semantic_bridge_headers(lines: list[str]) -> list[tuple[str, int, str]]:
    headers: list[tuple[str, int, str]] = []
    i = 0
    while i < len(lines):
        match = THEOREM_RE.match(lines[i])
        if match is None:
            i += 1
            continue

        name = match.group("name")
        if not name.endswith("_semantic_bridge"):
            i += 1
            continue

        start = i
        header_lines = [lines[i]]
        i += 1
        while i < len(lines):
            header_lines.append(lines[i])
            if re.search(r":\s*$", lines[i]):
                break
            i += 1

        headers.append((name, start + 1, "\n".join(header_lines)))
        i += 1

    return headers


def _find_layer2_universality_issues(target: Path) -> tuple[list[str], int]:
    errors: list[str] = []
    text = strip_lean_comments(target.read_text(encoding="utf-8"))
    lines = text.splitlines()

    theorem_headers = _collect_semantic_bridge_headers(lines)
    if not theorem_headers:
        errors.append(f"{_render_path(target)}: no *_semantic_bridge theorem headers found")

    for name, line_no, header in theorem_headers:
        if STATE_PARAM_RE.search(header) is None:
            errors.append(
                f"{_render_path(target)}:{line_no}: {name} is missing "
                "`(state : ContractState)` quantification"
            )
        if SENDER_PARAM_RE.search(header) is None:
            errors.append(
                f"{_render_path(target)}:{line_no}: {name} is missing "
                "`(sender : Address)` quantification"
            )

    for needle, reason in LEGACY_ANTI_PATTERNS:
        for idx, line in enumerate(lines, 1):
            if needle in line:
                errors.append(
                    f"{_render_path(target)}:{idx}: found `{needle}` "
                    f"(legacy non-universal pattern: {reason})"
                )

    return errors, len(theorem_headers)


def check_paths(*, tracked_paths: list[str] | None = None, semantic_bridge: Path | None = None) -> int:
    failures: list[str] = []

    paths = _git_tracked_paths() if tracked_paths is None else tracked_paths
    case_conflicts = _find_case_conflicts(paths)
    if case_conflicts:
        failures.append("case-insensitive path conflicts detected in tracked files/directories")
        failures.append("These collide on macOS/Windows and can cause checkout/build failures")
        failures.extend("- " + "  <->  ".join(group) for group in case_conflicts)

    target = TARGET if semantic_bridge is None else semantic_bridge
    layer2_issues, theorem_count = _find_layer2_universality_issues(target)
    if layer2_issues:
        failures.append("Layer-2 universality issues detected")
        failures.extend(layer2_issues)

    if failures:
        print("path validation failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print(
        "path checks passed "
        f"({len(case_conflicts)} case-conflict groups, {theorem_count} semantic bridge theorem headers validated)."
    )
    return 0


def main() -> int:
    return check_paths()


if __name__ == "__main__":
    raise SystemExit(main())
