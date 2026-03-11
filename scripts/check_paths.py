#!/usr/bin/env python3
"""Validate path safety invariants (case-insensitive collision detection)."""

from __future__ import annotations

import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path, PurePosixPath

from property_utils import ROOT


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


def check_paths(*, tracked_paths: list[str] | None = None) -> int:
    failures: list[str] = []

    paths = _git_tracked_paths() if tracked_paths is None else tracked_paths
    case_conflicts = _find_case_conflicts(paths)
    if case_conflicts:
        failures.append("case-insensitive path conflicts detected in tracked files/directories")
        failures.append("These collide on macOS/Windows and can cause checkout/build failures")
        failures.extend("- " + "  <->  ".join(group) for group in case_conflicts)

    if failures:
        print("path validation failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print(
        "path checks passed "
        f"({len(case_conflicts)} case-conflict groups)."
    )
    return 0


def main() -> int:
    return check_paths()


if __name__ == "__main__":
    raise SystemExit(main())
