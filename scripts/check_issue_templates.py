#!/usr/bin/env python3
"""Fail if issue templates contain pasted CI/GitHub Actions log output."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from property_utils import ROOT

DEFAULT_TEMPLATES_DIR = ROOT / ".github" / "ISSUE_TEMPLATE"

LOG_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("timestamped runner log line", re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z\b")),
    ("GitHub Actions group marker", re.compile(r"##\[(?:group|endgroup|error|warning)\]")),
    ("runner home/work path", re.compile(r"/home/runner/work/")),
    ("runner version banner", re.compile(r"Current runner version:\s*'[^']+'")),
    ("rendered ANSI escape sequence", re.compile(r"\^\[\[[0-9;]*[A-Za-z]")),
]


def _find_log_artifacts(path: Path) -> list[str]:
    findings: list[str] = []
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        for label, pattern in LOG_PATTERNS:
            if pattern.search(line):
                findings.append(f"{path}:{lineno}: {label}")
                break
    return findings


def _template_files(templates_dir: Path) -> list[Path]:
    return sorted(path for path in templates_dir.glob("*.yml") if path.is_file())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--templates-dir",
        default=str(DEFAULT_TEMPLATES_DIR.relative_to(ROOT)),
        help="Path to issue template directory relative to repo root (default: .github/ISSUE_TEMPLATE).",
    )
    args = parser.parse_args()

    templates_dir = ROOT / args.templates_dir
    if not templates_dir.exists() or not templates_dir.is_dir():
        print(f"issue template directory not found: {templates_dir}", file=sys.stderr)
        return 1

    templates = _template_files(templates_dir)
    if not templates:
        print(f"no .yml issue templates found under: {templates_dir}", file=sys.stderr)
        return 1

    findings: list[str] = []
    for template in templates:
        findings.extend(_find_log_artifacts(template))

    if findings:
        print("issue template contamination check failed:", file=sys.stderr)
        for finding in findings:
            print(f"  {finding}", file=sys.stderr)
        return 1

    print("issue template contamination check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
