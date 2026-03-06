#!/usr/bin/env python3
"""Validate GitHub issue templates for structure and contamination."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from property_utils import ROOT

DEFAULT_TEMPLATES_DIR = ROOT / ".github" / "ISSUE_TEMPLATE"
REQUIRED_TOP_LEVEL_KEYS = {"name", "description", "title", "labels", "body"}
DISALLOWED_TOP_LEVEL_KEYS = {"about"}
TOP_LEVEL_KEY_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_-]*):")

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
    files = sorted(templates_dir.glob("*.yml")) + sorted(templates_dir.glob("*.yaml"))
    return sorted({path for path in files if path.is_file() and path.name != "config.yml"})


def _render_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def _collect_top_level_keys(text: str) -> set[str]:
    keys: set[str] = set()
    for line in text.splitlines():
        if not line or line.startswith(" ") or line.startswith("\t"):
            continue
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        match = TOP_LEVEL_KEY_RE.match(line)
        if match:
            keys.add(match.group(1))
    return keys


def _check_form(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    keys = _collect_top_level_keys(text)
    issues: list[str] = []

    missing = sorted(REQUIRED_TOP_LEVEL_KEYS - keys)
    if missing:
        issues.append(f"missing required key(s): {', '.join(missing)}")

    forbidden = sorted(DISALLOWED_TOP_LEVEL_KEYS & keys)
    if forbidden:
        issues.append(f"disallowed key(s): {', '.join(forbidden)}")

    return issues


def check_issue_templates(templates_dir: Path) -> int:
    if not templates_dir.exists() or not templates_dir.is_dir():
        print(f"issue template directory not found: {templates_dir}", file=sys.stderr)
        return 1

    templates = _template_files(templates_dir)
    if not templates:
        print(f"no issue form templates found under: {templates_dir}", file=sys.stderr)
        return 1

    failures: list[str] = []
    for template in templates:
        for issue in _check_form(template):
            failures.append(f"{_render_path(template)}: {issue}")
        failures.extend(_find_log_artifacts(template))

    if failures:
        print("issue template validation failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print(f"issue templates OK ({len(templates)} file(s))")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--templates-dir",
        default=str(DEFAULT_TEMPLATES_DIR.relative_to(ROOT)),
        help="Path to issue template directory relative to repo root (default: .github/ISSUE_TEMPLATE).",
    )
    args = parser.parse_args()

    return check_issue_templates(ROOT / args.templates_dir)


if __name__ == "__main__":
    raise SystemExit(main())
