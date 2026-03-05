#!/usr/bin/env python3
"""Validate GitHub Issue Form templates under .github/ISSUE_TEMPLATE."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT

TEMPLATE_DIR = ROOT / ".github" / "ISSUE_TEMPLATE"
REQUIRED_TOP_LEVEL_KEYS = {"name", "description", "title", "labels", "body"}
DISALLOWED_TOP_LEVEL_KEYS = {"about"}
TOP_LEVEL_KEY_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_-]*):")


def _iter_form_files(template_dir: Path) -> list[Path]:
    files = sorted(template_dir.glob("*.yml")) + sorted(template_dir.glob("*.yaml"))
    return sorted({path for path in files if path.name != "config.yml"})


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


def check_issue_template_forms(template_dir: Path) -> int:
    if not template_dir.exists() or not template_dir.is_dir():
        print(f"issue template directory not found: {template_dir}", file=sys.stderr)
        return 1

    forms = _iter_form_files(template_dir)
    if not forms:
        print(f"no issue form templates found in {template_dir}", file=sys.stderr)
        return 1

    failures: list[str] = []
    for form in forms:
        for issue in _check_form(form):
            failures.append(f"{_render_path(form)}: {issue}")

    if failures:
        print("issue template form check failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print(f"issue template forms OK ({len(forms)} file(s))")
    return 0


def main() -> int:
    return check_issue_template_forms(TEMPLATE_DIR)


if __name__ == "__main__":
    raise SystemExit(main())
