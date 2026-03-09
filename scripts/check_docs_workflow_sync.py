#!/usr/bin/env python3
"""Validate docs workflow trigger paths."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from property_utils import ROOT

DOCS_WORKFLOW = ROOT / ".github" / "workflows" / "docs.yml"
EXPECTED_PATHS = [
    ".github/workflows/docs.yml",
    "docs-site/**",
]


def _normalize_path(raw: str) -> str:
    value = raw.strip()
    if value.startswith("- "):
        value = value[2:].strip()
    if (value.startswith("'") and value.endswith("'")) or (
        value.startswith('"') and value.endswith('"')
    ):
        value = value[1:-1]
    return value


def _extract_list_block(text: str, pattern: str, label: str, workflow_path: Path) -> list[str]:
    match = re.search(pattern, text, re.MULTILINE)
    if not match:
        raise ValueError(f"Could not locate {label} in {workflow_path}")
    block = match.group("block")
    entries = [_normalize_path(line) for line in block.splitlines() if line.strip()]
    if not entries:
        raise ValueError(f"{label} is empty in {workflow_path}")
    return entries


def _extract_push_paths(text: str, workflow_path: Path) -> list[str]:
    return _extract_list_block(
        text,
        r"^  push:\n(?:^    .*\n)*?^    paths:\n(?P<block>(?:^      - .*\n)+)",
        "on.push.paths",
        workflow_path,
    )


def _extract_pr_paths(text: str, workflow_path: Path) -> list[str]:
    return _extract_list_block(
        text,
        r"^  pull_request:\n(?:^    .*\n)*?^    paths:\n(?P<block>(?:^      - .*\n)+)",
        "on.pull_request.paths",
        workflow_path,
    )


def _compare_lists(name_a: str, a: list[str], name_b: str, b: list[str]) -> list[str]:
    if a == b:
        return []
    errors = [f"{name_a} does not match {name_b}."]
    max_len = max(len(a), len(b))
    for i in range(max_len):
        va = a[i] if i < len(a) else "<missing>"
        vb = b[i] if i < len(b) else "<missing>"
        if va != vb:
            errors.append(f"  idx {i}: {name_a}={va!r}, {name_b}={vb!r}")
    return errors


def check_docs_workflow_sync(workflow_path: Path = DOCS_WORKFLOW) -> int:
    text = workflow_path.read_text(encoding="utf-8")
    push_paths = _extract_push_paths(text, workflow_path)
    pr_paths = _extract_pr_paths(text, workflow_path)

    errors: list[str] = []
    errors.extend(_compare_lists("on.push.paths", push_paths, "expected paths", EXPECTED_PATHS))
    errors.extend(_compare_lists("on.pull_request.paths", pr_paths, "expected paths", EXPECTED_PATHS))
    errors.extend(_compare_lists("on.push.paths", push_paths, "on.pull_request.paths", pr_paths))

    if errors:
        print("docs workflow sync failed:", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1

    print(f"docs workflow paths OK ({workflow_path})")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--workflow",
        default=str(DOCS_WORKFLOW.relative_to(ROOT)),
        help="Path to docs workflow relative to repo root (default: .github/workflows/docs.yml).",
    )
    args = parser.parse_args()
    return check_docs_workflow_sync(ROOT / args.workflow)


if __name__ == "__main__":
    raise SystemExit(main())
