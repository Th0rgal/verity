#!/usr/bin/env python3
"""Ensure Compiler modules do not depend on concrete Contracts modules."""

from __future__ import annotations

import sys
from pathlib import Path

from property_utils import ROOT, extract_lean_import_modules, strip_lean_comments

COMPILER_DIR = ROOT / "Compiler"


def _render_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def _is_compiler_test_module(path: Path) -> bool:
    return path.name.endswith("Test.lean")


def collect_forbidden_imports(root: Path = COMPILER_DIR) -> list[str]:
    failures: list[str] = []
    for path in sorted(root.rglob("*.lean")):
        if _is_compiler_test_module(path):
            continue
        contents = strip_lean_comments(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(contents.splitlines(), 1):
            for module_name in extract_lean_import_modules(line):
                if module_name != "Contracts" and not module_name.startswith("Contracts."):
                    continue
                failures.append(
                    f"{_render_path(path)}:{line_no}: forbidden Compiler -> Contracts import `{module_name}`"
                )
    return failures


def main_for_root(root: Path = COMPILER_DIR) -> int:
    failures = collect_forbidden_imports(root)
    if failures:
        print("Compiler/Contracts boundary check failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print("Compiler/Contracts boundary check passed.")
    return 0


def main() -> int:
    return main_for_root()


if __name__ == "__main__":
    raise SystemExit(main())
