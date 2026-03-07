#!/usr/bin/env python3
"""Ensure the split compiler package exports every standalone compiler test module."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from property_utils import ROOT, strip_lean_comments

DEFAULT_LAKEFILE = ROOT / "packages" / "verity-compiler" / "lakefile.lean"
COMPILER_DIR = ROOT / "Compiler"

ONE_GLOB_RE = re.compile(r"\.one\s+`([A-Za-z0-9_.']+)")
AND_SUBMODULES_GLOB_RE = re.compile(r"\.andSubmodules\s+`([A-Za-z0-9_.']+)")
SUBMODULES_GLOB_RE = re.compile(r"\.submodules\s+`([A-Za-z0-9_.']+)")


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--lakefile",
        type=Path,
        default=DEFAULT_LAKEFILE,
        help="Split compiler package lakefile to inspect.",
    )
    return parser.parse_args(argv)


def display_path(path: Path) -> Path:
    try:
        return path.relative_to(ROOT)
    except ValueError:
        return path


def iter_globs(lakefile: Path) -> list[tuple[str, str]]:
    contents = strip_lean_comments(lakefile.read_text(encoding="utf-8"))
    globs: list[tuple[str, str]] = []
    for line in contents.splitlines():
        globs.extend(("one", module_name) for module_name in ONE_GLOB_RE.findall(line))
        globs.extend(("andSubmodules", module_name) for module_name in AND_SUBMODULES_GLOB_RE.findall(line))
        globs.extend(("submodules", module_name) for module_name in SUBMODULES_GLOB_RE.findall(line))
    return globs


def expected_test_modules(compiler_dir: Path = COMPILER_DIR) -> list[str]:
    return sorted(f"Compiler.{path.stem}" for path in compiler_dir.glob("*Test.lean"))


def _is_direct_child(namespace: str, module_name: str) -> bool:
    prefix = f"{namespace}."
    if not module_name.startswith(prefix):
        return False
    return "." not in module_name[len(prefix) :]


def glob_covers_module(glob_kind: str, glob_module: str, module_name: str) -> bool:
    if glob_kind == "one":
        return glob_module == module_name
    if glob_kind == "andSubmodules":
        return module_name == glob_module or module_name.startswith(f"{glob_module}.")
    if glob_kind == "submodules":
        return _is_direct_child(glob_module, module_name)
    return False


def collect_missing_modules(lakefile: Path, modules: list[str]) -> list[str]:
    globs = iter_globs(lakefile)
    return [
        module_name
        for module_name in modules
        if not any(glob_covers_module(glob_kind, glob_module, module_name) for glob_kind, glob_module in globs)
    ]


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    lakefile = args.lakefile
    if not lakefile.is_file():
        print(
            f"split compiler test module coverage check failed: missing lakefile: {display_path(lakefile)}",
            file=sys.stderr,
        )
        return 1

    modules = expected_test_modules()
    if not modules:
        print("split compiler test module coverage check failed: no Compiler/*Test.lean modules found", file=sys.stderr)
        return 1

    missing = collect_missing_modules(lakefile, modules)
    if missing:
        print("split compiler test module coverage check failed:", file=sys.stderr)
        for module_name in missing:
            print(f"  missing coverage for {module_name} in {display_path(lakefile)}", file=sys.stderr)
        return 1

    print(f"Split compiler test module coverage check passed ({len(modules)} modules).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
