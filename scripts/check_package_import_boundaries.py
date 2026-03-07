#!/usr/bin/env python3
"""Ensure split Lake packages keep their intended import boundaries."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, strip_lean_comments

IMPORT_TEMPLATE = r"^\s*import\s+({namespace}\.[A-Za-z0-9_.']+)\s*$"
ONE_GLOB_RE = re.compile(r"\.one\s+`([A-Za-z0-9_.']+)")
AND_SUBMODULES_GLOB_RE = re.compile(r"\.andSubmodules\s+`([A-Za-z0-9_.']+)")

PACKAGE_BOUNDARIES = (
    (
        ROOT / "packages" / "verity-edsl" / "lakefile.lean",
        re.compile(IMPORT_TEMPLATE.format(namespace="Compiler"), re.MULTILINE),
        "verity-edsl",
        "Compiler",
    ),
    (
        ROOT / "packages" / "verity-compiler" / "lakefile.lean",
        re.compile(IMPORT_TEMPLATE.format(namespace="Contracts"), re.MULTILINE),
        "verity-compiler",
        "Contracts",
    ),
)


def _render_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def _module_to_file(root: Path, module_name: str) -> Path:
    return root / Path(*module_name.split(".")).with_suffix(".lean")


def _expand_lake_globs(lakefile: Path, source_root: Path) -> tuple[list[str], list[Path]]:
    contents = strip_lean_comments(lakefile.read_text(encoding="utf-8"))

    failures: list[str] = []
    paths: set[Path] = set()

    for module_name in ONE_GLOB_RE.findall(contents):
        path = _module_to_file(source_root, module_name)
        if path.exists():
            paths.add(path)
        else:
            failures.append(f"{_render_path(lakefile)}: missing module listed in globs: {module_name}")

    for module_name in AND_SUBMODULES_GLOB_RE.findall(contents):
        root_file = _module_to_file(source_root, module_name)
        if root_file.exists():
            paths.add(root_file)

        submodule_dir = source_root / Path(*module_name.split("."))
        if not submodule_dir.exists():
            failures.append(
                f"{_render_path(lakefile)}: missing submodule directory listed in globs: {module_name}"
            )
            continue

        submodule_files = sorted(submodule_dir.rglob("*.lean"))
        if not submodule_files and not root_file.exists():
            failures.append(
                f"{_render_path(lakefile)}: empty submodule glob without root module: {module_name}"
            )
            continue
        paths.update(submodule_files)

    return failures, sorted(paths)


def collect_forbidden_imports(
    package_boundaries: tuple[tuple[Path, re.Pattern[str], str, str], ...] = PACKAGE_BOUNDARIES,
    *,
    source_root: Path = ROOT,
) -> list[str]:
    failures: list[str] = []
    for lakefile, import_re, package_name, forbidden_namespace in package_boundaries:
        if not lakefile.exists():
            failures.append(f"missing package lakefile: {_render_path(lakefile)}")
            continue

        lake_failures, module_paths = _expand_lake_globs(lakefile, source_root)
        failures.extend(lake_failures)
        for path in module_paths:
            contents = strip_lean_comments(path.read_text(encoding="utf-8"))
            for line_no, line in enumerate(contents.splitlines(), 1):
                match = import_re.match(line)
                if match is None:
                    continue
                failures.append(
                    f"{_render_path(path)}:{line_no}: forbidden {package_name} -> "
                    f"{forbidden_namespace} import `{match.group(1)}`"
                )
    return failures


def main_for_boundaries(
    package_boundaries: tuple[tuple[Path, re.Pattern[str], str, str], ...] = PACKAGE_BOUNDARIES,
    *,
    source_root: Path = ROOT,
) -> int:
    failures = collect_forbidden_imports(package_boundaries, source_root=source_root)
    if failures:
        print("Package import boundary check failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print("Package import boundary check passed.")
    return 0


def main() -> int:
    return main_for_boundaries()


if __name__ == "__main__":
    raise SystemExit(main())
