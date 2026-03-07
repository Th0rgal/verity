#!/usr/bin/env python3
"""Ensure split-package lakefiles only export their intended module surfaces."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, strip_lean_comments

ONE_GLOB_RE = re.compile(r"\.one\s+`([A-Za-z0-9_.']+)")
AND_SUBMODULES_GLOB_RE = re.compile(r"\.andSubmodules\s+`([A-Za-z0-9_.']+)")
SUBMODULES_GLOB_RE = re.compile(r"\.submodules\s+`([A-Za-z0-9_.']+)")

BRIDGE_GLOBS = {
    ("one", "Verity.Macro"),
    ("andSubmodules", "Verity.Macro"),
    ("submodules", "Verity.Macro"),
    ("one", "Verity.Proofs.Stdlib.Automation"),
    ("one", "Verity.Proofs.Stdlib.MappingAutomation"),
}

PACKAGE_SURFACES = (
    (ROOT / "packages" / "verity-edsl" / "lakefile.lean", "verity-edsl"),
    (ROOT / "packages" / "verity-compiler" / "lakefile.lean", "verity-compiler"),
    (ROOT / "packages" / "verity-examples" / "lakefile.lean", "verity-examples"),
)


def _render_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def _iter_globs(lakefile: Path) -> list[tuple[str, str, int]]:
    contents = strip_lean_comments(lakefile.read_text(encoding="utf-8"))
    globs: list[tuple[str, str, int]] = []
    for line_no, line in enumerate(contents.splitlines(), 1):
        for module_name in ONE_GLOB_RE.findall(line):
            globs.append(("one", module_name, line_no))
        for module_name in AND_SUBMODULES_GLOB_RE.findall(line):
            globs.append(("andSubmodules", module_name, line_no))
        for module_name in SUBMODULES_GLOB_RE.findall(line):
            globs.append(("submodules", module_name, line_no))
    return globs


def _is_owned_namespace(module_name: str, namespace: str) -> bool:
    return module_name == namespace or module_name.startswith(f"{namespace}.")


def _format_bridge_allowlist() -> str:
    return ", ".join(
        sorted(f".{glob_kind} `{module_name}`" for glob_kind, module_name in BRIDGE_GLOBS)
    )


def collect_surface_failures(
    package_surfaces: tuple[tuple[Path, str], ...] = PACKAGE_SURFACES,
) -> list[str]:
    failures: list[str] = []
    for lakefile, package_name in package_surfaces:
        if not lakefile.exists():
            failures.append(f"missing package lakefile: {_render_path(lakefile)}")
            continue

        for glob_kind, module_name, line_no in _iter_globs(lakefile):
            if package_name == "verity-edsl":
                if _is_owned_namespace(module_name, "Verity"):
                    continue
                failures.append(
                    f"{_render_path(lakefile)}:{line_no}: unexpected {package_name} glob "
                    f".{glob_kind} `{module_name}` (expected only Verity modules)"
                )
                continue

            if package_name == "verity-examples":
                if _is_owned_namespace(module_name, "Contracts"):
                    continue
                failures.append(
                    f"{_render_path(lakefile)}:{line_no}: unexpected {package_name} glob "
                    f".{glob_kind} `{module_name}` (expected only Contracts modules)"
                )
                continue

            if package_name == "verity-compiler":
                if _is_owned_namespace(module_name, "Compiler"):
                    continue
                if (glob_kind, module_name) in BRIDGE_GLOBS:
                    continue
                failures.append(
                    f"{_render_path(lakefile)}:{line_no}: unexpected {package_name} glob "
                    f".{glob_kind} `{module_name}`; allowed non-Compiler bridge globs: "
                    f"{_format_bridge_allowlist()}"
                )
                continue

            failures.append(
                f"{_render_path(lakefile)}:{line_no}: unsupported package surface rule for {package_name}"
            )
    return failures


def main_for_surfaces(
    package_surfaces: tuple[tuple[Path, str], ...] = PACKAGE_SURFACES,
) -> int:
    failures = collect_surface_failures(package_surfaces)
    if failures:
        print("Package glob surface check failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print("Package glob surface check passed.")
    return 0


def main() -> int:
    return main_for_surfaces()


if __name__ == "__main__":
    raise SystemExit(main())
