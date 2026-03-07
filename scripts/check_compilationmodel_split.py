#!/usr/bin/env python3
"""Guard the CompilationModel facade split against regressions."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, strip_lean_comments

FACADE = ROOT / "Compiler" / "CompilationModel.lean"
SUBMODULE_DIR = ROOT / "Compiler" / "CompilationModel"
MAX_FACADE_LINES = 200
IMPORT_RE = re.compile(r"^\s*import\s+(?P<module>[A-Za-z0-9_.']+)\s*$")


def _render_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def _discover_expected_imports(submodule_dir: Path) -> list[str]:
    modules: list[str] = []
    for path in sorted(submodule_dir.rglob("*.lean")):
        relative = path.relative_to(submodule_dir).with_suffix("")
        modules.append(
            "Compiler.CompilationModel." + ".".join(relative.parts)
        )
    return modules


def _collect_imports(lines: list[str]) -> list[str]:
    imports: list[str] = []
    for line in lines:
        match = IMPORT_RE.match(line)
        if match is not None:
            imports.append(match.group("module"))
    return imports


def _find_non_import_lines(facade: Path) -> list[str]:
    stripped = strip_lean_comments(facade.read_text(encoding="utf-8"))
    errors: list[str] = []
    for line_no, line in enumerate(stripped.splitlines(), 1):
        text = line.strip()
        if not text:
            continue
        if IMPORT_RE.match(text):
            continue
        errors.append(
            f"{_render_path(facade)}:{line_no}: facade should contain only imports/comments, found `{text}`"
        )
    return errors


def check_compilationmodel_split(
    *,
    facade: Path | None = None,
    submodule_dir: Path | None = None,
    max_facade_lines: int = MAX_FACADE_LINES,
) -> int:
    failures: list[str] = []

    facade_path = FACADE if facade is None else facade
    submodule_path = SUBMODULE_DIR if submodule_dir is None else submodule_dir

    line_count = len(facade_path.read_text(encoding="utf-8").splitlines())
    if line_count > max_facade_lines:
        failures.append(
            f"{_render_path(facade_path)}: expected at most {max_facade_lines} lines, found {line_count}"
        )

    failures.extend(_find_non_import_lines(facade_path))

    expected_imports = _discover_expected_imports(submodule_path)
    actual_imports = _collect_imports(
        strip_lean_comments(facade_path.read_text(encoding="utf-8")).splitlines()
    )

    missing = sorted(set(expected_imports) - set(actual_imports))
    unexpected = sorted(
        module for module in actual_imports if not module.startswith("Compiler.CompilationModel.")
    )

    if missing:
        failures.append(
            f"{_render_path(facade_path)}: missing facade imports for {len(missing)} submodule(s)"
        )
        failures.extend(f"  missing {module}" for module in missing)

    if unexpected:
        failures.append(
            f"{_render_path(facade_path)}: unexpected non-CompilationModel import(s) present"
        )
        failures.extend(f"  unexpected {module}" for module in unexpected)

    if failures:
        print("CompilationModel split check failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print(
        "CompilationModel split check passed "
        f"({line_count} facade lines, {len(expected_imports)} submodule imports)."
    )
    return 0


def main() -> int:
    return check_compilationmodel_split()


if __name__ == "__main__":
    raise SystemExit(main())
