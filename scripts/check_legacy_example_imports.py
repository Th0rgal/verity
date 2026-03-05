#!/usr/bin/env python3
"""Fail closed on reintroduction of legacy migrated-contract imports.

Issue #1143:
- For migrated contracts, block `import Verity.Examples.<Contract>` in active code.
- Allow explicit temporary exemptions through a documented allowlist.
- Fail when allowlist entries become stale.
"""

from __future__ import annotations

import re
import sys
from collections import defaultdict
from pathlib import Path

from property_utils import ROOT, scrub_lean_code

MIGRATED_CONTRACTS = {
    "SimpleStorage",
    "Counter",
    "SafeCounter",
    "Owned",
    "OwnedCounter",
    "Ledger",
    "SimpleToken",
    "ERC20",
    "ERC721",
}

IMPORT_RE = re.compile(
    r"^\s*import\s+Verity\.Examples\.(?P<name>[A-Za-z_][A-Za-z0-9_]*)\b",
    flags=re.MULTILINE,
)

ALLOWLIST_PATH = ROOT / "scripts" / "legacy_example_import_allowlist.txt"
SCAN_ROOTS = [
    ROOT / "Compiler",
    ROOT / "Verity",
]
EXTRA_SCAN_FILES = [
    ROOT / "Compiler.lean",
    ROOT / "Verity.lean",
]


def discover_scan_files() -> list[Path]:
    files: list[Path] = []
    for root in SCAN_ROOTS:
        files.extend(sorted(root.rglob("*.lean")))
    files.extend(path for path in EXTRA_SCAN_FILES if path.exists())
    return sorted(set(files))


def parse_allowlist(path: Path) -> dict[Path, set[str]]:
    if not path.exists():
        raise SystemExit(f"Missing allowlist file: {path}")

    entries: dict[Path, set[str]] = {}
    for line_no, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if ":" not in line:
            raise SystemExit(
                f"Invalid allowlist entry at {path}:{line_no}: expected '<path>: <module>[, ...]'"
            )
        rel_raw, modules_raw = line.split(":", 1)
        rel_text = rel_raw.strip()
        modules = [token.strip() for token in modules_raw.split(",") if token.strip()]
        if not rel_text or not modules:
            raise SystemExit(
                f"Invalid allowlist entry at {path}:{line_no}: expected non-empty path and module list"
            )
        rel_path = Path(rel_text)
        if rel_path.is_absolute():
            raise SystemExit(
                f"Invalid allowlist entry at {path}:{line_no}: path must be repository-relative"
            )
        unknown = sorted(set(modules) - MIGRATED_CONTRACTS)
        if unknown:
            raise SystemExit(
                f"Invalid allowlist entry at {path}:{line_no}: unknown migrated contract(s): {', '.join(unknown)}"
            )
        if rel_path in entries:
            raise SystemExit(
                f"Invalid allowlist entry at {path}:{line_no}: duplicate path {rel_path}"
            )
        entries[rel_path] = set(modules)
    return entries


def find_migrated_imports(text: str) -> list[str]:
    imports: list[str] = []
    for match in IMPORT_RE.finditer(text):
        name = match.group("name")
        if name in MIGRATED_CONTRACTS:
            imports.append(name)
    return imports


def main() -> int:
    allowlist = parse_allowlist(ALLOWLIST_PATH)
    files = discover_scan_files()

    used_allowlist: dict[Path, set[str]] = defaultdict(set)
    errors: list[str] = []

    for file_path in files:
        rel = file_path.relative_to(ROOT)
        imports = set(find_migrated_imports(scrub_lean_code(file_path.read_text(encoding="utf-8"))))
        if not imports:
            continue

        allowed = allowlist.get(rel, set())
        disallowed = sorted(imports - allowed)
        if disallowed:
            rendered = ", ".join(f"Verity.Examples.{name}" for name in disallowed)
            errors.append(f"{rel}: unexpected legacy migrated-contract import(s): {rendered}")

        used_allowlist[rel].update(imports & allowed)

    for rel, allowed_modules in sorted(allowlist.items(), key=lambda kv: str(kv[0])):
        file_path = ROOT / rel
        if not file_path.exists():
            errors.append(f"{rel}: stale allowlist entry (file does not exist)")
            continue
        stale_modules = sorted(allowed_modules - used_allowlist.get(rel, set()))
        if stale_modules:
            rendered = ", ".join(f"Verity.Examples.{name}" for name in stale_modules)
            errors.append(
                f"{rel}: stale allowlist module(s) with no matching import(s): {rendered}"
            )

    if errors:
        print("Legacy migrated-contract import guard failed:", file=sys.stderr)
        for err in errors:
            print(f"- {err}", file=sys.stderr)
        print(
            "\nIssue #1143 guard: new imports of migrated legacy modules are blocked by default. "
            "Use scripts/legacy_example_import_allowlist.txt only for explicit, temporary exemptions.",
            file=sys.stderr,
        )
        return 1

    allowlist_count = sum(len(mods) for mods in allowlist.values())
    print(
        "Legacy migrated-contract import guard passed "
        f"({len(files)} Lean files scanned; {allowlist_count} explicit exemption module(s))."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
