#!/usr/bin/env python3
"""Ensure runtime interpreters use centralized Yul builtin semantics.

Issue #294 tracks replacing hand-rolled Yul semantics with EVMYulLean. This
guard keeps builtin-call dispatch centralized in one module so that migration is
a backend swap instead of duplicated edits.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOFS_DIR = ROOT / "Compiler" / "Proofs"
BUILTINS_FILE = PROOFS_DIR / "YulGeneration" / "Builtins.lean"

RUNTIME_INTERPRETERS = [
    PROOFS_DIR / "IRGeneration" / "IRInterpreter.lean",
    PROOFS_DIR / "YulGeneration" / "Semantics.lean",
]

IMPORT_BUILTINS_RE = re.compile(r"^\s*import\s+Compiler\.Proofs\.YulGeneration\.Builtins\s*$", re.MULTILINE)
BUILTIN_CALL_RE = re.compile(r"Compiler\.Proofs\.YulGeneration\.evalBuiltinCall")
INLINE_DISPATCH_RE = re.compile(
    r'func\s*=\s*"(?:mappingSlot|sload|add|sub|mul|div|mod|lt|gt|eq|iszero|and|or|xor|not|shl|shr|caller|calldataload)"'
)


def main() -> int:
    errors: list[str] = []

    if not BUILTINS_FILE.exists():
        errors.append(f"{BUILTINS_FILE.relative_to(ROOT)}: missing builtin boundary module")

    for lean_file in RUNTIME_INTERPRETERS:
        text = lean_file.read_text(encoding="utf-8")
        rel = lean_file.relative_to(ROOT)

        if not IMPORT_BUILTINS_RE.search(text):
            errors.append(f"{rel}: missing import Compiler.Proofs.YulGeneration.Builtins")

        if not BUILTIN_CALL_RE.search(text):
            errors.append(f"{rel}: missing call to Compiler.Proofs.YulGeneration.evalBuiltinCall")

        if INLINE_DISPATCH_RE.search(text):
            errors.append(
                f"{rel}: inline builtin dispatch detected; move builtin semantics to "
                "Compiler/Proofs/YulGeneration/Builtins.lean"
            )

    if errors:
        print("Yul builtin boundary check failed:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    print("✓ Yul builtin boundary is enforced")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
