#!/usr/bin/env python3
"""Ensure Linker.yulBuiltins and ContractSpec.interopBuiltinCallNames stay in sync.

Both lists enumerate EVM/Yul opcodes. yulBuiltins is the Linker allowlist for
linked library validation; interopBuiltinCallNames is the ContractSpec denylist
for user-function body validation. They must agree on the opcode universe, with
known exceptions documented below.

Expected differences:
  - yulBuiltins includes low-level call opcodes (call, staticcall, delegatecall,
    callcode) that ContractSpec tracks separately in `isLowLevelCallName`.
  - yulBuiltins includes Yul-object builtins (datasize, dataoffset, datacopy)
    that are not EVM opcodes and not relevant to interop validation.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LINKER = ROOT / "Compiler" / "Linker.lean"
CONTRACT_SPEC = ROOT / "Compiler" / "ContractSpec.lean"

# Items in yulBuiltins but intentionally absent from interopBuiltinCallNames
# AND isLowLevelCallName. These are Yul-object builtins, not EVM opcodes.
EXPECTED_LINKER_ONLY = {
    "datasize", "dataoffset", "datacopy",
}


def extract_string_list(text: str, name: str) -> set[str]:
    """Extract a Lean string list definition by name."""
    # Match: (private )?(def|abbrev) <name> ... := \n  [...]
    pattern = rf'(?:private\s+)?def\s+{re.escape(name)}\b[^:]*:\s*List\s+String\s*:=\s*\n((?:\s*\[.*?\](?:\s*\+\+\s*\[.*?\])*)+)'
    # Simpler: just find all quoted strings after the definition start
    # First find the definition
    def_pattern = rf'(?:private\s+)?def\s+{re.escape(name)}\b'
    m = re.search(def_pattern, text)
    if not m:
        print(f"  Could not find definition of '{name}'", file=sys.stderr)
        return set()

    # From the definition start, collect all quoted strings until next definition or end
    rest = text[m.start():]
    # Find end: next `private def`, `def`, `end`, or blank line after content
    lines = rest.split('\n')
    strings: set[str] = set()
    started = False
    for line in lines:
        if '"' in line:
            started = True
            strings.update(re.findall(r'"([^"]+)"', line))
        elif started and line.strip() and not line.strip().startswith('--'):
            # Non-empty line without strings after we started = end of list
            break
    return strings


def extract_low_level_calls(text: str) -> set[str]:
    """Extract the isLowLevelCallName string list (single-line definition)."""
    m = re.search(r'def\s+isLowLevelCallName[^\n]*\n\s*\[([^\]]+)\]', text)
    if not m:
        return set()
    return set(re.findall(r'"([^"]+)"', m.group(1)))


def main() -> int:
    errors: list[str] = []

    if not LINKER.exists():
        errors.append(f"Missing: {LINKER.relative_to(ROOT)}")
        print("\n".join(errors), file=sys.stderr)
        return 1

    if not CONTRACT_SPEC.exists():
        errors.append(f"Missing: {CONTRACT_SPEC.relative_to(ROOT)}")
        print("\n".join(errors), file=sys.stderr)
        return 1

    linker_text = LINKER.read_text(encoding="utf-8")
    spec_text = CONTRACT_SPEC.read_text(encoding="utf-8")

    yul_builtins = extract_string_list(linker_text, "yulBuiltins")
    interop_builtins = extract_string_list(spec_text, "interopBuiltinCallNames")
    low_level_calls = extract_low_level_calls(spec_text)

    if not yul_builtins:
        errors.append("Failed to extract yulBuiltins from Linker.lean")
    if not interop_builtins:
        errors.append("Failed to extract interopBuiltinCallNames from ContractSpec.lean")

    if errors:
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    # ContractSpec's full opcode set = interopBuiltinCallNames ∪ isLowLevelCallName
    spec_full = interop_builtins | low_level_calls

    # yulBuiltins without the expected Linker-only entries should equal spec_full
    linker_comparable = yul_builtins - EXPECTED_LINKER_ONLY

    in_linker_not_spec = linker_comparable - spec_full
    in_spec_not_linker = spec_full - linker_comparable

    if in_linker_not_spec:
        sorted_names = sorted(in_linker_not_spec)
        errors.append(
            f"In Linker.yulBuiltins but not in ContractSpec "
            f"(interopBuiltinCallNames ∪ isLowLevelCallName): {sorted_names}"
        )
    if in_spec_not_linker:
        sorted_names = sorted(in_spec_not_linker)
        errors.append(
            f"In ContractSpec (interopBuiltinCallNames ∪ isLowLevelCallName) "
            f"but not in Linker.yulBuiltins: {sorted_names}"
        )

    if errors:
        print("Builtin list sync check failed:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        print(
            "\nKeep Linker.yulBuiltins and ContractSpec.interopBuiltinCallNames "
            "in sync. See scripts/check_builtin_list_sync.py for expected differences.",
            file=sys.stderr,
        )
        return 1

    print(f"✓ Builtin lists in sync ({len(yul_builtins)} Linker, "
          f"{len(interop_builtins)}+{len(low_level_calls)} ContractSpec)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
