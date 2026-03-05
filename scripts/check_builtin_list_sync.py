#!/usr/bin/env python3
"""Ensure Linker.yulBuiltins and CompilationModel.interopBuiltinCallNames stay in sync.

Both lists enumerate EVM/Yul opcodes. yulBuiltins is the Linker allowlist for
linked library validation; interopBuiltinCallNames is the CompilationModel denylist
for user-function body validation. They must agree on the opcode universe, with
known exceptions documented below.

Expected differences:
  - yulBuiltins includes low-level call opcodes (call, staticcall, delegatecall,
    callcode) that CompilationModel tracks separately in `isLowLevelCallName`.
  - yulBuiltins includes Yul-object builtins (datasize, dataoffset, datacopy)
    that are not EVM opcodes and not relevant to interop validation.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import strip_lean_comments

ROOT = Path(__file__).resolve().parents[1]
LINKER = ROOT / "Compiler" / "Linker.lean"
CONTRACT_SPEC = ROOT / "Compiler" / "CompilationModel.lean"

# Items in yulBuiltins but intentionally absent from interopBuiltinCallNames
# AND isLowLevelCallName. These are Yul-object builtins, not EVM opcodes.
EXPECTED_LINKER_ONLY = {
    "datasize", "dataoffset", "datacopy",
}


def extract_string_list(text: str, name: str) -> set[str]:
    """Extract string literals from a Lean `def ... :=` body by name.

    Source is stripped of Lean comments first so comment-only decoys like
    `-- def <name>` cannot satisfy extraction.
    """
    cleaned = strip_lean_comments(text)
    body = extract_def_body(cleaned, name)
    if body is None:
        print(f"  Could not find definition of '{name}'", file=sys.stderr)
        return set()
    list_expr = extract_list_expression(body)
    if list_expr is None:
        print(f"  Could not parse list body for '{name}'", file=sys.stderr)
        return set()
    return set(re.findall(r'"([^"]+)"', list_expr))


def extract_def_body(text: str, name: str) -> str | None:
    """Extract a `def <name> ... :=` body until the next `def` header.

    Assumes comments have already been stripped.
    """
    header_re = re.compile(
        rf"^[ \t]*(?:private[ \t]+)?def[ \t]+{re.escape(name)}\b[^\n]*:=[ \t]*(.*)$",
        re.MULTILINE,
    )
    m = header_re.search(text)
    if not m:
        return None

    lines = text[m.start() :].splitlines()
    lines[0] = m.group(1)
    body_lines: list[str] = []
    list_depth = 0
    saw_list = False
    in_string = False
    escaped = False
    next_def_re = re.compile(r"^[ \t]*(?:private[ \t]+)?def[ \t]+\w+\b")

    for idx, line in enumerate(lines):
        if idx > 0 and list_depth == 0 and saw_list and next_def_re.match(line):
            break
        body_lines.append(line)
        for ch in line:
            if in_string:
                if escaped:
                    escaped = False
                    continue
                if ch == "\\":
                    escaped = True
                    continue
                if ch == '"':
                    in_string = False
                continue
            if ch == '"':
                in_string = True
                continue
            if ch == "[":
                list_depth += 1
                saw_list = True
            elif ch == "]":
                list_depth = max(list_depth - 1, 0)

    body = "\n".join(body_lines)
    return body if saw_list else None


def extract_low_level_calls(text: str) -> set[str]:
    """Extract string literals from isLowLevelCallName list expression."""
    cleaned = strip_lean_comments(text)
    body = extract_def_body(cleaned, "isLowLevelCallName")
    if body is None:
        return set()
    list_expr = extract_list_expression(body)
    if list_expr is None:
        return set()
    return set(re.findall(r'"([^"]+)"', list_expr))


def extract_list_expression(body: str) -> str | None:
    """Extract `[ ... ]` (optionally chained by `++ [ ... ]`) from a def body."""
    i = 0
    n = len(body)

    def skip_ws(pos: int) -> int:
        while pos < n and body[pos].isspace():
            pos += 1
        return pos

    def parse_list(start: int) -> int | None:
        if start >= n or body[start] != "[":
            return None
        depth = 0
        in_string = False
        escaped = False
        pos = start
        while pos < n:
            ch = body[pos]
            if in_string:
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == '"':
                    in_string = False
                pos += 1
                continue
            if ch == '"':
                in_string = True
                pos += 1
                continue
            if ch == "[":
                depth += 1
            elif ch == "]":
                depth -= 1
                if depth == 0:
                    return pos + 1
            pos += 1
        return None

    i = skip_ws(i)
    start = i
    end = parse_list(i)
    if end is None:
        return None
    i = end
    while True:
        i = skip_ws(i)
        if i + 1 < n and body[i] == "+" and body[i + 1] == "+":
            i += 2
            i = skip_ws(i)
            next_end = parse_list(i)
            if next_end is None:
                return None
            i = next_end
            end = i
            continue
        end = i
        break
    return body[start:end]


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
    selector_interop_helpers = ROOT / "Compiler" / "CompilationModel" / "SelectorInteropHelpers.lean"
    helper_text = (
        selector_interop_helpers.read_text(encoding="utf-8")
        if selector_interop_helpers.exists()
        else ""
    )

    yul_builtins = extract_string_list(linker_text, "yulBuiltins")
    interop_builtins = extract_string_list(helper_text, "interopBuiltinCallNames")
    low_level_calls = extract_low_level_calls(helper_text)

    # Backward compatibility for older layouts where these defs were in
    # CompilationModel.lean directly.
    if not interop_builtins:
        interop_builtins = extract_string_list(spec_text, "interopBuiltinCallNames")
    if not low_level_calls:
        low_level_calls = extract_low_level_calls(spec_text)

    if not yul_builtins:
        errors.append("Failed to extract yulBuiltins from Linker.lean")
    if not interop_builtins:
        errors.append(
            "Failed to extract interopBuiltinCallNames from "
            "SelectorInteropHelpers.lean or CompilationModel.lean"
        )

    if errors:
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    # CompilationModel's full opcode set = interopBuiltinCallNames ∪ isLowLevelCallName
    spec_full = interop_builtins | low_level_calls

    # yulBuiltins without the expected Linker-only entries should equal spec_full
    linker_comparable = yul_builtins - EXPECTED_LINKER_ONLY

    in_linker_not_spec = linker_comparable - spec_full
    in_spec_not_linker = spec_full - linker_comparable

    if in_linker_not_spec:
        sorted_names = sorted(in_linker_not_spec)
        errors.append(
            f"In Linker.yulBuiltins but not in CompilationModel "
            f"(interopBuiltinCallNames ∪ isLowLevelCallName): {sorted_names}"
        )
    if in_spec_not_linker:
        sorted_names = sorted(in_spec_not_linker)
        errors.append(
            f"In CompilationModel (interopBuiltinCallNames ∪ isLowLevelCallName) "
            f"but not in Linker.yulBuiltins: {sorted_names}"
        )

    if errors:
        print("Builtin list sync check failed:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        print(
            "\nKeep Linker.yulBuiltins and CompilationModel.interopBuiltinCallNames "
            "in sync. See scripts/check_builtin_list_sync.py for expected differences.",
            file=sys.stderr,
        )
        return 1

    print(f"✓ Builtin lists in sync ({len(yul_builtins)} Linker, "
          f"{len(interop_builtins)}+{len(low_level_calls)} CompilationModel)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
