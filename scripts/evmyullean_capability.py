"""Shared EVMYulLean capability boundary definitions for CI checks/artifacts."""

from __future__ import annotations

import re
from pathlib import Path

from property_utils import ROOT

BUILTINS_FILE = ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Builtins.lean"

BUILTIN_NAME_RE = re.compile(r'func\s*=\s*"([^"]+)"')
FUNC_COMPARE_RE = re.compile(r"\bfunc\s*=\s*(.+?)\s+then\b")
STRING_LITERAL_RE = re.compile(r'^"([^"]+)"$')
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
LET_BINDING_RE = re.compile(
    r"^\s*let\s+([A-Za-z_][A-Za-z0-9_']*)(?:\s*:\s*[^:=]+)?\s*:=\s*(.+?)\s*$"
)


def _strip_outer_parens(text: str) -> str:
    """Strip one level of balanced outer parentheses from an expression."""
    text = text.strip()
    if len(text) >= 2 and text[0] == "(" and text[-1] == ")":
        depth = 0
        for idx, ch in enumerate(text):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and idx != len(text) - 1:
                    return text
        if depth == 0:
            return text[1:-1].strip()
    return text

# Builtins currently modeled as part of the overlap subset for planned
# EVMYulLean-backed semantics.
EVMYULLEAN_OVERLAP_BUILTINS = {
    "add",
    "and",
    "address",
    "calldataload",
    "calldatasize",
    "caller",
    "callvalue",
    "chainid",
    "div",
    "eq",
    "gt",
    "iszero",
    "lt",
    "mod",
    "mul",
    "number",
    "not",
    "or",
    "shl",
    "shr",
    "sload",
    "sub",
    "timestamp",
    "xor",
}

# Verity-level helper kept outside upstream Yul builtin set.
VERITY_HELPER_BUILTINS = {"mappingSlot"}

# Explicitly unsupported in the planned EVMYulLean-backed path (per #294
# research notes). Presence here in Builtins.lean should block CI.
EVMYULLEAN_UNSUPPORTED_BUILTINS = {
    "create",
    "create2",
    "extcodecopy",
    "extcodehash",
    "extcodesize",
}


def extract_found_builtins(builtins_file: Path = BUILTINS_FILE) -> set[str]:
    """Extract builtin names from Builtins.lean."""
    found, _diagnostics = extract_found_builtins_with_diagnostics(builtins_file)
    return found


def _strip_lean_line_comment(line: str) -> str:
    """Remove Lean single-line comments to avoid comment-decoy parsing."""
    return line.split("--", 1)[0]


def extract_found_builtins_with_diagnostics(
    builtins_file: Path = BUILTINS_FILE,
) -> tuple[set[str], list[str]]:
    """Extract builtins and report non-literal dispatch patterns.

    Fail-closed diagnostics are produced when `func = ... then` uses an
    unresolved/non-literal RHS in `evalBuiltinCall`.
    """
    text = builtins_file.read_text(encoding="utf-8")
    lines = text.splitlines()

    found: set[str] = set()
    diagnostics: list[str] = []
    aliases: dict[str, str] = {}

    in_eval_builtin = False
    eval_indent = 0

    for line_no, raw_line in enumerate(lines, start=1):
        line = _strip_lean_line_comment(raw_line)

        if not in_eval_builtin:
            if line.lstrip().startswith("def evalBuiltinCall"):
                in_eval_builtin = True
                eval_indent = len(line) - len(line.lstrip())
            continue

        stripped = line.strip()
        if stripped:
            indent = len(line) - len(line.lstrip())
            if indent <= eval_indent and not stripped.startswith("|"):
                break

        let_match = LET_BINDING_RE.match(line)
        if let_match:
            alias_name = let_match.group(1)
            rhs_expr = _strip_outer_parens(let_match.group(2))
            literal_match = STRING_LITERAL_RE.match(rhs_expr)
            if literal_match:
                aliases[alias_name] = literal_match.group(1)
            elif IDENT_RE.match(rhs_expr):
                resolved = aliases.get(rhs_expr)
                if resolved is not None:
                    aliases[alias_name] = resolved

        compare_match = FUNC_COMPARE_RE.search(line)
        if not compare_match:
            continue

        rhs = compare_match.group(1).strip()
        literal_match = STRING_LITERAL_RE.match(rhs)
        if literal_match:
            found.add(literal_match.group(1))
            continue

        if IDENT_RE.match(rhs):
            resolved = aliases.get(rhs)
            if resolved is not None:
                found.add(resolved)
            else:
                diagnostics.append(
                    f"line {line_no}: unresolved non-literal dispatch `func = {rhs}`"
                )
            continue

        diagnostics.append(
            f"line {line_no}: unsupported non-literal dispatch `func = {rhs}`"
        )

    # Backward-compatible fallback in case evalBuiltinCall was not detected.
    if not found and not diagnostics:
        found = set(BUILTIN_NAME_RE.findall(text))

    return found, diagnostics
