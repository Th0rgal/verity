#!/usr/bin/env python3
"""Verify selector hashing against CompilationModel, IR proofs, and Yul artifacts.

Checks:
1) CompilationModel function signatures -> keccak selectors are unique per contract.
2) Compiler/Proofs/IRGeneration/Expr.lean compile selector lists match the spec.
3) Generated Yul files include all expected selector case labels.
4) No function name uses the reserved ``internal_`` prefix (Yul namespace collision).
5) Error(string) selector constant sync between CompilationModel and Interpreter.
6) Address mask constant sync between CompilationModel and Interpreter.
7) Selector shift constant sync between CompilationModel, Codegen, and Builtins.
8) Internal function prefix sync between CompilationModel and CI script.
9) Special entrypoint names sync between CompilationModel and CI script.
10) No duplicate function names per contract; compile has all five duplicate-name guards.
11) Free memory pointer constant matches Solidity convention (0x40).
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Iterator, List, Tuple

import check_selector_fixtures
from keccak256 import selector as keccak_selector
from property_utils import ROOT, YUL_DIR, die, report_errors, strip_lean_comments
SPEC_FILES = (
    ROOT / "Contracts" / "Specs.lean",
    ROOT / "Contracts" / "SpecAliases.lean",
)
IR_EXPR_FILE = ROOT / "Compiler" / "Proofs" / "IRGeneration" / "Expr.lean"
CONTRACT_SPEC_FILE = ROOT / "Compiler" / "CompilationModel.lean"
CONSTANTS_FILE = ROOT / "Compiler" / "Constants.lean"
YUL_DIR_LEGACY = ("yul", YUL_DIR)

SIMPLE_PARAM_MAP = {
    "uint256": "uint256",
    "address": "address",
    "bool": "bool",
    "bytes32": "bytes32",
    "bytes": "bytes",
}
COMPILER_ALIAS_RE = re.compile(
    r"def\s+(\w+)\s*:\s*CompilationModel\s*:=\s*Contracts\.(\w+)\.spec"
)
COMPILER_FILTERED_ALIAS_RE = re.compile(
    r"def\s+(\w+)\s*:\s*CompilationModel\s*:=\s*"
    r"let\s+canonical\s*:=\s*Contracts\.(\w+)\.spec\s*"
    r"\{\s*canonical\s+with\s+functions\s*:=\s*canonical\.functions\.filter\s+fun\s+fn\s*=>\s*(.*?)\s*\}",
    re.DOTALL,
)
MACRO_FUNCTION_RE = re.compile(
    r"^\s*function\s+(\w+)\s*\((.*?)\)\s*:\s*([A-Za-z0-9_→ ]+)\s*:=\s*do",
    re.MULTILINE,
)
MACRO_TYPE_MAP = {
    "Uint256": "uint256",
    "Address": "address",
    "Bool": "bool",
    "Unit": "",
    "Bytes32": "bytes32",
}


@dataclass
class SpecInfo:
    def_name: str
    contract_name: str
    signatures: List[str]
    has_externals: bool = False
    all_function_names: List[str] = field(default_factory=list)


@dataclass
class CompileSelectors:
    def_name: str
    selectors: List[int]


def find_matching(text: str, start: int, open_ch: str, close_ch: str) -> int:
    depth = 0
    for idx in range(start, len(text)):
        ch = text[idx]
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return idx
    return -1


def _macro_contract_path(contract_name: str) -> Path:
    return ROOT / "Contracts" / contract_name / f"{contract_name}.lean"


def _macro_type_to_signature(ty: str) -> str:
    normalized = " ".join(ty.strip().split())
    if normalized in MACRO_TYPE_MAP:
        return MACRO_TYPE_MAP[normalized]
    die(f"Unsupported macro-contract type in selector extraction: {ty}")


def _split_macro_params(params: str) -> list[str]:
    if not params.strip():
        return []
    param_types: list[str] = []
    for part in params.split(","):
        chunk = part.strip()
        if not chunk:
            continue
        if ":" not in chunk:
            die(f"Malformed macro-contract parameter list: {params}")
        _name, ty = chunk.split(":", 1)
        param_types.append(_macro_type_to_signature(ty))
    return param_types


def _extract_macro_spec(def_name: str, contract_name: str) -> SpecInfo:
    path = _macro_contract_path(contract_name)
    if not path.exists():
        die(f"Missing macro contract source for alias spec {def_name}: {path}")

    content = strip_lean_comments(path.read_text(encoding="utf-8"))
    signatures: List[str] = []
    all_names: List[str] = []
    for fn_name, params, _ret in MACRO_FUNCTION_RE.findall(content):
        all_names.append(fn_name)
        signatures.append(f"{fn_name}({','.join(_split_macro_params(params))})")
    return SpecInfo(def_name, contract_name, signatures, False, all_names)


def _extract_filtered_macro_spec(
    def_name: str, contract_name: str, filter_body: str
) -> SpecInfo:
    allowed_names = re.findall(r'fn\.name\s*=\s*"([^"]+)"', filter_body)
    if not allowed_names:
        die(f"Unsupported filtered macro spec form for {def_name}")

    canonical = _extract_macro_spec(def_name, contract_name)
    allowed = set(allowed_names)
    filtered_signatures = [
        sig
        for sig in canonical.signatures
        if sig.split("(", 1)[0] in allowed
    ]
    filtered_names = [name for name in canonical.all_function_names if name in allowed]
    return SpecInfo(
        def_name,
        contract_name,
        filtered_signatures,
        canonical.has_externals,
        filtered_names,
    )


def extract_specs(text: str) -> List[SpecInfo]:
    specs: List[SpecInfo] = []
    seen_def_names: set[str] = set()
    spec_re = re.compile(r"def\s+(\w+)\s*:\s*CompilationModel\s*:=\s*\{")
    for match in spec_re.finditer(text):
        def_name = match.group(1)
        block_start = match.end() - 1
        block_end = find_matching(text, block_start, "{", "}")
        if block_end == -1:
            die(f"Failed to parse spec block for {def_name}")
        block = text[block_start : block_end + 1]
        name_match = re.search(r"name\s*:=\s*\"([^\"]+)\"", block)
        if not name_match:
            die(f"Missing name for spec {def_name}")
        contract_name = name_match.group(1)
        signatures = extract_functions(block)
        has_externals = has_nonempty_externals(block)
        all_names = extract_all_function_names(block)
        specs.append(SpecInfo(def_name, contract_name, signatures, has_externals, all_names))
        seen_def_names.add(def_name)

    for def_name, contract_name in COMPILER_ALIAS_RE.findall(text):
        if def_name in seen_def_names:
            continue
        specs.append(_extract_macro_spec(def_name, contract_name))
        seen_def_names.add(def_name)

    for def_name, contract_name, filter_body in COMPILER_FILTERED_ALIAS_RE.findall(text):
        if def_name in seen_def_names:
            continue
        specs.append(_extract_filtered_macro_spec(def_name, contract_name, filter_body))
        seen_def_names.add(def_name)
    return specs


def load_specs_text() -> str:
    missing = [path for path in SPEC_FILES if not path.exists()]
    if missing:
        joined = ", ".join(str(path) for path in missing)
        die(f"Missing specs file(s): {joined}")
    return "\n".join(
        strip_lean_comments(path.read_text(encoding="utf-8")) for path in SPEC_FILES
    )


def has_nonempty_externals(spec_block: str) -> bool:
    """Return True only when a spec has a non-empty externals list."""
    ext_match = re.search(r"externals\s*:=\s*\[", spec_block)
    if not ext_match:
        return False
    list_start = ext_match.end() - 1
    list_end = find_matching(spec_block, list_start, "[", "]")
    if list_end == -1:
        die("Failed to parse externals list")
    return bool(spec_block[list_start + 1 : list_end].strip())


# Special entrypoint names that are NOT dispatched by selector.
# Must match `isInteropEntrypointName` in CompilationModel.lean.
_SPECIAL_ENTRYPOINTS = {"fallback", "receive"}

# Reserved Yul name prefix for compiler-generated internal functions.
# Must match `internalFunctionPrefix` in CompilationModel.lean.
_INTERNAL_FUNCTION_PREFIX = "internal_"


def _is_internal_function(fn_block: str) -> bool:
    """Return True if the function block has isInternal := true."""
    return bool(re.search(r"isInternal\s*:=\s*true", fn_block))


def _iter_function_blocks(spec_block: str) -> Iterator[Tuple[str, str]]:
    """Yield (fn_name, fn_block) pairs from a functions := [...] block.

    Shared iteration logic for function extraction from spec blocks.
    Callers apply their own filtering and result-building.
    """
    fn_match = re.search(r"functions\s*:=\s*\[", spec_block)
    if not fn_match:
        return
    list_start = fn_match.end() - 1
    list_end = find_matching(spec_block, list_start, "[", "]")
    if list_end == -1:
        die("Failed to parse functions list")
    functions_block = spec_block[list_start : list_end + 1]
    idx = 0
    while idx < len(functions_block):
        if functions_block[idx] == "{":
            end = find_matching(functions_block, idx, "{", "}")
            if end == -1:
                die("Failed to parse function block")
            fn_block = functions_block[idx : end + 1]
            name_match = re.search(r"name\s*:=\s*\"([^\"]+)\"", fn_block)
            if not name_match:
                die("Function block missing name")
            yield name_match.group(1), fn_block
            idx = end + 1
        else:
            idx += 1


def _build_signature(fn_block: str, fn_name: str) -> str:
    """Build a Solidity-style function signature from a parsed function block."""
    params = extract_param_types(fn_block)
    return f"{fn_name}({','.join(params)})"


def extract_functions(spec_block: str) -> List[str]:
    """Extract external function signatures from a CompilationModel block.

    Skips internal functions and special entrypoints (fallback/receive)
    to match Selector.computeSelectors and CompilationModel.compile filtering.
    """
    sigs: List[str] = []
    for fn_name, fn_block in _iter_function_blocks(spec_block):
        if _is_internal_function(fn_block) or fn_name in _SPECIAL_ENTRYPOINTS:
            continue
        sigs.append(_build_signature(fn_block, fn_name))
    return sigs


def extract_all_function_names(spec_block: str) -> List[str]:
    """Extract ALL function names from a spec block (including internal/special)."""
    return [fn_name for fn_name, _ in _iter_function_blocks(spec_block)]


def _skip_ws(text: str, pos: int) -> int:
    while pos < len(text) and text[pos].isspace():
        pos += 1
    return pos


def _read_ident(text: str, pos: int) -> tuple[str, int]:
    start = pos
    while pos < len(text) and (text[pos].isalnum() or text[pos] == "_"):
        pos += 1
    return text[start:pos], pos


def _parse_param_type_expr(text: str, pos: int) -> tuple[str, int]:
    pos = _skip_ws(text, pos)
    if pos >= len(text):
        die("Unexpected end of ParamType expression")

    if text[pos] == "(":
        parsed, pos = _parse_param_type_expr(text, pos + 1)
        pos = _skip_ws(text, pos)
        if pos >= len(text) or text[pos] != ")":
            die("Unclosed parenthesized ParamType expression")
        return parsed, pos + 1

    if not text.startswith("ParamType.", pos):
        die(f"Expected ParamType.* near: {text[pos:pos+32]!r}")
    pos += len("ParamType.")
    variant, pos = _read_ident(text, pos)
    if not variant:
        die("Missing ParamType variant name")

    simple = SIMPLE_PARAM_MAP.get(variant)
    if simple is not None:
        return simple, pos

    if variant == "array":
        elem_type, pos = _parse_param_type_expr(text, pos)
        return f"{elem_type}[]", pos

    if variant == "fixedArray":
        elem_type, pos = _parse_param_type_expr(text, pos)
        pos = _skip_ws(text, pos)
        size_start = pos
        while pos < len(text) and text[pos].isdigit():
            pos += 1
        if size_start == pos:
            die("fixedArray missing size")
        size = text[size_start:pos]
        return f"{elem_type}[{size}]", pos

    if variant == "tuple":
        pos = _skip_ws(text, pos)
        if pos >= len(text) or text[pos] != "[":
            die("tuple missing element list")
        pos += 1
        elems: List[str] = []
        while True:
            pos = _skip_ws(text, pos)
            if pos < len(text) and text[pos] == "]":
                pos += 1
                break
            elem, pos = _parse_param_type_expr(text, pos)
            elems.append(elem)
            pos = _skip_ws(text, pos)
            if pos < len(text) and text[pos] == ",":
                pos += 1
                continue
            if pos < len(text) and text[pos] == "]":
                pos += 1
                break
            die("tuple elements must be comma-separated")
        return f"({','.join(elems)})", pos

    die(f"Unsupported ParamType.{variant}")
    return "", pos  # unreachable


def parse_param_type(text: str) -> str:
    parsed, pos = _parse_param_type_expr(text, 0)
    pos = _skip_ws(text, pos)
    if pos != len(text):
        die(f"Unexpected trailing ParamType tokens: {text[pos:]!r}")
    return parsed


def _self_test_param_type_parser() -> None:
    cases = {
        "ParamType.uint256": "uint256",
        "ParamType.bool": "bool",
        "ParamType.array ParamType.address": "address[]",
        "ParamType.fixedArray (ParamType.array ParamType.uint256) 3": "uint256[][3]",
        "ParamType.tuple [ParamType.uint256, ParamType.address, ParamType.bool]": "(uint256,address,bool)",
        "ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.address])": "(uint256,address)[]",
    }
    for src, expected in cases.items():
        got = parse_param_type(src)
        if got != expected:
            die(f"ParamType parser self-test failed: {src!r} -> {got!r} (expected {expected!r})")


def extract_param_types(fn_block: str) -> List[str]:
    params_match = re.search(r"params\s*:=\s*\[", fn_block)
    if not params_match:
        return []
    list_start = params_match.end() - 1
    list_end = find_matching(fn_block, list_start, "[", "]")
    if list_end == -1:
        die("Failed to parse params list")
    params_block = fn_block[list_start : list_end + 1]

    # Extract each { ... } param block and parse its ty field
    sol_types: List[str] = []
    idx = 0
    while idx < len(params_block):
        if params_block[idx] == "{":
            end = find_matching(params_block, idx, "{", "}")
            if end == -1:
                die("Failed to parse param block")
            param_block = params_block[idx : end + 1]
            ty_match = re.search(r"ty\s*:=\s*(.*?)(?:\s*\}|\s*,\s*\w)", param_block, re.DOTALL)
            if ty_match:
                ty_text = ty_match.group(1).strip().rstrip(",").rstrip("}")
                if ty_text:
                    sol_types.append(parse_param_type(ty_text))
            idx = end + 1
        else:
            idx += 1
    return sol_types


def compute_selectors(signatures: Iterable[str]) -> List[int]:
    return [int(keccak_selector(sig), 16) for sig in signatures]


def extract_compile_selectors(text: str) -> List[CompileSelectors]:
    items: List[CompileSelectors] = []
    # Allow empty selector tables (`compile fooSpec []`) as valid Lean syntax.
    pattern = re.compile(r"compile\s+(\w+)Spec\s*\[([^\]]*)\]")
    for match in pattern.finditer(text):
        def_name = match.group(1) + "Spec"
        raw_list = match.group(2)
        selectors = [int(x, 16) for x in re.findall(r"0x[0-9a-fA-F]+", raw_list)]
        items.append(CompileSelectors(def_name, selectors))
    return items


def check_reserved_prefix_collisions(specs: List[SpecInfo]) -> List[str]:
    """Check that no function name (internal or external) starts with ``internal_``.

    The compiler prepends ``internal_`` to internal function names in generated
    Yul (see ``internalFunctionPrefix`` in CompilationModel.lean).  Any user-defined
    function whose name starts with this prefix — regardless of whether it is
    marked ``isInternal`` — would create confusing or colliding Yul identifiers.
    """
    errors: List[str] = []
    for spec in specs:
        for name in spec.all_function_names:
            if name.startswith(_INTERNAL_FUNCTION_PREFIX):
                errors.append(
                    f"{spec.contract_name}: function '{name}' uses reserved "
                    f"prefix '{_INTERNAL_FUNCTION_PREFIX}' (collides with "
                    f"compiler-generated internal function names)"
                )
    return errors


def check_unique_function_names(specs: List[SpecInfo]) -> List[str]:
    """Check that no contract has duplicate function names.

    Mirrors the ``firstDuplicateName (spec.functions.map (·.name))`` check in
    ``CompilationModel.compile``.
    """
    errors: List[str] = []
    for spec in specs:
        seen: set[str] = set()
        for name in spec.all_function_names:
            if name in seen:
                errors.append(
                    f"{spec.contract_name}: duplicate function name '{name}'"
                )
            seen.add(name)
    return errors


def check_unique_selectors(specs: List[SpecInfo]) -> List[str]:
    errors: List[str] = []
    for spec in specs:
        selectors = compute_selectors(spec.signatures)
        if len(set(selectors)) != len(selectors):
            errors.append(f"{spec.contract_name}: duplicate selectors detected")
    return errors


def check_compile_lists(specs: List[SpecInfo], compile_lists: List[CompileSelectors]) -> List[str]:
    errors: List[str] = []
    spec_map = {spec.def_name: spec for spec in specs}
    seen_specs: set[str] = set()
    for item in compile_lists:
        spec = spec_map.get(item.def_name)
        if spec is None:
            errors.append(f"Compile list references unknown spec {item.def_name}")
            continue
        seen_specs.add(item.def_name)
        expected = compute_selectors(spec.signatures)
        if expected != item.selectors:
            errors.append(
                f"{spec.contract_name}: compile selector list mismatch: expected {format_selectors(expected)} "
                f"got {format_selectors(item.selectors)}"
            )
    for spec in specs:
        # Specs compiled only via --link do not need compile selector tables.
        if spec.has_externals:
            continue
        if spec.def_name not in seen_specs:
            errors.append(f"{spec.contract_name}: missing compile selector list for {spec.def_name}")
    return errors


def check_yul_selectors(specs: List[SpecInfo], yul_label: str, yul_dir: Path) -> List[str]:
    errors: List[str] = []
    for spec in specs:
        yul_path = yul_dir / f"{spec.contract_name}.yul"
        if not yul_path.exists():
            # Specs with external dependencies are only compiled with --link
            if spec.has_externals:
                continue
            errors.append(f"Missing {yul_label} output for {spec.contract_name}: {yul_path}")
            continue
        yul_text = yul_path.read_text(encoding="utf-8")
        selectors = compute_selectors(spec.signatures)
        for sig, sel in zip(spec.signatures, selectors):
            needle = f"case 0x{sel:08x}"
            if needle not in yul_text:
                errors.append(f"{spec.contract_name} ({yul_label}): selector {needle} missing for {sig}")
    return errors


def format_selectors(selectors: List[int]) -> str:
    return "[" + ", ".join(f"0x{sel:08x}" for sel in selectors) + "]"


# ---------------------------------------------------------------------------
# Error(string) selector constant sync
# ---------------------------------------------------------------------------

# Canonical value: keccak256("Error(string)")[0:4] left-shifted to 32-byte word.
_ERROR_STRING_SELECTOR_SHIFTED: int = 0x08c379a0 * (2**224)

_CANONICAL_RE = re.compile(
    r"def\s+errorStringSelectorWord\s*:\s*Nat\s*:=\s*(0x[0-9a-fA-F]+)\s*\*\s*\(2\s*\^\s*224\)"
)


def check_error_selector_sync() -> List[str]:
    """Verify the Error(string) selector constant is consistent.

    Checks that Constants.errorStringSelectorWord matches the expected value.
    (The canonical definition now lives in Compiler/Constants.lean.)
    """
    errors: List[str] = []

    if not CONSTANTS_FILE.exists():
        errors.append(f"Missing {CONSTANTS_FILE}")
        return errors

    constants_text = CONSTANTS_FILE.read_text(encoding="utf-8")
    m = _CANONICAL_RE.search(constants_text)
    if not m:
        errors.append(
            "Constants.lean: missing errorStringSelectorWord definition"
        )
    else:
        canonical = int(m.group(1), 16) * (2**224)
        if canonical != _ERROR_STRING_SELECTOR_SHIFTED:
            errors.append(
                f"Constants.errorStringSelectorWord: expected "
                f"0x{_ERROR_STRING_SELECTOR_SHIFTED:064x}, got 0x{canonical:064x}"
            )

    return errors


# ---------------------------------------------------------------------------
# Address mask constant sync
# ---------------------------------------------------------------------------

_ADDRESS_MASK: int = (2**160) - 1

_ADDRESS_MASK_RE = re.compile(
    r"def\s+addressMask\s*:\s*Nat\s*:=\s*\(2\s*\^\s*160\)\s*-\s*1"
)
_ADDRESS_MODULUS_RE = re.compile(
    r"def\s+addressModulus\s*:\s*Nat\s*:=\s*\n?\s*2\s*\^\s*160"
)


def check_address_mask_sync() -> List[str]:
    """Verify the address mask/modulus constants exist in Constants.lean.

    Checks that Constants.addressMask and Constants.addressModulus exist.
    (The canonical definitions now live in Compiler/Constants.lean.)
    """
    errors: List[str] = []

    if not CONSTANTS_FILE.exists():
        errors.append(f"Missing {CONSTANTS_FILE}")
        return errors

    constants_text = CONSTANTS_FILE.read_text(encoding="utf-8")
    if not _ADDRESS_MASK_RE.search(constants_text):
        errors.append(
            "Constants.lean: missing addressMask definition "
            "(expected: def addressMask : Nat := (2 ^ 160) - 1)"
        )
    if not _ADDRESS_MODULUS_RE.search(constants_text):
        errors.append(
            "Constants.lean: missing addressModulus definition "
            "(expected: def addressModulus : Nat := 2 ^ 160)"
        )

    return errors


# ---------------------------------------------------------------------------
# Selector shift constant sync
# ---------------------------------------------------------------------------

_SELECTOR_SHIFT_RE = re.compile(
    r"def\s+selectorShift\s*:\s*Nat\s*:=\s*224"
)


def check_selector_shift_sync() -> List[str]:
    """Verify the selectorShift constant (224) exists in Constants.lean.

    The canonical definition now lives in Compiler/Constants.lean;
    CompilationModel, Codegen, and Builtins import it from there.
    """
    errors: List[str] = []
    if not CONSTANTS_FILE.exists():
        errors.append(f"Missing {CONSTANTS_FILE}")
        return errors
    text = CONSTANTS_FILE.read_text(encoding="utf-8")
    if not _SELECTOR_SHIFT_RE.search(text):
        errors.append(
            "Constants.lean: missing or changed selectorShift definition "
            "(expected: def selectorShift : Nat := 224)"
        )
    return errors


# ---------------------------------------------------------------------------
# Internal function prefix sync
# ---------------------------------------------------------------------------

_INTERNAL_PREFIX_RE = re.compile(
    r'def\s+internalFunctionPrefix\s*:\s*String\s*:=\s*"([^"]*)"'
)


def check_internal_prefix_sync() -> List[str]:
    """Verify _INTERNAL_FUNCTION_PREFIX matches CompilationModel.internalFunctionPrefix."""
    errors: List[str] = []
    if not CONTRACT_SPEC_FILE.exists():
        errors.append(f"Missing {CONTRACT_SPEC_FILE}")
        return errors
    text = CONTRACT_SPEC_FILE.read_text(encoding="utf-8")
    m = _INTERNAL_PREFIX_RE.search(text)
    if not m:
        errors.append(
            "CompilationModel.lean: missing internalFunctionPrefix definition"
        )
    elif m.group(1) != _INTERNAL_FUNCTION_PREFIX:
        errors.append(
            f"CompilationModel.internalFunctionPrefix is {m.group(1)!r} "
            f"but check_selectors.py uses {_INTERNAL_FUNCTION_PREFIX!r}"
        )
    return errors


# ---------------------------------------------------------------------------
# Special entrypoint names sync
# ---------------------------------------------------------------------------

_INTEROP_ENTRYPOINTS_RE = re.compile(
    r'def\s+isInteropEntrypointName\b.*?:=\s*\[([^\]]*)\]',
    re.DOTALL,
)


def check_special_entrypoints_sync() -> List[str]:
    """Verify _SPECIAL_ENTRYPOINTS matches CompilationModel.isInteropEntrypointName."""
    errors: List[str] = []
    if not CONTRACT_SPEC_FILE.exists():
        errors.append(f"Missing {CONTRACT_SPEC_FILE}")
        return errors
    text = CONTRACT_SPEC_FILE.read_text(encoding="utf-8")
    m = _INTEROP_ENTRYPOINTS_RE.search(text)
    if not m:
        errors.append(
            "CompilationModel.lean: missing isInteropEntrypointName definition"
        )
        return errors
    # Parse the Lean list literal: ["fallback", "receive"]
    lean_names = set(
        n.strip().strip('"') for n in m.group(1).split(",") if n.strip()
    )
    if lean_names != _SPECIAL_ENTRYPOINTS:
        errors.append(
            f"CompilationModel.isInteropEntrypointName uses {sorted(lean_names)} "
            f"but check_selectors.py uses {sorted(_SPECIAL_ENTRYPOINTS)}"
        )
    return errors


def check_free_memory_pointer_sync() -> List[str]:
    """Verify freeMemoryPointer matches the Solidity convention (0x40)."""
    errors: List[str] = []
    if not CONSTANTS_FILE.exists():
        errors.append(f"Missing {CONSTANTS_FILE}")
        return errors
    text = CONSTANTS_FILE.read_text(encoding="utf-8")
    m = re.search(r"def\s+freeMemoryPointer\s*:\s*Nat\s*:=\s*(0x[0-9a-fA-F]+|\d+)", text)
    if not m:
        errors.append(
            "Constants.lean: missing freeMemoryPointer definition"
        )
    else:
        val = int(m.group(1), 0)
        if val != 0x40:
            errors.append(
                f"Constants.freeMemoryPointer: expected 0x40 (64), got {val}"
            )
    return errors


def check_compile_duplicate_name_guard() -> List[str]:
    """Verify that CompilationModel.compile checks for duplicate names across all spec lists.

    Ensures the compile function calls ``firstDuplicateName`` on all five
    spec collections: functions, errors, fields, events, and externals.
    """
    errors: List[str] = []
    if not CONTRACT_SPEC_FILE.exists():
        errors.append(f"Missing {CONTRACT_SPEC_FILE}")
        return errors
    text = CONTRACT_SPEC_FILE.read_text(encoding="utf-8")
    for collection in ("functions", "errors", "fields", "events", "externals"):
        if not re.search(
            rf"firstDuplicateName\s*\(spec\.{collection}\.map", text
        ):
            errors.append(
                f"CompilationModel.compile: missing duplicate {collection} name check "
                f"(expected firstDuplicateName (spec.{collection}.map ...))"
            )
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check-fixtures",
        action="store_true",
        help="Also validate selector hashing against the Solidity fixture via solc.",
    )
    args = parser.parse_args(argv)

    if not IR_EXPR_FILE.exists():
        die(f"Missing IR proof file: {IR_EXPR_FILE}")

    _self_test_param_type_parser()

    specs = extract_specs(load_specs_text())
    if not specs:
        die("No CompilationModel definitions found")

    compile_text = strip_lean_comments(IR_EXPR_FILE.read_text(encoding="utf-8"))
    compile_lists = extract_compile_selectors(compile_text)

    errors: List[str] = []
    errors.extend(check_unique_selectors(specs))
    errors.extend(check_unique_function_names(specs))
    errors.extend(check_reserved_prefix_collisions(specs))
    errors.extend(check_compile_lists(specs, compile_lists))

    # Validate yul/ (legacy path) against CompilationModel specs.
    yul_label, yul_dir = YUL_DIR_LEGACY
    if yul_dir.exists():
        errors.extend(check_yul_selectors(specs, yul_label, yul_dir))

    # Validate Error(string) selector constant consistency.
    errors.extend(check_error_selector_sync())

    # Validate address mask constant consistency.
    errors.extend(check_address_mask_sync())

    # Validate selector shift constant consistency.
    errors.extend(check_selector_shift_sync())

    # Validate internal function prefix consistency.
    errors.extend(check_internal_prefix_sync())

    # Validate special entrypoint names consistency.
    errors.extend(check_special_entrypoints_sync())

    # Validate free memory pointer matches Solidity convention.
    errors.extend(check_free_memory_pointer_sync())

    # Validate compile function has all five duplicate-name guards.
    errors.extend(check_compile_duplicate_name_guard())

    report_errors(errors, "Selector checks failed")
    if args.check_fixtures:
        fixture_rc = check_selector_fixtures.main()
        if fixture_rc != 0:
            return fixture_rc
    print("Selector checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
