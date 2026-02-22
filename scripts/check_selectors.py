#!/usr/bin/env python3
"""Verify selector hashing against ContractSpec, ASTSpecs, and IR/Yul artifacts.

Checks:
1) ContractSpec function signatures -> keccak selectors are unique per contract.
2) Compiler/Proofs/IRGeneration/Expr.lean compile selector lists match the spec.
3) Generated Yul files include all expected selector case labels.
4) ASTSpecs function signatures -> keccak selectors match for yul-ast output.
5) Cross-check: shared contracts have identical signatures in both spec sets.
6) No function name uses the reserved ``internal_`` prefix (Yul namespace collision).
7) Error(string) selector constant sync between ContractSpec and Interpreter.
8) Address mask constant sync between ContractSpec and Interpreter.
9) Selector shift constant sync between ContractSpec, Codegen, and Builtins.
10) Internal function prefix sync between ContractSpec and CI script.
11) Special entrypoint names sync between ContractSpec and CI script.
12) No duplicate function names per contract; compile function has the guard.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Iterator, List, Tuple

from keccak256 import selector as keccak_selector
from property_utils import ROOT, YUL_DIR, die, report_errors, strip_lean_comments
SPEC_FILE = ROOT / "Compiler" / "Specs.lean"
AST_SPEC_FILE = ROOT / "Compiler" / "ASTSpecs.lean"
IR_EXPR_FILE = ROOT / "Compiler" / "Proofs" / "IRGeneration" / "Expr.lean"
CONTRACT_SPEC_FILE = ROOT / "Compiler" / "ContractSpec.lean"
INTERPRETER_FILE = ROOT / "Compiler" / "Interpreter.lean"
CODEGEN_FILE = ROOT / "Compiler" / "Codegen.lean"
BUILTINS_FILE = ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Builtins.lean"
YUL_DIR_LEGACY = ("yul", YUL_DIR)
YUL_DIR_AST = ("yul-ast", ROOT / "compiler" / "yul-ast")

SIMPLE_PARAM_MAP = {
    "uint256": "uint256",
    "address": "address",
    "bool": "bool",
    "bytes32": "bytes32",
    "bytes": "bytes",
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


def extract_specs(text: str) -> List[SpecInfo]:
    specs: List[SpecInfo] = []
    spec_re = re.compile(r"def\s+(\w+)\s*:\s*ContractSpec\s*:=\s*\{")
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
    return specs


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
# Must match `isInteropEntrypointName` in ContractSpec.lean.
_SPECIAL_ENTRYPOINTS = {"fallback", "receive"}

# Reserved Yul name prefix for compiler-generated internal functions.
# Must match `internalFunctionPrefix` in ContractSpec.lean.
_INTERNAL_FUNCTION_PREFIX = "internal_"


def _is_internal_function(fn_block: str) -> bool:
    """Return True if the function block has isInternal := true."""
    return bool(re.search(r"isInternal\s*:=\s*true", fn_block))


def _iter_function_blocks(spec_block: str) -> Iterator[Tuple[str, str]]:
    """Yield (fn_name, fn_block) pairs from a functions := [...] block.

    Shared iteration logic for ContractSpec and ASTSpecs function extraction.
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
    """Extract external function signatures from a ContractSpec block.

    Skips internal functions and special entrypoints (fallback/receive)
    to match Selector.computeSelectors and ContractSpec.compile filtering.
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


def extract_ast_specs(text: str) -> List[SpecInfo]:
    """Extract specs from ASTSpecs.lean (ASTContractSpec definitions).

    ASTSpecs functions have no isInternal or special entrypoint semantics,
    so all functions are treated as external (matching ASTDriver.computeSelectors).
    """
    specs: List[SpecInfo] = []
    spec_re = re.compile(r"def\s+(\w+)\s*:\s*ASTContractSpec\s*:=\s*\{")
    for match in spec_re.finditer(text):
        def_name = match.group(1)
        block_start = match.end() - 1
        block_end = find_matching(text, block_start, "{", "}")
        if block_end == -1:
            die(f"Failed to parse AST spec block for {def_name}")
        block = text[block_start : block_end + 1]
        name_match = re.search(r"name\s*:=\s*\"([^\"]+)\"", block)
        if not name_match:
            die(f"Missing name for AST spec {def_name}")
        contract_name = name_match.group(1)
        signatures = extract_ast_functions(block)
        all_names = extract_all_function_names(block)
        specs.append(SpecInfo(def_name, contract_name, signatures, all_function_names=all_names))
    return specs


def extract_ast_functions(spec_block: str) -> List[str]:
    """Extract function signatures from an ASTContractSpec block.

    Unlike ContractSpec, ASTSpecs have no isInternal or fallback/receive
    semantics — all functions are external (matching ASTDriver.computeSelectors).
    """
    return [_build_signature(fn_block, fn_name)
            for fn_name, fn_block in _iter_function_blocks(spec_block)]


def check_ast_vs_legacy_signatures(
    legacy_specs: List[SpecInfo], ast_specs: List[SpecInfo]
) -> List[str]:
    """Cross-check that shared contracts have equivalent external signatures.

    ContractSpec's ``extract_functions`` filters out isInternal and
    fallback/receive.  AST's ``extract_ast_functions`` includes everything
    (ASTFunctionSpec doesn't model those concepts yet).  To compare like
    with like, we filter AST signatures through the same exclusion set
    before comparison.
    """
    errors: List[str] = []
    legacy_map = {spec.contract_name: spec for spec in legacy_specs}
    for ast_spec in ast_specs:
        legacy_spec = legacy_map.get(ast_spec.contract_name)
        if legacy_spec is None:
            continue  # AST-only contract, no cross-check needed
        # Filter AST signatures to match ContractSpec filtering (exclude
        # any functions whose name is in _SPECIAL_ENTRYPOINTS).  AST specs
        # don't have isInternal, so only entrypoint filtering applies.
        ast_external_sigs = [
            sig for sig, name in zip(ast_spec.signatures, ast_spec.all_function_names)
            if name not in _SPECIAL_ENTRYPOINTS
        ]
        if ast_external_sigs != legacy_spec.signatures:
            errors.append(
                f"{ast_spec.contract_name}: AST and ContractSpec signatures diverge: "
                f"AST={ast_external_sigs} vs ContractSpec={legacy_spec.signatures}"
            )
    return errors


def compute_selectors(signatures: Iterable[str]) -> List[int]:
    return [int(keccak_selector(sig), 16) for sig in signatures]


def extract_compile_selectors(text: str) -> List[CompileSelectors]:
    items: List[CompileSelectors] = []
    pattern = re.compile(r"compile\s+(\w+)Spec\s*\[([^\]]+)\]")
    for match in pattern.finditer(text):
        def_name = match.group(1) + "Spec"
        raw_list = match.group(2)
        selectors = [int(x, 16) for x in re.findall(r"0x[0-9a-fA-F]+", raw_list)]
        items.append(CompileSelectors(def_name, selectors))
    return items


def check_reserved_prefix_collisions(specs: List[SpecInfo]) -> List[str]:
    """Check that no function name (internal or external) starts with ``internal_``.

    The compiler prepends ``internal_`` to internal function names in generated
    Yul (see ``internalFunctionPrefix`` in ContractSpec.lean).  Any user-defined
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
    ``ContractSpec.compile``.
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
_INTERPRETER_RE = re.compile(
    r"def\s+revertSelectorWord\s*:\s*Nat\s*:=\s*\n?\s*(\d+)"
)


def check_error_selector_sync() -> List[str]:
    """Verify the Error(string) selector constant is consistent across files.

    Checks that:
    - ContractSpec.errorStringSelectorWord matches the expected value
    - Interpreter.revertSelectorWord (private copy) matches the canonical value
    """
    errors: List[str] = []

    if not CONTRACT_SPEC_FILE.exists():
        errors.append(f"Missing {CONTRACT_SPEC_FILE}")
        return errors

    spec_text = CONTRACT_SPEC_FILE.read_text(encoding="utf-8")
    m = _CANONICAL_RE.search(spec_text)
    if not m:
        errors.append(
            "ContractSpec.lean: missing errorStringSelectorWord definition"
        )
    else:
        canonical = int(m.group(1), 16) * (2**224)
        if canonical != _ERROR_STRING_SELECTOR_SHIFTED:
            errors.append(
                f"ContractSpec.errorStringSelectorWord: expected "
                f"0x{_ERROR_STRING_SELECTOR_SHIFTED:064x}, got 0x{canonical:064x}"
            )

    if INTERPRETER_FILE.exists():
        interp_text = INTERPRETER_FILE.read_text(encoding="utf-8")
        m2 = _INTERPRETER_RE.search(interp_text)
        if m2:
            interp_val = int(m2.group(1))
            if interp_val != _ERROR_STRING_SELECTOR_SHIFTED:
                errors.append(
                    f"Interpreter.revertSelectorWord: value {interp_val} does not "
                    f"match canonical errorStringSelectorWord "
                    f"({_ERROR_STRING_SELECTOR_SHIFTED})"
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
    """Verify the address mask/modulus constants are consistent across files.

    Checks that:
    - ContractSpec.addressMask exists (canonical definition)
    - Interpreter.addressModulus == 2^160 (matches addressMask + 1)
    """
    errors: List[str] = []

    if not CONTRACT_SPEC_FILE.exists():
        errors.append(f"Missing {CONTRACT_SPEC_FILE}")
        return errors

    spec_text = CONTRACT_SPEC_FILE.read_text(encoding="utf-8")
    if not _ADDRESS_MASK_RE.search(spec_text):
        errors.append(
            "ContractSpec.lean: missing addressMask definition "
            "(expected: def addressMask : Nat := (2 ^ 160) - 1)"
        )

    if INTERPRETER_FILE.exists():
        interp_text = INTERPRETER_FILE.read_text(encoding="utf-8")
        if not _ADDRESS_MODULUS_RE.search(interp_text):
            errors.append(
                "Interpreter.lean: missing or changed addressModulus definition "
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
    """Verify the selectorShift constant (224) is consistent across files.

    Checks that ContractSpec, Codegen, and Builtins all define selectorShift = 224.
    """
    errors: List[str] = []
    targets = [
        ("ContractSpec.lean", CONTRACT_SPEC_FILE),
        ("Codegen.lean", CODEGEN_FILE),
        ("Builtins.lean", BUILTINS_FILE),
    ]
    for label, path in targets:
        if not path.exists():
            errors.append(f"Missing {path}")
            continue
        text = path.read_text(encoding="utf-8")
        if not _SELECTOR_SHIFT_RE.search(text):
            errors.append(
                f"{label}: missing or changed selectorShift definition "
                f"(expected: def selectorShift : Nat := 224)"
            )
    return errors


# ---------------------------------------------------------------------------
# Internal function prefix sync
# ---------------------------------------------------------------------------

_INTERNAL_PREFIX_RE = re.compile(
    r'def\s+internalFunctionPrefix\s*:\s*String\s*:=\s*"([^"]*)"'
)


def check_internal_prefix_sync() -> List[str]:
    """Verify _INTERNAL_FUNCTION_PREFIX matches ContractSpec.internalFunctionPrefix."""
    errors: List[str] = []
    if not CONTRACT_SPEC_FILE.exists():
        errors.append(f"Missing {CONTRACT_SPEC_FILE}")
        return errors
    text = CONTRACT_SPEC_FILE.read_text(encoding="utf-8")
    m = _INTERNAL_PREFIX_RE.search(text)
    if not m:
        errors.append(
            "ContractSpec.lean: missing internalFunctionPrefix definition"
        )
    elif m.group(1) != _INTERNAL_FUNCTION_PREFIX:
        errors.append(
            f"ContractSpec.internalFunctionPrefix is {m.group(1)!r} "
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
    """Verify _SPECIAL_ENTRYPOINTS matches ContractSpec.isInteropEntrypointName."""
    errors: List[str] = []
    if not CONTRACT_SPEC_FILE.exists():
        errors.append(f"Missing {CONTRACT_SPEC_FILE}")
        return errors
    text = CONTRACT_SPEC_FILE.read_text(encoding="utf-8")
    m = _INTEROP_ENTRYPOINTS_RE.search(text)
    if not m:
        errors.append(
            "ContractSpec.lean: missing isInteropEntrypointName definition"
        )
        return errors
    # Parse the Lean list literal: ["fallback", "receive"]
    lean_names = set(
        n.strip().strip('"') for n in m.group(1).split(",") if n.strip()
    )
    if lean_names != _SPECIAL_ENTRYPOINTS:
        errors.append(
            f"ContractSpec.isInteropEntrypointName uses {sorted(lean_names)} "
            f"but check_selectors.py uses {sorted(_SPECIAL_ENTRYPOINTS)}"
        )
    return errors


def check_compile_duplicate_name_guard() -> List[str]:
    """Verify that ContractSpec.compile checks for duplicate function names.

    Ensures the compile function calls ``firstDuplicateName`` on
    ``spec.functions`` (not just on ``spec.errors``), preventing regression
    of the duplicate function name validation.
    """
    errors: List[str] = []
    if not CONTRACT_SPEC_FILE.exists():
        errors.append(f"Missing {CONTRACT_SPEC_FILE}")
        return errors
    text = CONTRACT_SPEC_FILE.read_text(encoding="utf-8")
    # Look for the duplicate function name check pattern inside compile
    if not re.search(
        r"firstDuplicateName\s*\(spec\.functions\.map", text
    ):
        errors.append(
            "ContractSpec.compile: missing duplicate function name check "
            "(expected firstDuplicateName (spec.functions.map ...))"
        )
    return errors


def main() -> None:
    if not SPEC_FILE.exists():
        die(f"Missing specs file: {SPEC_FILE}")
    if not IR_EXPR_FILE.exists():
        die(f"Missing IR proof file: {IR_EXPR_FILE}")

    _self_test_param_type_parser()

    specs_text = strip_lean_comments(SPEC_FILE.read_text(encoding="utf-8"))
    specs = extract_specs(specs_text)
    if not specs:
        die("No ContractSpec definitions found")

    compile_text = strip_lean_comments(IR_EXPR_FILE.read_text(encoding="utf-8"))
    compile_lists = extract_compile_selectors(compile_text)

    # Extract AST specs for yul-ast validation (if file exists).
    ast_specs: List[SpecInfo] = []
    if AST_SPEC_FILE.exists():
        ast_text = strip_lean_comments(AST_SPEC_FILE.read_text(encoding="utf-8"))
        ast_specs = extract_ast_specs(ast_text)

    errors: List[str] = []
    errors.extend(check_unique_selectors(specs))
    errors.extend(check_unique_function_names(specs))
    errors.extend(check_reserved_prefix_collisions(specs))
    errors.extend(check_compile_lists(specs, compile_lists))

    # Validate yul/ (legacy path) against ContractSpec specs.
    yul_label, yul_dir = YUL_DIR_LEGACY
    if yul_dir.exists():
        errors.extend(check_yul_selectors(specs, yul_label, yul_dir))

    # Validate yul-ast/ against AST specs (fall back to ContractSpec with warning).
    ast_label, ast_dir = YUL_DIR_AST
    if ast_dir.exists():
        if ast_specs:
            ast_check_specs = ast_specs
        else:
            print(
                "WARNING: ASTSpecs.lean missing/empty; validating yul-ast/ "
                "against ContractSpec specs instead",
                file=sys.stderr,
            )
            ast_check_specs = specs
        errors.extend(check_yul_selectors(ast_check_specs, ast_label, ast_dir))
        errors.extend(check_unique_selectors(ast_specs))
        errors.extend(check_unique_function_names(ast_specs))
        errors.extend(check_reserved_prefix_collisions(ast_specs))

    # Cross-check: shared contracts must have identical signatures.
    if ast_specs:
        errors.extend(check_ast_vs_legacy_signatures(specs, ast_specs))

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

    # Validate compile function has duplicate function name guard.
    errors.extend(check_compile_duplicate_name_guard())

    report_errors(errors, "Selector checks failed")
    print("Selector checks passed.")


if __name__ == "__main__":
    main()
