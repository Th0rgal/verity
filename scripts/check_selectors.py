#!/usr/bin/env python3
"""Verify selector hashing against ContractSpec, ASTSpecs, and IR/Yul artifacts.

Checks:
1) ContractSpec function signatures -> keccak selectors are unique per contract.
2) Compiler/Proofs/IRGeneration/Expr.lean compile selector lists match the spec.
3) Generated Yul files include all expected selector case labels.
4) ASTSpecs function signatures -> keccak selectors match for yul-ast output.
5) Cross-check: shared contracts have identical signatures in both spec sets.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List

from keccak256 import selector as keccak_selector
from property_utils import ROOT, YUL_DIR, die, report_errors, strip_lean_comments
SPEC_FILE = ROOT / "Compiler" / "Specs.lean"
AST_SPEC_FILE = ROOT / "Compiler" / "ASTSpecs.lean"
IR_EXPR_FILE = ROOT / "Compiler" / "Proofs" / "IRGeneration" / "Expr.lean"
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
        specs.append(SpecInfo(def_name, contract_name, signatures, has_externals))
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


def _is_internal_function(fn_block: str) -> bool:
    """Return True if the function block has isInternal := true."""
    return bool(re.search(r"isInternal\s*:=\s*true", fn_block))


def extract_functions(spec_block: str) -> List[str]:
    fn_match = re.search(r"functions\s*:=\s*\[", spec_block)
    if not fn_match:
        return []
    list_start = fn_match.end() - 1
    list_end = find_matching(spec_block, list_start, "[", "]")
    if list_end == -1:
        die("Failed to parse functions list")
    functions_block = spec_block[list_start : list_end + 1]
    sigs: List[str] = []
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
            fn_name = name_match.group(1)
            # Skip internal functions and special entrypoints (fallback/receive)
            # to match Selector.computeSelectors and ContractSpec.compile filtering.
            if _is_internal_function(fn_block) or fn_name in _SPECIAL_ENTRYPOINTS:
                idx = end + 1
                continue
            params = extract_param_types(fn_block)
            sigs.append(f"{fn_name}({','.join(params)})")
            idx = end + 1
        else:
            idx += 1
    return sigs


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
        specs.append(SpecInfo(def_name, contract_name, signatures))
    return specs


def extract_ast_functions(spec_block: str) -> List[str]:
    """Extract function signatures from an ASTContractSpec block.

    Unlike ContractSpec, ASTSpecs have no isInternal or fallback/receive
    semantics — all functions are external.
    """
    fn_match = re.search(r"functions\s*:=\s*\[", spec_block)
    if not fn_match:
        return []
    list_start = fn_match.end() - 1
    list_end = find_matching(spec_block, list_start, "[", "]")
    if list_end == -1:
        die("Failed to parse AST functions list")
    functions_block = spec_block[list_start : list_end + 1]
    sigs: List[str] = []
    idx = 0
    while idx < len(functions_block):
        if functions_block[idx] == "{":
            end = find_matching(functions_block, idx, "{", "}")
            if end == -1:
                die("Failed to parse AST function block")
            fn_block = functions_block[idx : end + 1]
            name_match = re.search(r"name\s*:=\s*\"([^\"]+)\"", fn_block)
            if not name_match:
                die("AST function block missing name")
            fn_name = name_match.group(1)
            params = extract_param_types(fn_block)
            sigs.append(f"{fn_name}({','.join(params)})")
            idx = end + 1
        else:
            idx += 1
    return sigs


def check_ast_vs_legacy_signatures(
    legacy_specs: List[SpecInfo], ast_specs: List[SpecInfo]
) -> List[str]:
    """Cross-check that shared contracts have identical signatures."""
    errors: List[str] = []
    legacy_map = {spec.contract_name: spec for spec in legacy_specs}
    for ast_spec in ast_specs:
        legacy_spec = legacy_map.get(ast_spec.contract_name)
        if legacy_spec is None:
            continue  # AST-only contract, no cross-check needed
        if ast_spec.signatures != legacy_spec.signatures:
            errors.append(
                f"{ast_spec.contract_name}: AST and ContractSpec signatures diverge: "
                f"AST={ast_spec.signatures} vs ContractSpec={legacy_spec.signatures}"
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
    errors.extend(check_compile_lists(specs, compile_lists))

    # Validate yul/ (legacy path) against ContractSpec specs.
    yul_label, yul_dir = YUL_DIR_LEGACY
    if yul_dir.exists():
        errors.extend(check_yul_selectors(specs, yul_label, yul_dir))

    # Validate yul-ast/ against AST specs (or fall back to ContractSpec).
    ast_label, ast_dir = YUL_DIR_AST
    if ast_dir.exists():
        ast_check_specs = ast_specs if ast_specs else specs
        errors.extend(check_yul_selectors(ast_check_specs, ast_label, ast_dir))
        errors.extend(check_unique_selectors(ast_specs))

    # Cross-check: shared contracts must have identical signatures.
    if ast_specs:
        errors.extend(check_ast_vs_legacy_signatures(specs, ast_specs))

    report_errors(errors, "Selector checks failed")
    print("Selector checks passed.")


if __name__ == "__main__":
    main()
