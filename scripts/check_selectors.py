#!/usr/bin/env python3
"""Verify selector hashing against ContractSpec and IR/Yul artifacts.

Checks:
1) ContractSpec function signatures -> keccak selectors are unique per contract.
2) Compiler/Proofs/IRGeneration/Expr.lean compile selector lists match the spec.
3) Generated Yul files include all expected selector case labels.
"""

from __future__ import annotations

import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List

from property_utils import die

ROOT = Path(__file__).resolve().parent.parent
SPEC_FILE = ROOT / "Compiler" / "Specs.lean"
IR_EXPR_FILE = ROOT / "Compiler" / "Proofs" / "IRGeneration" / "Expr.lean"
YUL_DIRS = [
    ("yul", ROOT / "compiler" / "yul"),
]
KECCAK = ROOT / "scripts" / "keccak256.py"

SIMPLE_PARAM_MAP = {
    "uint256": "uint256",
    "address": "address",
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
        has_externals = bool(re.search(r"externals\s*:=\s*\[", block))
        specs.append(SpecInfo(def_name, contract_name, signatures, has_externals))
    return specs


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
            params = extract_param_types(fn_block)
            sigs.append(f"{fn_name}({','.join(params)})")
            idx = end + 1
        else:
            idx += 1
    return sigs


def _parse_param_type(tokens: List[str], pos: int) -> tuple[str, int]:
    """Parse a ParamType expression from a token list, returning (solidity_type, next_pos).

    Handles recursive types like ``ParamType.array ParamType.uint256`` → ``uint256[]``
    and ``ParamType.fixedArray ParamType.address 3`` → ``address[3]``.
    Parenthesized sub-expressions are handled by stripping parens first.
    """
    if pos >= len(tokens):
        die("Unexpected end of ParamType tokens")
    tok = tokens[pos]
    if not tok.startswith("ParamType."):
        die(f"Expected ParamType.*, got '{tok}'")
    variant = tok[len("ParamType."):]

    sol = SIMPLE_PARAM_MAP.get(variant)
    if sol is not None:
        return sol, pos + 1

    if variant == "array":
        elem_type, next_pos = _parse_param_type(tokens, pos + 1)
        return f"{elem_type}[]", next_pos

    if variant == "fixedArray":
        elem_type, next_pos = _parse_param_type(tokens, pos + 1)
        if next_pos >= len(tokens):
            die("fixedArray missing size")
        size = tokens[next_pos]
        return f"{elem_type}[{size}]", next_pos + 1

    die(f"Unsupported ParamType.{variant}")
    return "", pos  # unreachable


def _tokenize_param_types(text: str) -> List[str]:
    """Tokenize a Lean type expression, stripping parentheses.

    Splits on whitespace and removes bare ``(`` and ``)`` tokens, as well as
    stripping them from token edges.  This lets us handle both
    ``ParamType.array ParamType.uint256`` and
    ``ParamType.array (ParamType.array ParamType.uint256)``.
    """
    raw = text.split()
    tokens: List[str] = []
    for r in raw:
        # Strip leading/trailing parens
        r = r.strip("()")
        if not r:
            continue
        tokens.append(r)
    return tokens


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
                tokens = _tokenize_param_types(ty_text)
                if tokens:
                    sol_type, _ = _parse_param_type(tokens, 0)
                    sol_types.append(sol_type)
            idx = end + 1
        else:
            idx += 1
    return sol_types


def compute_selectors(signatures: Iterable[str]) -> List[int]:
    sigs = list(signatures)
    if not sigs:
        return []
    result = subprocess.run(
        ["python3", str(KECCAK), *sigs],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        die(f"keccak256.py failed: {result.stderr.strip()}")
    selectors: List[int] = []
    for line in result.stdout.strip().splitlines():
        line = line.strip()
        if not line:
            continue
        selectors.append(int(line, 16))
    if len(selectors) != len(sigs):
        die(f"keccak256.py returned {len(selectors)} selectors for {len(sigs)} signatures")
    return selectors


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
    for item in compile_lists:
        spec = spec_map.get(item.def_name)
        if spec is None:
            errors.append(f"Compile list references unknown spec {item.def_name}")
            continue
        expected = compute_selectors(spec.signatures)
        if expected != item.selectors:
            errors.append(
                f"{spec.contract_name}: compile selector list mismatch: expected {format_selectors(expected)} "
                f"got {format_selectors(item.selectors)}"
            )
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


def main() -> int:
    if not SPEC_FILE.exists():
        die(f"Missing specs file: {SPEC_FILE}")
    if not IR_EXPR_FILE.exists():
        die(f"Missing IR proof file: {IR_EXPR_FILE}")
    if not KECCAK.exists():
        die(f"Missing keccak script: {KECCAK}")

    specs_text = SPEC_FILE.read_text(encoding="utf-8")
    specs = extract_specs(specs_text)
    if not specs:
        die("No ContractSpec definitions found")

    compile_text = IR_EXPR_FILE.read_text(encoding="utf-8")
    compile_lists = extract_compile_selectors(compile_text)

    errors: List[str] = []
    errors.extend(check_unique_selectors(specs))
    errors.extend(check_compile_lists(specs, compile_lists))
    for label, yul_dir in YUL_DIRS:
        if yul_dir.exists():
            errors.extend(check_yul_selectors(specs, label, yul_dir))

    if errors:
        for err in errors:
            print(f"error: {err}", file=sys.stderr)
        return 1

    print("Selector checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
