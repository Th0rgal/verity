#!/usr/bin/env python3
"""Generate Foundry property-test stubs from `verity_contract` declarations.

This script scans Lean sources for macro contracts declared with `verity_contract` and emits
baseline Foundry suites (`Property<Contract>.t.sol`) with one test per function.

Goals:
- Keep generation deterministic and fail-closed on missing contracts.
- Provide immediately runnable stubs for mutating functions.
- Emit explicit TODO assertions for getter/non-Unit functions.
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass, field
from pathlib import Path

from property_utils import ROOT

CONTRACT_RE = re.compile(r"^\s*verity_contract\s+([A-Za-z_][A-Za-z0-9_]*)\s+where\s*$")
FUNCTION_RE = re.compile(
    r"^\s*function\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(([^)]*)\)\s*:\s*(.+?)\s*:=\s*",
)
CONSTRUCTOR_RE = re.compile(r"^\s*constructor\s*\(([^)]*)\)\s*:=\s*")
PARAM_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+?)\s*$")
STORAGE_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+?)\s*:=\s*slot\s+([0-9]+)\s*$",
)
VALUE_BINDING_RE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+?)\s*:=\s*(.+?)\s*$",
)
STORAGE_READ_RE = re.compile(
    r"let\s+([A-Za-z_][A-Za-z0-9_]*)\s*←\s*(getStorage|getStorageAddr)\s+([A-Za-z_][A-Za-z0-9_]*)$"
)
STORAGE_ARRAY_LENGTH_RE = re.compile(
    r"let\s+([A-Za-z_][A-Za-z0-9_]*)\s*←\s*getStorageArrayLength\s+([A-Za-z_][A-Za-z0-9_]*)$"
)
STORAGE_ARRAY_ELEMENT_RE = re.compile(
    r"let\s+([A-Za-z_][A-Za-z0-9_]*)\s*←\s*getStorageArrayElement\s+"
    r"([A-Za-z_][A-Za-z0-9_]*)\s+([0-9]+)$"
)
MAPPING_READ_RE = re.compile(
    r"let\s+([A-Za-z_][A-Za-z0-9_]*)\s*←\s*"
    r"(getMapping|getMappingUint|getMappingAddr|getMappingUintAddr)\s+"
    r"([A-Za-z_][A-Za-z0-9_]*)\s+([A-Za-z_][A-Za-z0-9_]*)$"
)
MAPPING2_READ_RE = re.compile(
    r"let\s+([A-Za-z_][A-Za-z0-9_]*)\s*←\s*getMapping2\s+"
    r"([A-Za-z_][A-Za-z0-9_]*)\s+([A-Za-z_][A-Za-z0-9_]*)\s+([A-Za-z_][A-Za-z0-9_]*)$"
)
MAPPING_WORD_READ_RE = re.compile(
    r"let\s+([A-Za-z_][A-Za-z0-9_]*)\s*←\s*getMappingWord\s+"
    r"([A-Za-z_][A-Za-z0-9_]*)\s+([A-Za-z_][A-Za-z0-9_]*)\s+([0-9]+)$"
)
MAPPING_N_READ_RE = re.compile(
    r"let\s+([A-Za-z_][A-Za-z0-9_]*)\s*←\s*getMappingN\s+"
    r"([A-Za-z_][A-Za-z0-9_]*)\s+\[(.+)\]$"
)
STRUCT_MEMBER_READ_RE = re.compile(
    r'let\s+([A-Za-z_][A-Za-z0-9_]*)\s*←\s*structMember\s+"([^"]+)"\s+'
    r'([A-Za-z_][A-Za-z0-9_]*)\s+"([^"]+)"$'
)
STRUCT_MEMBER2_READ_RE = re.compile(
    r'let\s+([A-Za-z_][A-Za-z0-9_]*)\s*←\s*structMember2\s+"([^"]+)"\s+'
    r'([A-Za-z_][A-Za-z0-9_]*)\s+([A-Za-z_][A-Za-z0-9_]*)\s+"([^"]+)"$'
)
NON_ZERO_REQUIRE_RE = re.compile(
    r'require\s+\(([A-Za-z_][A-Za-z0-9_]*)\s*!=\s*0\)\s+"[^"]+"$'
)
BUILTIN_READ_RE = re.compile(
    r"let\s+([A-Za-z_][A-Za-z0-9_]*)\s*←\s*(msgSender|msgValue)$"
)
PARAM_COMPARE_RETURN_RE = re.compile(
    r"return\s+\(?([A-Za-z_][A-Za-z0-9_]*)\s*(==|!=)\s*([A-Za-z_][A-Za-z0-9_]*)\)?$"
)
PARAM_COMPARE_BRANCH_RE = re.compile(
    r"if\s+([A-Za-z_][A-Za-z0-9_]*)\s*(==|!=)\s*([A-Za-z_][A-Za-z0-9_]*)\s+then$"
)


@dataclass(frozen=True)
class ParamDecl:
    name: str
    lean_type: str


@dataclass(frozen=True)
class FunctionDecl:
    name: str
    params: tuple[ParamDecl, ...]
    return_type: str
    body: tuple[str, ...] = ()


@dataclass(frozen=True)
class ConstructorDecl:
    params: tuple[ParamDecl, ...]


@dataclass(frozen=True)
class ValueDecl:
    name: str
    lean_type: str
    expr: str


@dataclass(frozen=True)
class ContractDecl:
    name: str
    constructor: ConstructorDecl | None
    functions: tuple[FunctionDecl, ...]
    storage_slots: dict[str, int]
    source: Path
    storage_types: dict[str, str] = field(default_factory=dict)
    constants: dict[str, ValueDecl] = field(default_factory=dict)
    immutables: dict[str, ValueDecl] = field(default_factory=dict)


@dataclass(frozen=True)
class ReadAccessor:
    var_name: str
    accessor: str
    storage_name: str
    key_names: tuple[str, ...]
    word_offset: int = 0
    array_index: int | None = None
    member_name: str | None = None


@dataclass(frozen=True)
class StructMemberLayout:
    word_offset: int
    packed_offset: int | None = None
    packed_width: int | None = None


def _normalize_type(type_src: str) -> str:
    return " ".join(type_src.strip().split())


def _split_params(params_src: str) -> tuple[ParamDecl, ...]:
    if not params_src.strip():
        return ()
    # Split on commas respecting bracket nesting (for Tuple [...] types)
    depth = 0
    parts: list[str] = []
    current: list[str] = []
    for ch in params_src:
        if ch == "[":
            depth += 1
            current.append(ch)
        elif ch == "]":
            depth -= 1
            current.append(ch)
        elif ch == "," and depth == 0:
            parts.append("".join(current).strip())
            current = []
        else:
            current.append(ch)
    remaining = "".join(current).strip()
    if remaining:
        parts.append(remaining)
    out: list[ParamDecl] = []
    for part in parts:
        if not part:
            continue
        m = PARAM_RE.match(part)
        if not m:
            raise ValueError(f"invalid parameter declaration: {part!r}")
        out.append(ParamDecl(name=m.group(1), lean_type=_normalize_type(m.group(2))))
    return tuple(out)


def parse_contracts(text: str, source: Path) -> dict[str, ContractDecl]:
    contracts: dict[str, ContractDecl] = {}
    current_name: str | None = None
    current_constructor: ConstructorDecl | None = None
    current_storage_slots: dict[str, int] = {}
    current_storage_types: dict[str, str] = {}
    current_constants: dict[str, ValueDecl] = {}
    current_immutables: dict[str, ValueDecl] = {}
    current_functions: list[FunctionDecl] = []
    current_function: FunctionDecl | None = None
    current_body: list[str] = []
    guard_pending = False
    in_storage_block = False
    in_constants_block = False
    in_immutables_block = False
    pending_storage_lines: list[str] = []

    def flush_function() -> None:
        nonlocal current_function, current_body
        if current_function is None:
            return
        current_functions.append(
            FunctionDecl(
                name=current_function.name,
                params=current_function.params,
                return_type=current_function.return_type,
                body=tuple(current_body),
            )
        )
        current_function = None
        current_body = []

    def flush_current() -> None:
        nonlocal current_name, current_constructor, current_storage_slots, current_storage_types, current_constants, current_immutables, current_functions, in_storage_block, in_constants_block, in_immutables_block, pending_storage_lines
        if current_name is None:
            return
        flush_function()
        contracts[current_name] = ContractDecl(
            name=current_name,
            constructor=current_constructor,
            functions=tuple(current_functions),
            storage_slots=dict(current_storage_slots),
            source=source,
            storage_types=dict(current_storage_types),
            constants=dict(current_constants),
            immutables=dict(current_immutables),
        )
        current_name = None
        current_constructor = None
        current_storage_slots = {}
        current_storage_types = {}
        current_constants = {}
        current_immutables = {}
        current_functions = []
        in_storage_block = False
        in_constants_block = False
        in_immutables_block = False
        pending_storage_lines = []

    for line in text.splitlines():
        if line.strip() == "#guard_msgs in":
            flush_current()
            guard_pending = True
            continue
        cm = CONTRACT_RE.match(line)
        if cm:
            if guard_pending:
                guard_pending = False
                continue
            flush_current()
            current_name = cm.group(1)
            continue

        if current_name is None:
            continue

        if current_function is not None and line.strip() and not line.startswith("    "):
            flush_function()

        if line.strip() == "storage":
            in_storage_block = True
            in_constants_block = False
            in_immutables_block = False
            pending_storage_lines = []
            continue

        if line.strip() == "constants":
            in_storage_block = False
            in_constants_block = True
            in_immutables_block = False
            pending_storage_lines = []
            continue

        if line.strip() == "immutables":
            in_storage_block = False
            in_constants_block = False
            in_immutables_block = True
            pending_storage_lines = []
            continue

        ctor = CONSTRUCTOR_RE.match(line)
        if ctor:
            flush_function()
            if current_constructor is not None:
                raise ValueError(f"duplicate constructor in contract '{current_name}'")
            current_constructor = ConstructorDecl(params=_split_params(ctor.group(1)))
            in_storage_block = False
            in_constants_block = False
            in_immutables_block = False
            continue

        fm = FUNCTION_RE.match(line)
        if fm:
            flush_function()
            fn_name = fm.group(1)
            params_src = fm.group(2)
            ret_ty = _normalize_type(fm.group(3))
            current_function = FunctionDecl(
                name=fn_name,
                params=_split_params(params_src),
                return_type=ret_ty,
            )
            in_storage_block = False
            in_constants_block = False
            in_immutables_block = False
            continue

        if in_storage_block:
            stripped = line.strip()
            sm = STORAGE_RE.match(stripped)
            if sm:
                current_storage_slots[sm.group(1)] = int(sm.group(3))
                current_storage_types[sm.group(1)] = _normalize_type(sm.group(2))
                pending_storage_lines = []
                continue
            if pending_storage_lines:
                pending_storage_lines.append(stripped)
                sm = STORAGE_RE.match(" ".join(pending_storage_lines))
                if sm:
                    current_storage_slots[sm.group(1)] = int(sm.group(3))
                    current_storage_types[sm.group(1)] = _normalize_type(sm.group(2))
                    pending_storage_lines = []
                continue
            if stripped:
                pending_storage_lines = [stripped]
                continue

        if in_constants_block:
            vm = VALUE_BINDING_RE.match(line)
            if vm:
                current_constants[vm.group(1)] = ValueDecl(
                    name=vm.group(1),
                    lean_type=_normalize_type(vm.group(2)),
                    expr=vm.group(3).strip(),
                )
                continue
            if line.strip():
                in_constants_block = False

        if in_immutables_block:
            vm = VALUE_BINDING_RE.match(line)
            if vm:
                current_immutables[vm.group(1)] = ValueDecl(
                    name=vm.group(1),
                    lean_type=_normalize_type(vm.group(2)),
                    expr=vm.group(3).strip(),
                )
                continue
            if line.strip():
                in_immutables_block = False

        if current_function is not None and line.startswith("    "):
            stripped = line.strip()
            if stripped:
                current_body.append(stripped)

    flush_current()
    return contracts


def discover_macro_contract_sources(macro_dir: Path) -> list[Path]:
    """Return all Lean macro-contract sources under `macro_dir` recursively."""
    return sorted(macro_dir.rglob("*.lean"))


def collect_contracts(paths: list[Path]) -> dict[str, ContractDecl]:
    all_contracts: dict[str, ContractDecl] = {}
    for path in paths:
        text = path.read_text(encoding="utf-8")
        parsed = parse_contracts(text, path)
        for name, contract in parsed.items():
            if name in all_contracts:
                prev = all_contracts[name].source
                raise ValueError(f"duplicate contract '{name}' in {prev} and {contract.source}")
            all_contracts[name] = contract
    return all_contracts


def _parse_tuple_elements(inner: str) -> list[str]:
    """Parse the comma-separated element list inside Tuple [ ... ]."""
    depth = 0
    parts: list[str] = []
    current: list[str] = []
    for ch in inner:
        if ch in "([":
            depth += 1
            current.append(ch)
        elif ch in ")]":
            depth -= 1
            current.append(ch)
        elif ch == "," and depth == 0:
            parts.append("".join(current).strip())
            current = []
        else:
            current.append(ch)
    remaining = "".join(current).strip()
    if remaining:
        parts.append(remaining)
    return parts


def _sol_type(lean_ty: str) -> str:
    ty = _normalize_type(lean_ty)
    if ty == "Uint256":
        return "uint256"
    if ty == "Int256":
        return "int256"
    if ty == "Uint8":
        return "uint8"
    if ty == "Address":
        return "address"
    if ty == "Bool":
        return "bool"
    if ty == "Bytes32":
        return "bytes32"
    if ty == "Bytes":
        return "bytes"
    if ty == "String":
        return "string"
    if ty.startswith("Array "):
        elem = ty[len("Array ") :].strip()
        return f"{_sol_type(elem)}[]"
    if ty.startswith("Tuple [") and ty.endswith("]"):
        inner = ty[len("Tuple [") : -1]
        elems = _parse_tuple_elements(inner)
        sol_elems = ",".join(_sol_type(e) for e in elems)
        return f"({sol_elems})"
    raise ValueError(f"unsupported Lean type for Solidity signature mapping: {ty!r}")


def _sol_tuple_value_type(lean_ty: str) -> str:
    ty = _normalize_type(lean_ty)
    if ty.startswith("Tuple [") and ty.endswith("]"):
        inner = ty[len("Tuple [") : -1]
        elems = _parse_tuple_elements(inner)
        sol_elems = ", ".join(_sol_type(e) for e in elems)
        return f"({sol_elems})"
    raise ValueError(f"unsupported Lean tuple type for Solidity tuple value mapping: {ty!r}")


def _example_value(lean_ty: str) -> str:
    ty = _normalize_type(lean_ty)
    if ty == "Uint256":
        return "uint256(1)"
    if ty == "Int256":
        return "int256(1)"
    if ty == "Uint8":
        return "uint8(27)"
    if ty == "Address":
        return "alice"
    if ty == "Bool":
        return "true"
    if ty == "Bytes32":
        return "bytes32(uint256(0xBEEF))"
    if ty == "Bytes":
        return "hex\"CAFE\""
    if ty == "String":
        return '"verity"'
    if ty.startswith("Array "):
        elem = ty[len("Array ") :].strip()
        if elem == "Uint256":
            return "_singletonUintArray(1)"
        if elem == "Address":
            return "_singletonAddressArray(alice)"
        if elem == "Bool":
            return "_singletonBoolArray(true)"
        if elem == "Bytes32":
            return "_singletonBytes32Array(bytes32(uint256(0xBEEF)))"
        raise ValueError(
            "unsupported Lean array element type for generated example value: "
            f"{elem!r}"
        )
    if ty.startswith("Tuple [") and ty.endswith("]"):
        inner = ty[len("Tuple [") : -1]
        elems = _parse_tuple_elements(inner)
        elem_vals = ", ".join(_example_value(e) for e in elems)
        tuple_ty = _sol_tuple_value_type(ty)
        return f"abi.decode(abi.encode({elem_vals}), {tuple_ty})"
    raise ValueError(f"unsupported Lean type for generated example value: {ty!r}")


def _sol_signature(fn: FunctionDecl) -> str:
    param_types = ",".join(_sol_type(p.lean_type) for p in fn.params)
    return f"{fn.name}({param_types})"


def _fn_camel(name: str) -> str:
    return name[:1].upper() + name[1:]


def _binding_type_and_expr(binding: ValueDecl) -> tuple[str, str]:
    return binding.lean_type, binding.expr


def _strip_outer_parens(expr: str) -> str:
    expr = expr.strip()
    while expr.startswith("(") and expr.endswith(")"):
        depth = 0
        balanced = True
        for i, ch in enumerate(expr):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(expr) - 1:
                    balanced = False
                    break
        if not balanced or depth != 0:
            break
        expr = expr[1:-1].strip()
    return expr


def _split_prefix_expr(expr: str) -> tuple[str, list[str]] | None:
    expr = _strip_outer_parens(expr)
    parts: list[str] = []
    current: list[str] = []
    depth = 0
    for ch in expr:
        if ch == "(":
            depth += 1
            current.append(ch)
            continue
        if ch == ")":
            depth -= 1
            current.append(ch)
            continue
        if ch == " " and depth == 0:
            if current:
                parts.append("".join(current).strip())
                current = []
            continue
        current.append(ch)
    if current:
        parts.append("".join(current).strip())
    if len(parts) < 3:
        return None
    return parts[0], parts[1:]


def _split_top_level_csv(expr: str) -> list[str]:
    parts: list[str] = []
    current: list[str] = []
    paren_depth = 0
    bracket_depth = 0
    for ch in expr:
        if ch == "(":
            paren_depth += 1
        elif ch == ")":
            paren_depth -= 1
        elif ch == "[":
            bracket_depth += 1
        elif ch == "]":
            bracket_depth -= 1
        if ch == "," and paren_depth == 0 and bracket_depth == 0:
            part = "".join(current).strip()
            if part:
                parts.append(part)
            current = []
            continue
        current.append(ch)
    tail = "".join(current).strip()
    if tail:
        parts.append(tail)
    return parts


def _lookup_named_binding(contract: ContractDecl, name: str) -> ValueDecl | None:
    return contract.constants.get(name) or contract.immutables.get(name)


def _resolve_named_value_expr(
    contract: ContractDecl,
    name: str,
    lean_type: str,
    constructor_examples: dict[str, str],
    seen: set[str] | None = None,
) -> str | None:
    binding = _lookup_named_binding(contract, name)
    if binding is None:
        return None
    binding_ty, binding_expr = _binding_type_and_expr(binding)
    return _resolve_value_expr(
        contract,
        binding_expr,
        binding_ty or lean_type,
        constructor_examples,
        (seen or set()) | {name},
    )


def _resolve_value_expr(
    contract: ContractDecl,
    expr: str,
    lean_type: str,
    constructor_examples: dict[str, str],
    seen: set[str] | None = None,
    local_values: dict[str, str] | None = None,
) -> str | None:
    seen = seen or set()
    local_values = local_values or {}
    expr = _strip_outer_parens(expr)

    literal = _literal_expr(expr, lean_type)
    if literal is not None:
        return literal

    if expr in constructor_examples:
        return constructor_examples[expr]

    if expr in local_values:
        return local_values[expr]

    if expr in seen:
        return None

    binding = _lookup_named_binding(contract, expr)
    if binding is not None:
        binding_ty, binding_expr = _binding_type_and_expr(binding)
        return _resolve_value_expr(
            contract,
            binding_expr,
            binding_ty or lean_type,
            constructor_examples,
            seen | {expr},
            local_values,
        )

    if lean_type == "Address":
        word_to_address = re.fullmatch(r"wordToAddress\s+(.+)", expr)
        if word_to_address:
            inner = _resolve_value_expr(
                contract,
                word_to_address.group(1),
                "Uint256",
                constructor_examples,
                seen,
                local_values,
            )
            if inner is not None:
                return f"address(uint160({inner}))"

    op_parts = _split_prefix_expr(expr)
    if op_parts is not None:
        op, args = op_parts
        op_map = {"add": "+", "sub": "-", "mul": "*", "div": "/"}
        if op in op_map and len(args) == 2 and lean_type in {"Uint256", "Int256", "Uint8"}:
            lhs = _resolve_value_expr(
                contract, args[0], lean_type, constructor_examples, seen, local_values
            )
            rhs = _resolve_value_expr(contract, args[1], lean_type, constructor_examples, seen, local_values)
            if lhs is not None and rhs is not None:
                return f"({lhs} {op_map[op]} {rhs})"

    return None


def _return_shape_assertion(lean_ty: str, fn_name: str) -> str:
    ty = _normalize_type(lean_ty)
    if ty in {"Uint256", "Int256", "Uint8", "Address", "Bool", "Bytes32"}:
        return (
            f'        assertEq(ret.length, 32, "{fn_name} ABI return length mismatch (expected 32 bytes)");'
        )
    if ty in {"Bytes", "String"}:
        return (
            f'        require(ret.length >= 64, "{fn_name} ABI return payload unexpectedly short");'
        )
    if ty.startswith("Array "):
        return (
            f'        require(ret.length >= 64, "{fn_name} ABI dynamic return payload unexpectedly short");'
        )
    if ty.startswith("Tuple [") and ty.endswith("]"):
        inner = ty[len("Tuple [") : -1]
        n_elems = len(_parse_tuple_elements(inner))
        expected_min = n_elems * 32
        return (
            f'        require(ret.length >= {expected_min}, "{fn_name} ABI tuple return payload unexpectedly short");'
        )
    raise ValueError(f"unsupported Lean return type for generated assertion: {ty!r}")


def _storage_word_expr(lean_ty: str, value_expr: str) -> str:
    ty = _normalize_type(lean_ty)
    if ty in {"Uint256", "Int256", "Uint8"}:
        return f"bytes32(uint256({value_expr}))"
    if ty == "Bool":
        return f"bytes32(uint256({value_expr} ? 1 : 0))"
    if ty == "Address":
        return f"bytes32(uint256(uint160({value_expr})))"
    if ty == "Bytes32":
        return value_expr
    raise ValueError(f"unsupported Lean type for generated storage write: {ty!r}")


def _single_word_uint_expr(lean_ty: str, value_expr: str) -> str | None:
    ty = _normalize_type(lean_ty)
    if ty in {"Uint256", "Int256", "Uint8"}:
        return f"uint256({value_expr})"
    if ty == "Bool":
        return f"({value_expr} ? 1 : 0)"
    if ty == "Address":
        return f"uint256(uint160({value_expr}))"
    if ty == "Bytes32":
        return f"uint256({value_expr})"
    return None


def _literal_expr(value: str, lean_ty: str) -> str | None:
    ty = _normalize_type(lean_ty)
    if ty in {"Uint256", "Int256", "Uint8"} and re.fullmatch(r"(0x[0-9A-Fa-f]+|[0-9]+)", value):
        return value
    if ty == "Bool" and value in {"true", "false"}:
        return value
    if ty == "Bytes32" and re.fullmatch(r"(0x[0-9A-Fa-f]+|[0-9]+)", value):
        return f"bytes32(uint256({value}))"
    return None


def _split_return_values(exprs_src: str) -> list[str]:
    return [part.strip() for part in exprs_src.split(",") if part.strip()]


def _matches_return_expr(line: str, expr: str) -> bool:
    return line in {f"return {expr}", f"return ({expr})"}


def _storage_read_type(contract: ContractDecl, read: ReadAccessor) -> str | None:
    if read.accessor == "getStorageAddr":
        return "Address"
    if read.accessor == "getStorage":
        return contract.storage_types.get(read.storage_name)
    return None


def _parse_struct_member_layouts(storage_ty: str) -> dict[str, StructMemberLayout] | None:
    ty = _normalize_type(storage_ty)
    if ty.startswith("MappingStruct(") and ty.endswith(")"):
        inner = ty[len("MappingStruct(") : -1]
    elif ty.startswith("MappingStruct2(") and ty.endswith(")"):
        inner = ty[len("MappingStruct2(") : -1]
    else:
        return None
    parts = _split_top_level_csv(inner)
    if not parts:
        return None
    members_src = parts[-1]
    if not (members_src.startswith("[") and members_src.endswith("]")):
        return None
    layouts: dict[str, StructMemberLayout] = {}
    member_specs = _split_top_level_csv(members_src[1:-1])
    for spec in member_specs:
        match = re.fullmatch(
            r"([A-Za-z_][A-Za-z0-9_]*)\s+@word\s+([0-9]+)(?:\s+packed\(([0-9]+),([0-9]+)\))?",
            spec.strip(),
        )
        if match is None:
            return None
        layouts[match.group(1)] = StructMemberLayout(
            word_offset=int(match.group(2)),
            packed_offset=int(match.group(3)) if match.group(3) is not None else None,
            packed_width=int(match.group(4)) if match.group(4) is not None else None,
        )
    return layouts


def _struct_member_layout(contract: ContractDecl, read: ReadAccessor) -> StructMemberLayout | None:
    if read.member_name is None:
        return None
    storage_ty = contract.storage_types.get(read.storage_name)
    if storage_ty is None:
        return None
    layouts = _parse_struct_member_layouts(storage_ty)
    if layouts is None:
        return None
    return layouts.get(read.member_name)


def _struct_member_slot_expr(
    contract: ContractDecl,
    fn: FunctionDecl,
    read: ReadAccessor,
    param_examples: dict[str, str],
) -> str | None:
    if read.accessor not in {"structMember", "structMember2"}:
        return None
    base_accessor = "getMapping2" if read.accessor == "structMember2" else "getMapping"
    base_slot = _mapping_slot_expr(
        contract,
        fn,
        ReadAccessor(
            var_name=read.var_name,
            accessor=base_accessor,
            storage_name=read.storage_name,
            key_names=read.key_names,
        ),
        param_examples,
    )
    layout = _struct_member_layout(contract, read)
    if layout is None:
        return None
    if layout.word_offset == 0:
        return base_slot
    return f"bytes32(uint256({base_slot}) + {layout.word_offset})"


def _flush_pending_struct_slots(
    setup_lines: list[str],
    pending_struct_slots: dict[str, list[str]],
) -> None:
    for slot_expr, terms in pending_struct_slots.items():
        combined = " | ".join(terms)
        setup_lines.append(f"vm.store(target, {slot_expr}, bytes32({combined}));")


def _seed_struct_read_setup(
    contract: ContractDecl,
    fn: FunctionDecl,
    read: ReadAccessor,
    read_ty: str,
    param_examples: dict[str, str],
    expected_name: str,
    setup_lines: list[str],
    pending_struct_slots: dict[str, list[str]],
) -> bool:
    slot_expr = _struct_member_slot_expr(contract, fn, read, param_examples)
    layout = _struct_member_layout(contract, read)
    if slot_expr is None or layout is None:
        return False
    setup_lines.append(f"{_sol_type(read_ty)} {expected_name} = {_example_value(read_ty)};")
    if layout.packed_offset is None:
        if slot_expr in pending_struct_slots:
            return False
        setup_lines.append(f"vm.store(target, {slot_expr}, {_storage_word_expr(read_ty, expected_name)});")
        return True
    packed_value = _single_word_uint_expr(read_ty, expected_name)
    if packed_value is None:
        return False
    shifted = (
        packed_value
        if layout.packed_offset == 0
        else f"({packed_value} << {layout.packed_offset})"
    )
    pending_struct_slots.setdefault(slot_expr, []).append(shifted)
    return True


def _render_inferred_scalar_return(
    fn: FunctionDecl,
    idx: int,
    encode_args: str,
    decoded_type: str,
    expected_expr: str,
    setup_lines: list[str],
    summary: str,
    suffix: str,
) -> str:
    return _render_decoded_assertion(
        fn,
        idx,
        encode_args,
        _return_shape_assertion(fn.return_type, fn.name),
        decoded_type,
        setup_lines,
        f"{decoded_type} actual = abi.decode(ret, ({decoded_type}));",
        [f'assertEq(actual, {expected_expr}, "{fn.name} should preserve the inferred result");'],
        summary,
        suffix,
    )


def _render_inferred_tuple_return(
    fn: FunctionDecl,
    idx: int,
    encode_args: str,
    elem_types: list[str],
    expected_exprs: list[str],
    setup_lines: list[str],
    summary: str,
    suffix: str,
) -> str:
    typed_vars = ", ".join(f"{_sol_type(elem_ty)} actual{i}" for i, elem_ty in enumerate(elem_types))
    raw_types = ", ".join(_sol_type(elem_ty) for elem_ty in elem_types)
    return _render_decoded_assertion(
        fn,
        idx,
        encode_args,
        _return_shape_assertion(fn.return_type, fn.name),
        _sol_type(fn.return_type),
        setup_lines,
        f"({typed_vars}) = abi.decode(ret, ({raw_types}));",
        [
            f'assertEq(actual{i}, {expected_exprs[i]}, "{fn.name} tuple element {i} should preserve the inferred result");'
            for i in range(len(elem_types))
        ],
        summary,
        suffix,
    )


def _parse_read_accessor(line: str) -> ReadAccessor | None:
    storage_match = STORAGE_READ_RE.fullmatch(line)
    if storage_match:
        return ReadAccessor(
            var_name=storage_match.group(1),
            accessor=storage_match.group(2),
            storage_name=storage_match.group(3),
            key_names=(),
        )

    storage_array_length_match = STORAGE_ARRAY_LENGTH_RE.fullmatch(line)
    if storage_array_length_match:
        return ReadAccessor(
            var_name=storage_array_length_match.group(1),
            accessor="getStorageArrayLength",
            storage_name=storage_array_length_match.group(2),
            key_names=(),
        )

    storage_array_element_match = STORAGE_ARRAY_ELEMENT_RE.fullmatch(line)
    if storage_array_element_match:
        return ReadAccessor(
            var_name=storage_array_element_match.group(1),
            accessor="getStorageArrayElement",
            storage_name=storage_array_element_match.group(2),
            key_names=(),
            array_index=int(storage_array_element_match.group(3)),
        )

    mapping_match = MAPPING_READ_RE.fullmatch(line)
    if mapping_match:
        return ReadAccessor(
            var_name=mapping_match.group(1),
            accessor=mapping_match.group(2),
            storage_name=mapping_match.group(3),
            key_names=(mapping_match.group(4),),
        )

    mapping2_match = MAPPING2_READ_RE.fullmatch(line)
    if mapping2_match:
        return ReadAccessor(
            var_name=mapping2_match.group(1),
            accessor="getMapping2",
            storage_name=mapping2_match.group(2),
            key_names=(mapping2_match.group(3), mapping2_match.group(4)),
        )

    mapping_word_match = MAPPING_WORD_READ_RE.fullmatch(line)
    if mapping_word_match:
        return ReadAccessor(
            var_name=mapping_word_match.group(1),
            accessor="getMappingWord",
            storage_name=mapping_word_match.group(2),
            key_names=(mapping_word_match.group(3),),
            word_offset=int(mapping_word_match.group(4)),
        )

    mapping_n_match = MAPPING_N_READ_RE.fullmatch(line)
    if mapping_n_match:
        keys = tuple(_split_top_level_csv(mapping_n_match.group(3)))
        if not keys:
            return None
        return ReadAccessor(
            var_name=mapping_n_match.group(1),
            accessor="getMappingN",
            storage_name=mapping_n_match.group(2),
            key_names=keys,
        )

    struct_member_match = STRUCT_MEMBER_READ_RE.fullmatch(line)
    if struct_member_match:
        return ReadAccessor(
            var_name=struct_member_match.group(1),
            accessor="structMember",
            storage_name=struct_member_match.group(2),
            key_names=(struct_member_match.group(3),),
            member_name=struct_member_match.group(4),
        )

    struct_member2_match = STRUCT_MEMBER2_READ_RE.fullmatch(line)
    if struct_member2_match:
        return ReadAccessor(
            var_name=struct_member2_match.group(1),
            accessor="structMember2",
            storage_name=struct_member2_match.group(2),
            key_names=(struct_member2_match.group(3), struct_member2_match.group(4)),
            member_name=struct_member2_match.group(5),
        )

    return None


def _mapping_key_expr(param: ParamDecl, value_expr: str) -> str:
    ty = _normalize_type(param.lean_type)
    if ty == "Address":
        return f"bytes32(uint256(uint160({value_expr})))"
    if ty in {"Uint256", "Uint8", "Bytes32"}:
        return f"bytes32(uint256({value_expr}))"
    raise ValueError(f"unsupported Lean key type for generated mapping setup: {ty!r}")


def _mapping_n_key_expr(
    key_src: str,
    fn: FunctionDecl,
    param_examples: dict[str, str],
) -> str:
    params = {param.name: param for param in fn.params}
    if key_src in params:
        value_expr = param_examples.get(key_src)
        if value_expr is None:
            raise ValueError(f"missing example value for parameter '{key_src}' in function '{fn.name}'")
        return _mapping_key_expr(params[key_src], value_expr)

    address_word_match = re.fullmatch(r"addressToWord\s+([A-Za-z_][A-Za-z0-9_]*)", key_src)
    if address_word_match:
        inner_name = address_word_match.group(1)
        param = params.get(inner_name)
        value_expr = param_examples.get(inner_name)
        if param is None or value_expr is None:
            raise ValueError(
                f"unsupported getMappingN key expression '{key_src}' in function '{fn.name}'"
            )
        if _normalize_type(param.lean_type) != "Address":
            raise ValueError(
                f"addressToWord key expression must reference an Address parameter, got {param.lean_type!r}"
            )
        return f"bytes32(uint256(uint160({value_expr})))"

    raise ValueError(f"unsupported getMappingN key expression '{key_src}' in function '{fn.name}'")


def _mapping_slot_expr(
    contract: ContractDecl,
    fn: FunctionDecl,
    read: ReadAccessor,
    param_examples: dict[str, str],
) -> str:
    slot = contract.storage_slots.get(read.storage_name)
    if slot is None:
        raise ValueError(f"unknown storage slot '{read.storage_name}' on contract '{contract.name}'")

    key_exprs = []
    for key_name in read.key_names:
        if read.accessor == "getMappingN":
            key_exprs.append(_mapping_n_key_expr(key_name, fn, param_examples))
            continue
        params = {param.name: param for param in fn.params}
        param = params.get(key_name)
        if param is None:
            raise ValueError(f"unknown parameter '{key_name}' in function '{fn.name}'")
        value_expr = param_examples.get(key_name)
        if value_expr is None:
            raise ValueError(f"missing example value for parameter '{key_name}' in function '{fn.name}'")
        key_exprs.append(_mapping_key_expr(param, value_expr))

    if read.accessor == "getMapping2":
        return f"_nestedMappingSlot({key_exprs[0]}, {key_exprs[1]}, {slot})"
    if read.accessor == "getMappingWord":
        return f"_mappingWordSlot({key_exprs[0]}, {slot}, {read.word_offset})"
    if read.accessor == "getMappingN":
        current = f"_mappingSlot({key_exprs[0]}, {slot})"
        for key_expr in key_exprs[1:]:
            current = f"keccak256(abi.encode({key_expr}, {current}))"
        return current
    if read.accessor in {"getMapping", "getMappingUint", "getMappingAddr", "getMappingUintAddr"}:
        return f"_mappingSlot({key_exprs[0]}, {slot})"
    raise ValueError(f"unsupported accessor for mapping slot generation: {read.accessor!r}")


def _storage_array_element_slot_expr(slot: int, index: int) -> str:
    return f"bytes32(uint256(keccak256(abi.encode(uint256({slot})))) + {index})"


def _render_decoded_assertion(
    fn: FunctionDecl,
    idx: int,
    encode_args: str,
    ret_assert: str,
    decoded_type: str,
    setup_lines: list[str],
    actual_decode: str,
    assert_lines: list[str],
    summary: str,
    suffix: str,
) -> str:
    setup = "\n".join(f"        {line}" for line in setup_lines)
    asserts = "\n".join(f"        {line}" for line in assert_lines)
    if setup:
        setup += "\n"
    return f"""    // Property {idx}: {summary}
    function testAuto_{_fn_camel(fn.name)}_{suffix}() public {{
{setup}        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature({encode_args}));
        require(ok, \"{fn.name} reverted unexpectedly\");
{ret_assert}
        {actual_decode}
{asserts}
    }}
"""


def _render_direct_return_assertion(
    fn: FunctionDecl,
    idx: int,
    encode_args: str,
    decoded_type: str,
    expected_expr: str,
    summary: str,
    suffix: str,
) -> str:
    ret_assert = _return_shape_assertion(fn.return_type, fn.name)
    return f"""    // Property {idx}: {summary}
    function testAuto_{_fn_camel(fn.name)}_{suffix}() public {{
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature({encode_args}));
        require(ok, \"{fn.name} reverted unexpectedly\");
{ret_assert}
        {decoded_type} actual = abi.decode(ret, ({decoded_type}));
        assertEq(actual, {expected_expr}, \"{fn.name} should preserve the expected value\");
    }}
"""


def _render_dynamic_param_compare_assertion(
    fn: FunctionDecl,
    idx: int,
    encode_args: str,
    decoded_type: str,
    expected_expr: str,
    summary: str,
    suffix: str,
    assertion_expr: str,
    assertion_msg: str,
) -> str:
    ret_assert = _return_shape_assertion(fn.return_type, fn.name)
    return f"""    // Property {idx}: {summary}
    function testAuto_{_fn_camel(fn.name)}_{suffix}() public {{
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature({encode_args}));
        require(ok, \"{fn.name} reverted unexpectedly\");
{ret_assert}
        {decoded_type} actual = abi.decode(ret, ({decoded_type}));
        {decoded_type} expected = {expected_expr};
        assertEq(actual, expected, \"{assertion_msg}\");
        {assertion_expr}
    }}
"""


def _infer_straight_line_non_unit_test(
    contract: ContractDecl,
    fn: FunctionDecl,
    idx: int,
    encode_args: str,
    decoded_type: str,
    param_examples: dict[str, str],
    param_types: dict[str, str],
    constructor_examples: dict[str, str],
) -> str | None:
    if not fn.body:
        return None

    local_values = dict(param_examples)
    local_types = dict(param_types)
    setup_lines: list[str] = []
    pending_struct_slots: dict[str, list[str]] = {}
    seeded_reads = 0

    for line in fn.body[:-1]:
        read = _parse_read_accessor(line)
        if read is not None:
            if read.accessor in {"structMember", "structMember2"}:
                expected_name = "expected" if seeded_reads == 0 else f"expected{seeded_reads}"
                read_ty = _normalize_type(fn.return_type)
                if not _seed_struct_read_setup(
                    contract,
                    fn,
                    read,
                    read_ty,
                    param_examples,
                    expected_name,
                    setup_lines,
                    pending_struct_slots,
                ):
                    return None
                local_values[read.var_name] = expected_name
                local_types[read.var_name] = read_ty
                seeded_reads += 1
                continue
            if read.accessor not in {"getStorage", "getStorageAddr"}:
                return None
            slot = contract.storage_slots.get(read.storage_name)
            read_ty = _storage_read_type(contract, read)
            if slot is None or read_ty is None:
                return None
            expected_name = "expected" if seeded_reads == 0 else f"expected{seeded_reads}"
            setup_lines.append(f"{_sol_type(read_ty)} {expected_name} = {_example_value(read_ty)};")
            setup_lines.append(
                f"vm.store(target, bytes32(uint256({slot})), {_storage_word_expr(read_ty, expected_name)});"
            )
            local_values[read.var_name] = expected_name
            local_types[read.var_name] = read_ty
            seeded_reads += 1
            continue

        let_match = re.fullmatch(r"let\s+(?:mut\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*:=\s*(.+)", line)
        if let_match:
            name, expr = let_match.groups()
            target_ty = local_types.get(name, _normalize_type(fn.return_type))
            resolved = _resolve_value_expr(
                contract,
                expr,
                target_ty,
                constructor_examples,
                local_values=local_values,
            )
            if resolved is None:
                return None
            local_values[name] = resolved
            local_types[name] = target_ty
            continue

        assign_match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)\s*:=\s*(.+)", line)
        if assign_match:
            name, expr = assign_match.groups()
            target_ty = local_types.get(name)
            if target_ty is None:
                return None
            resolved = _resolve_value_expr(
                contract,
                expr,
                target_ty,
                constructor_examples,
                local_values=local_values,
            )
            if resolved is None:
                return None
            local_values[name] = resolved
            continue

        return None

    _flush_pending_struct_slots(setup_lines, pending_struct_slots)

    final_line = fn.body[-1]
    return_match = re.fullmatch(r"return\s+(.+)", final_line)
    if return_match is None:
        return None

    return_ty = _normalize_type(fn.return_type)
    return_expr = return_match.group(1).strip()
    if return_ty.startswith("Tuple [") and return_ty.endswith("]"):
        elems = _parse_tuple_elements(return_ty[len("Tuple [") : -1])
        tuple_expr = _strip_outer_parens(return_expr)
        tuple_parts = _split_top_level_csv(tuple_expr)
        if len(tuple_parts) != len(elems):
            return None
        expected_exprs: list[str] = []
        for elem_ty, elem_expr in zip(elems, tuple_parts):
            resolved = _resolve_value_expr(
                contract,
                elem_expr,
                elem_ty,
                constructor_examples,
                local_values=local_values,
            )
            if resolved is None:
                return None
            expected_exprs.append(resolved)
        return _render_inferred_tuple_return(
            fn,
            idx,
            encode_args,
            elems,
            expected_exprs,
            setup_lines,
            f"{fn.name} decodes and matches the inferred tuple result",
            "ReturnsInferredTupleResult",
        )

    expected_expr = _resolve_value_expr(
        contract,
        return_expr,
        return_ty,
        constructor_examples,
        local_values=local_values,
    )
    if expected_expr is None:
        return None
    return _render_inferred_scalar_return(
        fn,
        idx,
        encode_args,
        decoded_type,
        expected_expr,
        setup_lines,
        f"{fn.name} decodes and matches the inferred straight-line result",
        "ReturnsInferredStraightLineResult",
    )


def _render_inferred_non_unit_test(contract: ContractDecl, fn: FunctionDecl, idx: int, encode_args: str) -> str | None:
    fn_camel = _fn_camel(fn.name)
    body = list(fn.body)
    ty = _normalize_type(fn.return_type)
    param_examples = {param.name: _example_value(param.lean_type) for param in fn.params}
    constructor_examples = (
        {param.name: _example_value(param.lean_type) for param in contract.constructor.params}
        if contract.constructor is not None
        else {}
    )
    decoded_type = _sol_type(fn.return_type)
    param_types = {param.name: _normalize_type(param.lean_type) for param in fn.params}

    if len(body) == 1:
        compare_match = PARAM_COMPARE_RETURN_RE.fullmatch(body[0])
        if compare_match and ty == "Bool":
            lhs_name, op, rhs_name = compare_match.groups()
            lhs_ty = param_types.get(lhs_name)
            rhs_ty = param_types.get(rhs_name)
            lhs_example = param_examples.get(lhs_name)
            rhs_example = param_examples.get(rhs_name)
            if (
                lhs_ty is not None
                and rhs_ty is not None
                and lhs_ty == rhs_ty
                and lhs_ty in {"String", "Bytes"}
                and lhs_example is not None
                and rhs_example is not None
            ):
                examples_match = lhs_example == rhs_example
                expected_expr = "true" if (examples_match if op == "==" else not examples_match) else "false"
                compare_kind = lhs_ty.lower()
                return _render_dynamic_param_compare_assertion(
                    fn,
                    idx,
                    encode_args,
                    decoded_type,
                    expected_expr,
                    f"{fn.name} matches the expected dynamic-parameter comparison result",
                    "ComparesDirectDynamicParamsEq" if op == "==" else "ComparesDirectDynamicParamsNeq",
                    (
                        f'assertTrue(actual, "{fn.name} should return true for the configured {compare_kind} comparison");'
                        if expected_expr == "true"
                        else f'assertFalse(actual, "{fn.name} should return false for the configured {compare_kind} comparison");'
                    ),
                    f"{fn.name} should preserve the configured comparison result",
                )

        direct_return_match = re.fullmatch(r"return\s+([A-Za-z_][A-Za-z0-9_]*)", body[0])
        if direct_return_match:
            returned_name = direct_return_match.group(1)
            if returned_name in param_examples:
                return _render_direct_return_assertion(
                    fn,
                    idx,
                    encode_args,
                    decoded_type,
                    param_examples[returned_name],
                    f"{fn.name} returns the direct parameter value",
                    "ReturnsDirectParam",
                )
            resolved_named_value = _resolve_named_value_expr(
                contract,
                returned_name,
                ty,
                constructor_examples,
            )
            if resolved_named_value is not None:
                return _render_direct_return_assertion(
                    fn,
                    idx,
                    encode_args,
                    decoded_type,
                    resolved_named_value,
                    f"{fn.name} returns the declared constant or immutable value",
                    "ReturnsDeclaredBinding",
                )

        return_bytes_match = re.fullmatch(r"returnBytes\s+([A-Za-z_][A-Za-z0-9_]*)", body[0])
        if return_bytes_match:
            returned_name = return_bytes_match.group(1)
            if returned_name in param_examples:
                return _render_direct_return_assertion(
                    fn,
                    idx,
                    encode_args,
                    decoded_type,
                    param_examples[returned_name],
                    f"{fn.name} returns the direct dynamic parameter payload",
                    "ReturnsDirectDynamicParam",
                )

        storage_words_match = re.fullmatch(r"returnStorageWords\s+([A-Za-z_][A-Za-z0-9_]*)", body[0])
        if storage_words_match and ty == "Array Uint256":
            returned_name = storage_words_match.group(1)
            param_ty = param_types.get(returned_name)
            example_expr = param_examples.get(returned_name)
            if param_ty is not None and example_expr is not None and param_ty.startswith("Array "):
                elem_ty = param_ty[len("Array ") :].strip()
                expected_word_expr = _single_word_uint_expr(elem_ty, _example_value(elem_ty))
                if expected_word_expr is not None:
                    ret_assert = _return_shape_assertion(fn.return_type, fn.name)
                    return f"""    // Property {idx}: {fn.name} returns the canonical storage words for the configured input slots
    function testAuto_{fn_camel}_ReturnsCanonicalStorageWords() public {{
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature({encode_args}));
        require(ok, \"{fn.name} reverted unexpectedly\");
{ret_assert}
        uint256[] memory actual = abi.decode(ret, (uint256[]));
        assertEq(actual.length, 1, \"{fn.name} should return one word for the configured singleton input\");
        assertEq(actual[0], {expected_word_expr}, \"{fn.name} should return the canonical word for the configured input\");
    }}
"""

        literal_match = re.fullmatch(r"return\s+(.+)", body[0])
        if literal_match:
            literal_expr = _literal_expr(literal_match.group(1).strip(), ty)
            if literal_expr is not None:
                ret_assert = _return_shape_assertion(fn.return_type, fn.name)
                return f"""    // Property {idx}: {fn.name} returns the declared constant result
    function testAuto_{fn_camel}_ReturnsDeclaredConstant() public {{
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature({encode_args}));
        require(ok, \"{fn.name} reverted unexpectedly\");
{ret_assert}
        {decoded_type} actual = abi.decode(ret, ({decoded_type}));
        assertEq(actual, {literal_expr}, \"{fn.name} should return the declared constant\");
    }}
"""
        tuple_match = re.fullmatch(r"returnValues\s+\[(.+)\]", body[0])
        if tuple_match and ty.startswith("Tuple [") and ty.endswith("]"):
            elems = _parse_tuple_elements(ty[len("Tuple [") : -1])
            exprs = _split_return_values(tuple_match.group(1))
            if len(elems) != len(exprs):
                return None
            expected_exprs: list[str] = []
            for elem_ty, expr in zip(elems, exprs):
                if expr in param_examples:
                    expected_exprs.append(param_examples[expr])
                    continue
                literal_expr = _literal_expr(expr, elem_ty)
                if literal_expr is None:
                    return None
                expected_exprs.append(literal_expr)
            typed_vars = ", ".join(f"{_sol_type(elem_ty)} actual{i}" for i, elem_ty in enumerate(elems))
            raw_types = ", ".join(_sol_type(elem_ty) for elem_ty in elems)
            assert_lines = "\n".join(
                f'        assertEq(actual{i}, {expected_exprs[i]}, "{fn.name} tuple element {i} mismatch");'
                for i in range(len(elems))
            )
            ret_assert = _return_shape_assertion(fn.return_type, fn.name)
            return f"""    // Property {idx}: {fn.name} decodes and matches the returned tuple elements
    function testAuto_{fn_camel}_DecodesTupleResult() public {{
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature({encode_args}));
        require(ok, \"{fn.name} reverted unexpectedly\");
{ret_assert}
        ({typed_vars}) = abi.decode(ret, ({raw_types}));
{assert_lines}
    }}
"""

    if len(body) == 2:
        builtin_read_match = BUILTIN_READ_RE.fullmatch(body[0])
        if builtin_read_match and body[1] == f"return {builtin_read_match.group(1)}":
            builtin_name = builtin_read_match.group(2)
            expected_expr = "alice" if builtin_name == "msgSender" else "0"
            summary = (
                f"{fn.name} returns the active caller"
                if builtin_name == "msgSender"
                else f"{fn.name} returns the active call value"
            )
            suffix = "ReturnsMsgSender" if builtin_name == "msgSender" else "ReturnsMsgValue"
            return _render_direct_return_assertion(
                fn,
                idx,
                encode_args,
                decoded_type,
                expected_expr,
                summary,
                suffix,
            )

        read = _parse_read_accessor(body[0])
        if read and body[1] == f"return {read.var_name}":
            ret_assert = _return_shape_assertion(fn.return_type, fn.name)
            expected_expr = _example_value(fn.return_type)
            if read.accessor in {"structMember", "structMember2"}:
                setup_lines: list[str] = []
                pending_struct_slots: dict[str, list[str]] = {}
                if not _seed_struct_read_setup(
                    contract,
                    fn,
                    read,
                    _normalize_type(fn.return_type),
                    param_examples,
                    "expected",
                    setup_lines,
                    pending_struct_slots,
                ):
                    return None
                _flush_pending_struct_slots(setup_lines, pending_struct_slots)
                return _render_decoded_assertion(
                    fn,
                    idx,
                    encode_args,
                    ret_assert,
                    decoded_type,
                    setup_lines,
                    f"{decoded_type} actual = abi.decode(ret, ({decoded_type}));",
                    [f'assertEq(actual, expected, "{fn.name} should decode the configured struct member");'],
                    f"{fn.name} reads the configured struct member",
                    "ReadsConfiguredStructMember",
                )
            if read.accessor in {"getStorage", "getStorageAddr"}:
                slot = contract.storage_slots.get(read.storage_name)
                if slot is None:
                    return None
                return f"""    // Property {idx}: {fn.name} reads storage slot {slot} and decodes the result
    function testAuto_{fn_camel}_ReadsConfiguredStorage() public {{
        {decoded_type} expected = {expected_expr};
        vm.store(target, bytes32(uint256({slot})), {_storage_word_expr(fn.return_type, "expected")});
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature({encode_args}));
        require(ok, \"{fn.name} reverted unexpectedly\");
{ret_assert}
        {decoded_type} actual = abi.decode(ret, ({decoded_type}));
        assertEq(actual, expected, \"{fn.name} should return storage slot {slot}\");
    }}
"""
            if read.accessor == "getStorageArrayLength":
                slot = contract.storage_slots.get(read.storage_name)
                if slot is None:
                    return None
                return _render_decoded_assertion(
                    fn,
                    idx,
                    encode_args,
                    ret_assert,
                    decoded_type,
                    [
                        f"uint256 expected = {_example_value('Uint256')};",
                        f"vm.store(target, bytes32(uint256({slot})), bytes32(expected));",
                    ],
                    f"{decoded_type} actual = abi.decode(ret, ({decoded_type}));",
                    [f'assertEq(actual, expected, "{fn.name} should return the configured array length");'],
                    f"{fn.name} reads the configured storage-array length",
                    "ReadsConfiguredStorageArrayLength",
                )
            if read.accessor == "getStorageArrayElement":
                slot = contract.storage_slots.get(read.storage_name)
                if slot is None or read.array_index is None:
                    return None
                return _render_decoded_assertion(
                    fn,
                    idx,
                    encode_args,
                    ret_assert,
                    decoded_type,
                    [
                        f"{decoded_type} expected = {expected_expr};",
                        f"vm.store(target, bytes32(uint256({slot})), bytes32(uint256({read.array_index + 1})));",
                        f"vm.store(target, {_storage_array_element_slot_expr(slot, read.array_index)}, {_storage_word_expr(fn.return_type, 'expected')});",
                    ],
                    f"{decoded_type} actual = abi.decode(ret, ({decoded_type}));",
                    [f'assertEq(actual, expected, "{fn.name} should return the configured array element");'],
                    f"{fn.name} reads the configured storage-array element",
                    "ReadsConfiguredStorageArrayElement",
                )
            if read.accessor in {
                "getMapping",
                "getMappingUint",
                "getMappingAddr",
                "getMappingUintAddr",
                "getMapping2",
                "getMappingWord",
                "getMappingN",
            }:
                slot_expr = _mapping_slot_expr(contract, fn, read, param_examples)
                return _render_decoded_assertion(
                    fn,
                    idx,
                    encode_args,
                    ret_assert,
                    decoded_type,
                    [
                        f"{decoded_type} expected = {expected_expr};",
                        f"vm.store(target, {slot_expr}, {_storage_word_expr(fn.return_type, 'expected')});",
                    ],
                    f"{decoded_type} actual = abi.decode(ret, ({decoded_type}));",
                    [f'assertEq(actual, expected, "{fn.name} should decode the configured mapping value");'],
                    f"{fn.name} reads the configured mapping value",
                    "ReadsConfiguredMapping",
                )

        if read and ty == "Bool":
            ret_assert = _return_shape_assertion(fn.return_type, fn.name)
            slot_expr = _mapping_slot_expr(contract, fn, read, param_examples)
            if _matches_return_expr(body[1], f"{read.var_name} != 0"):
                return _render_decoded_assertion(
                    fn,
                    idx,
                    encode_args,
                    ret_assert,
                    decoded_type,
                    [
                        f"vm.store(target, {slot_expr}, bytes32(uint256(1)));",
                    ],
                    f"{decoded_type} actual = abi.decode(ret, ({decoded_type}));",
                    [f'assertTrue(actual, "{fn.name} should return true when the configured word is non-zero");'],
                    f"{fn.name} returns true for a non-zero configured mapping word",
                    "DetectsNonZeroMappingWord",
                )
            if _matches_return_expr(body[1], f"{read.var_name} != zeroAddress"):
                return _render_decoded_assertion(
                    fn,
                    idx,
                    encode_args,
                    ret_assert,
                    decoded_type,
                    [
                        f"vm.store(target, {slot_expr}, bytes32(uint256(uint160(address(0xBEEF)))));",
                    ],
                    f"{decoded_type} actual = abi.decode(ret, ({decoded_type}));",
                    [f'assertTrue(actual, "{fn.name} should return true when the configured address is non-zero");'],
                    f"{fn.name} returns true for a non-zero configured mapping address",
                    "DetectsNonZeroMappingAddress",
                )
            if body[1] == f"return isZeroAddress {read.var_name}":
                return _render_decoded_assertion(
                    fn,
                    idx,
                    encode_args,
                    ret_assert,
                    decoded_type,
                    [
                        f"vm.store(target, {slot_expr}, bytes32(0));",
                    ],
                    f"{decoded_type} actual = abi.decode(ret, ({decoded_type}));",
                    [f'assertTrue(actual, "{fn.name} should return true when the configured address is zero");'],
                    f"{fn.name} returns true for a zero configured mapping address",
                    "DetectsZeroMappingAddress",
                )

    if len(body) == 3:
        read = _parse_read_accessor(body[0])
        require_match = NON_ZERO_REQUIRE_RE.fullmatch(body[1])
        if (
            read
            and read.accessor == "getMappingUint"
            and require_match
            and require_match.group(1) == read.var_name
            and body[2] == f"return wordToAddress {read.var_name}"
            and ty == "Address"
        ):
            ret_assert = _return_shape_assertion(fn.return_type, fn.name)
            slot_expr = _mapping_slot_expr(contract, fn, read, param_examples)
            return _render_decoded_assertion(
                fn,
                idx,
                encode_args,
                ret_assert,
                decoded_type,
                [
                    f"{decoded_type} expected = address(0xBEEF);",
                    f"vm.store(target, {slot_expr}, bytes32(uint256(uint160(expected))));",
                ],
                f"{decoded_type} actual = abi.decode(ret, ({decoded_type}));",
                [f'assertEq(actual, expected, "{fn.name} should decode the configured owner word");'],
                f"{fn.name} decodes a non-zero configured owner word",
                "DecodesConfiguredOwnerWord",
            )

    if len(body) == 4:
        branch_match = PARAM_COMPARE_BRANCH_RE.fullmatch(body[0])
        then_match = re.fullmatch(r"return\s+(.+)", body[1])
        else_match = re.fullmatch(r"return\s+(.+)", body[3])
        if branch_match and body[2] == "else" and then_match and else_match:
            lhs_name, op, rhs_name = branch_match.groups()
            lhs_ty = param_types.get(lhs_name)
            rhs_ty = param_types.get(rhs_name)
            lhs_example = param_examples.get(lhs_name)
            rhs_example = param_examples.get(rhs_name)
            if (
                lhs_ty is not None
                and rhs_ty is not None
                and lhs_ty == rhs_ty
                and lhs_ty in {"String", "Bytes"}
                and lhs_example is not None
                and rhs_example is not None
            ):
                examples_match = lhs_example == rhs_example
                take_then = examples_match if op == "==" else not examples_match
                expected_expr = _literal_expr(
                    then_match.group(1).strip() if take_then else else_match.group(1).strip(),
                    ty,
                )
                if expected_expr is not None:
                    ret_assert = _return_shape_assertion(fn.return_type, fn.name)
                    return f"""    // Property {idx}: {fn.name} selects the expected branch for the configured dynamic inputs
    function testAuto_{fn_camel}_SelectsDynamicComparisonBranch() public {{
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature({encode_args}));
        require(ok, \"{fn.name} reverted unexpectedly\");
{ret_assert}
        {decoded_type} actual = abi.decode(ret, ({decoded_type}));
        assertEq(actual, {expected_expr}, \"{fn.name} should return the configured branch value\");
    }}
"""

        precondition_read = _parse_read_accessor(body[0])
        require_match = NON_ZERO_REQUIRE_RE.fullmatch(body[1])
        result_read = _parse_read_accessor(body[2])
        if (
            precondition_read
            and result_read
            and precondition_read.accessor == "getMappingUint"
            and require_match
            and require_match.group(1) == precondition_read.var_name
            and body[3] == f"return {result_read.var_name}"
        ):
            ret_assert = _return_shape_assertion(fn.return_type, fn.name)
            owner_slot_expr = _mapping_slot_expr(contract, fn, precondition_read, param_examples)
            result_slot_expr = _mapping_slot_expr(contract, fn, result_read, param_examples)
            expected_expr = _example_value(fn.return_type)
            return _render_decoded_assertion(
                fn,
                idx,
                encode_args,
                ret_assert,
                decoded_type,
                [
                    "address ownerWord = alice;",
                    f"vm.store(target, {owner_slot_expr}, bytes32(uint256(uint160(ownerWord))));",
                    f"{decoded_type} expected = {expected_expr};",
                    f"vm.store(target, {result_slot_expr}, {_storage_word_expr(fn.return_type, 'expected')});",
                ],
                f"{decoded_type} actual = abi.decode(ret, ({decoded_type}));",
                [f'assertEq(actual, expected, "{fn.name} should decode the configured secondary mapping value");'],
                f"{fn.name} decodes the configured secondary mapping value after the existence precondition",
                "DecodesConfiguredSecondaryMapping",
            )

    straight_line = _infer_straight_line_non_unit_test(
        contract,
        fn,
        idx,
        encode_args,
        decoded_type,
        param_examples,
        param_types,
        constructor_examples,
    )
    if straight_line is not None:
        return straight_line

    return None


def render_contract_test(contract: ContractDecl) -> str:
    tests: list[str] = []
    need_uint_array_helper = False
    need_address_array_helper = False
    need_bool_array_helper = False
    need_bytes32_array_helper = False
    set_up_line = f'target = deployYul("{contract.name}");'
    if contract.constructor is not None and contract.constructor.params:
        constructor_args = [_example_value(p.lean_type) for p in contract.constructor.params]
        for p in contract.constructor.params:
            p_ty = _normalize_type(p.lean_type)
            if p_ty == "Array Uint256":
                need_uint_array_helper = True
            if p_ty == "Array Address":
                need_address_array_helper = True
            if p_ty == "Array Bool":
                need_bool_array_helper = True
            if p_ty == "Array Bytes32":
                need_bytes32_array_helper = True
        set_up_line = (
            f'target = deployYulWithArgs("{contract.name}", abi.encode('
            + ", ".join(constructor_args)
            + "));"
        )

    for idx, fn in enumerate(contract.functions, start=1):
        sig = _sol_signature(fn)
        call_args = [_example_value(p.lean_type) for p in fn.params]
        for p in fn.params:
            p_ty = _normalize_type(p.lean_type)
            if p_ty == "Array Uint256":
                need_uint_array_helper = True
            if p_ty == "Array Address":
                need_address_array_helper = True
            if p_ty == "Array Bool":
                need_bool_array_helper = True
            if p_ty == "Array Bytes32":
                need_bytes32_array_helper = True

        encode_args = ", ".join([f'"{sig}"', *call_args]) if call_args else f'"{sig}"'
        fn_camel = _fn_camel(fn.name)

        if _normalize_type(fn.return_type) == "Unit":
            body = f"""    // Property {idx}: {fn.name} has no unexpected revert
    function testAuto_{fn_camel}_NoUnexpectedRevert() public {{
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature({encode_args}));
        require(ok, \"{fn.name} reverted unexpectedly\");
    }}
"""
        else:
            body = _render_inferred_non_unit_test(contract, fn, idx, encode_args)
            if body is None:
                ret_assert = _return_shape_assertion(fn.return_type, fn.name)
                body = f"""    // Property {idx}: TODO decode and assert `{fn.name}` result
    function testTODO_{fn_camel}_DecodeAndAssert() public {{
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature({encode_args}));
        require(ok, \"{fn.name} reverted unexpectedly\");
{ret_assert}
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }}
"""
        tests.append(body)

    helper = ""
    if need_uint_array_helper:
        helper += """
    function _singletonUintArray(uint256 x) internal pure returns (uint256[] memory arr) {
        arr = new uint256[](1);
        arr[0] = x;
    }
"""
    if need_address_array_helper:
        helper += """
    function _singletonAddressArray(address x) internal pure returns (address[] memory arr) {
        arr = new address[](1);
        arr[0] = x;
    }
"""
    if need_bool_array_helper:
        helper += """
    function _singletonBoolArray(bool x) internal pure returns (bool[] memory arr) {
        arr = new bool[](1);
        arr[0] = x;
    }
"""
    if need_bytes32_array_helper:
        helper += """
    function _singletonBytes32Array(bytes32 x) internal pure returns (bytes32[] memory arr) {
        arr = new bytes32[](1);
        arr[0] = x;
    }
"""

    return f"""// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title Property{contract.name}Test
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: {contract.source.relative_to(ROOT)}
 */
contract Property{contract.name}Test is YulTestBase {{
    address target;
    address alice = address(0x1111);

    function setUp() public {{
        {set_up_line}
        require(target != address(0), "Deploy failed");
    }}

{''.join(tests)}{helper}}}
"""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Property*.t.sol baseline tests from verity_contract declarations."
    )
    parser.add_argument(
        "--source",
        action="append",
        default=[],
        help=(
            "Lean source path to scan (relative to repo root). "
            "Repeat flag for multiple files. Defaults to Contracts/**/*.lean."
        ),
    )
    parser.add_argument(
        "--contract",
        action="append",
        default=[],
        help="Only generate for the named contract (repeatable). Defaults to all discovered contracts.",
    )
    parser.add_argument(
        "--output-dir",
        default="test/generated",
        help="Output directory for generated Property*.t.sol files (default: test/generated).",
    )
    parser.add_argument(
        "--stdout",
        action="store_true",
        help="Print generated file content to stdout instead of writing files.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.source:
        paths = [ROOT / p for p in args.source]
    else:
        macro_dir = ROOT / "Contracts"
        paths = discover_macro_contract_sources(macro_dir)
        if not paths:
            raise SystemExit(f"no Lean files found in {macro_dir}")

    missing_sources = [str(p) for p in paths if not p.exists()]
    if missing_sources:
        raise SystemExit(f"source file(s) not found: {', '.join(missing_sources)}")

    contracts = collect_contracts(paths)
    if not contracts:
        raise SystemExit("no verity_contract declarations found")

    selected_names = args.contract or sorted(contracts.keys())
    unknown = [name for name in selected_names if name not in contracts]
    if unknown:
        known = ", ".join(sorted(contracts.keys()))
        raise SystemExit(f"unknown contract(s): {', '.join(unknown)}; known: {known}")

    output_dir = ROOT / args.output_dir
    if not args.stdout:
        output_dir.mkdir(parents=True, exist_ok=True)

    generated = 0
    for name in selected_names:
        rendered = render_contract_test(contracts[name])
        filename = f"Property{name}.t.sol"
        if args.stdout:
            print(f"// ===== {filename} =====")
            print(rendered)
        else:
            (output_dir / filename).write_text(rendered, encoding="utf-8")
        generated += 1

    if not args.stdout:
        print(f"Generated {generated} file(s) in {output_dir.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
