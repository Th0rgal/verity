#!/usr/bin/env python3
"""Validate storage layout consistency across EDSL, Spec, Compiler, and AST layers.

Extracts storage slot definitions from:
1. EDSL layer:     Verity/Examples/*.lean  (StorageSlot definitions)
2. Spec layer:     Verity/Specs/*/Spec.lean (StorageSlot definitions)
3. Compiler layer: Compiler/Specs.lean            (ContractSpec field lists)

Checks:
- No intra-contract slot collisions within any layer
- Cross-layer consistency: EDSL slots match Compiler slot assignments
- Spec layer duplications match EDSL definitions
- AST layer slot/type usage matches Compiler slot assignments
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import ROOT, strip_lean_comments

# Regex for EDSL/Spec StorageSlot definitions:
#   def <name> : StorageSlot <type> := ⟨<slot>⟩
STORAGE_SLOT_RE = re.compile(
    r"def\s+(\w+)\s*:\s*StorageSlot\s+(.+?)\s*:=\s*⟨(\d+)⟩"
)

# Regex for Compiler fields list entries:
#   { name := "<name>", ty := FieldType.<type> }
#   { name := "<name>", ty := FieldType.mappingTyped (.simple .address) }
#   { name := "<name>", ty := FieldType.mappingTyped (.nested .address .address) }
COMPILER_FIELD_RE = re.compile(
    r'\{\s*name\s*:=\s*"(\w+)"\s*,\s*ty\s*:=\s*FieldType\.([\w.() ]+?)\s*\}'
)

# Regex for ContractSpec name:
#   name := "<name>"
SPEC_NAME_RE = re.compile(r'name\s*:=\s*"(\w+)"')
AST_SPEC_FILE = ROOT / "Compiler" / "ASTSpecs.lean"

# Regex for Lean namespace:
#   namespace <name>
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)", re.MULTILINE)

# AST slot references in Verity/AST/*.lean:
#   .storage <slot>, .sstore <slot>, .storageAddr <slot>, .sstoreAddr <slot>
#   .mapping <slot>, .mstore <slot>
AST_UINT_SLOT_RE = re.compile(r"\.(?:storage|sstore)\s+(\d+)\b")
AST_ADDR_SLOT_RE = re.compile(r"\.(?:storageAddr|sstoreAddr)\s+(\d+)\b")
AST_MAPPING_SLOT_RE = re.compile(r"\.(?:mapping|mstore)\s+(\d+)\b")

# Spec slot references in Verity/Specs/*/Spec.lean:
#   s.storage <slot>, s'.storage <slot>
#   s.storageAddr <slot>, s'.storageAddr <slot>
#   s.storageMap <slot> <addr>, s'.storageMap <slot> <addr>
SPEC_UINT_SLOT_RE = re.compile(r"\bs'?\.(?:storage)\s+(\d+)\b")
SPEC_ADDR_SLOT_RE = re.compile(r"\bs'?\.(?:storageAddr)\s+(\d+)\b")
SPEC_MAPPING_SLOT_RE = re.compile(r"\bs'?\.(?:storageMap)\s+(\d+)\b")
SPEC_MAPPING_UINT_SLOT_RE = re.compile(r"\bs'?\.(?:storageMapUint)\s+(\d+)\b")
SPEC_MAPPING2_SLOT_RE = re.compile(r"\bs'?\.(?:storageMap2)\s+(\d+)\b")


def find_matching(text: str, start: int, open_ch: str, close_ch: str) -> int:
    """Return index of matching close delimiter starting at `start`."""
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


def iter_braced_blocks(text: str, header_pattern: re.Pattern[str]) -> list[str]:
    """Return braced block bodies following header matches in source text."""
    blocks: list[str] = []
    for match in header_pattern.finditer(text):
        body_start = match.end() - 1  # points at opening "{"
        body_end = find_matching(text, body_start, "{", "}")
        if body_end == -1:
            continue
        blocks.append(text[body_start + 1 : body_end])
    return blocks


def extract_edsl_slots(filepath: Path) -> dict[str, list[tuple[str, str, int]]]:
    """Extract StorageSlot definitions from a Lean file.

    Returns dict mapping namespace/contract to list of (name, type, slot_number).
    """
    content = strip_lean_comments(filepath.read_text())
    namespace = filepath.stem  # fallback to filename
    for m in NAMESPACE_RE.finditer(content):
        # Use the last component of the namespace
        ns = m.group(1)
        namespace = ns.split(".")[-1]

    slots = []
    for m in STORAGE_SLOT_RE.finditer(content):
        name, ty, slot_num = m.group(1), m.group(2).strip(), int(m.group(3))
        slots.append((name, ty, slot_num))

    if slots:
        return {namespace: slots}
    return {}


def extract_compiler_specs(filepath: Path) -> dict[str, list[tuple[str, str, int]]]:
    """Extract ContractSpec field definitions from Compiler/Specs.lean.

    Fields get automatic slot assignment based on list order (index-based).
    Returns dict mapping contract name to list of (name, type, slot_number).
    """
    content = strip_lean_comments(filepath.read_text())
    specs: dict[str, list[tuple[str, str, int]]] = {}

    spec_header_pattern = re.compile(
        r"def\s+\w+\s*:\s*ContractSpec\s*:=\s*\{"
    )
    for block in iter_braced_blocks(content, spec_header_pattern):

        # Extract contract name
        name_match = SPEC_NAME_RE.search(block)
        if not name_match:
            continue
        contract_name = name_match.group(1)

        # Extract fields in order
        fields = []
        for idx, field_match in enumerate(COMPILER_FIELD_RE.finditer(block)):
            # Only take fields before the first function definition
            field_pos = field_match.start()
            # Check if we've passed the fields section
            functions_marker = block.find("functions :=")
            constructor_marker = block.find("constructor :=")
            # Fields come before constructor and functions
            if functions_marker != -1 and field_pos > functions_marker:
                continue
            if constructor_marker != -1 and field_pos > constructor_marker:
                continue

            field_name = field_match.group(1)
            field_type = field_match.group(2)
            fields.append((field_name, field_type, idx))

        if fields:
            specs[contract_name] = fields

    return specs


def extract_compiler_externals(filepath: Path) -> dict[str, bool]:
    """Extract whether each ContractSpec has non-empty externals."""
    content = strip_lean_comments(filepath.read_text())
    externals: dict[str, bool] = {}

    spec_header_pattern = re.compile(
        r"def\s+\w+\s*:\s*ContractSpec\s*:=\s*\{"
    )
    for block in iter_braced_blocks(content, spec_header_pattern):
        name_match = SPEC_NAME_RE.search(block)
        if not name_match:
            continue
        contract_name = name_match.group(1)

        ext_match = re.search(r"externals\s*:=\s*\[", block)
        if not ext_match:
            externals[contract_name] = False
            continue

        list_start = ext_match.end() - 1
        list_end = find_matching(block, list_start, "[", "]")
        if list_end == -1:
            externals[contract_name] = False
            continue

        ext_body = block[list_start + 1 : list_end].strip()
        externals[contract_name] = bool(ext_body)

    return externals


def extract_ast_contract_names(filepath: Path) -> set[str]:
    """Extract contract names from Compiler/ASTSpecs.lean ASTContractSpec blocks."""
    if not filepath.exists():
        return set()

    content = strip_lean_comments(filepath.read_text())
    names: set[str] = set()
    spec_header_pattern = re.compile(
        r"def\s+\w+Spec\s*:\s*ASTContractSpec\s*:=\s*\{"
    )
    for block in iter_braced_blocks(content, spec_header_pattern):
        name_match = SPEC_NAME_RE.search(block)
        if name_match:
            names.add(name_match.group(1))
    return names


def check_ast_spec_coverage(
    compiler: dict[str, list[tuple[str, str, int]]],
    compiler_externals: dict[str, bool],
    ast_contracts: set[str],
) -> list[str]:
    """Ensure ASTSpecs covers all non-external ContractSpec contracts."""
    errors: list[str] = []
    for contract in sorted(compiler.keys()):
        if compiler_externals.get(contract, False):
            continue
        if contract not in ast_contracts:
            errors.append(
                f"AST-Compiler: {contract} in Compiler/Specs but missing from Compiler/ASTSpecs"
            )
    for contract in sorted(ast_contracts):
        if contract not in compiler:
            errors.append(
                f"AST-Compiler: {contract} in Compiler/ASTSpecs but missing from Compiler/Specs"
            )
    return errors


def extract_ast_slots(
    filepath: Path,
) -> tuple[list[tuple[str, str, int]], list[str]]:
    """Extract slot/type usage from a Verity AST file.

    Returns:
      - list of (name, type, slot_number) where name is synthetic "slot<N>"
      - list of consistency errors found inside the AST file itself
    """
    content = strip_lean_comments(filepath.read_text())
    contract = filepath.stem

    by_slot: dict[int, set[str]] = {}
    for m in AST_UINT_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("uint256")
    for m in AST_ADDR_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("address")
    for m in AST_MAPPING_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("mapping")

    entries: list[tuple[str, str, int]] = []
    errors: list[str] = []
    for slot in sorted(by_slot.keys()):
        kinds = by_slot[slot]
        if len(kinds) > 1:
            errors.append(
                f"[AST] {contract}: slot {slot} used with multiple kinds: {sorted(kinds)}"
            )
        kind = sorted(kinds)[0]
        entries.append((f"slot{slot}", kind, slot))
    return entries, errors


def extract_spec_slots(
    filepath: Path,
) -> tuple[list[tuple[str, str, int]], list[str]]:
    """Extract literal slot/type usage from a Spec.lean file.

    Returns:
      - list of (name, type, slot_number) where name is synthetic "slot<N>"
      - list of consistency errors found inside the spec file itself
    """
    content = strip_lean_comments(filepath.read_text())
    contract = filepath.parent.name

    by_slot: dict[int, set[str]] = {}
    for m in SPEC_UINT_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("uint256")
    for m in SPEC_ADDR_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("address")
    for m in SPEC_MAPPING_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("mapping")
    for m in SPEC_MAPPING_UINT_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("mapping_uint")
    for m in SPEC_MAPPING2_SLOT_RE.finditer(content):
        by_slot.setdefault(int(m.group(1)), set()).add("mapping2")

    entries: list[tuple[str, str, int]] = []
    errors: list[str] = []
    for slot in sorted(by_slot.keys()):
        kinds = by_slot[slot]
        if len(kinds) > 1:
            errors.append(
                f"[Spec] {contract}: slot {slot} used with multiple kinds: {sorted(kinds)}"
            )
        kind = sorted(kinds)[0]
        entries.append((f"slot{slot}", kind, slot))
    return entries, errors


def normalize_type(ty: str) -> str:
    """Normalize type names for comparison across layers."""
    raw = ty.strip()
    # Strip balanced outer parentheses for EDSL types like "(Address → Uint256)"
    stripped = raw
    if stripped.startswith("(") and stripped.endswith(")"):
        stripped = stripped[1:-1].strip()
    mapping = {
        # EDSL types (from StorageSlot definitions)
        "Uint256": "uint256",
        "Address": "address",
        "Address → Uint256": "mapping",
        "Uint256 → Uint256": "mapping_uint",
        "Address → Address → Uint256": "mapping2",
        # Compiler types (from FieldType variants)
        "mapping": "mapping",
        "mappingTyped (.simple .address)": "mapping",
        "mappingTyped (.simple .uint256)": "mapping_uint",
        "mappingTyped (.nested .address .address)": "mapping2",
        "mappingTyped (.nested .address .uint256)": "mapping2",
        "mappingTyped (.nested .uint256 .address)": "mapping2",
        "mappingTyped (.nested .uint256 .uint256)": "mapping2",
    }
    # Try raw first (for Compiler types like "mappingTyped (...)"), then stripped
    return mapping.get(raw, mapping.get(stripped, stripped.lower()))


def check_intra_collisions(
    contract: str, slots: list[tuple[str, str, int]], layer: str
) -> list[str]:
    """Check for slot number collisions within a single contract."""
    errors = []
    slot_map: dict[int, str] = {}
    for name, _ty, slot_num in slots:
        if slot_num in slot_map:
            errors.append(
                f"[{layer}] {contract}: Slot {slot_num} collision between "
                f"'{slot_map[slot_num]}' and '{name}'"
            )
        else:
            slot_map[slot_num] = name
    return errors


def check_layer_consistency(
    reference: dict[str, list[tuple[str, str, int]]],
    subject: dict[str, list[tuple[str, str, int]]],
    label: str,
    ref_label: str = "EDSL",
    subj_label: str = "",
    check_reverse: bool = False,
) -> list[str]:
    """Check that subject layer fields match reference layer definitions.

    Args:
        reference: The authoritative layer (e.g. EDSL).
        subject: The layer to validate against reference.
        label: Prefix for error messages (e.g. "Cross-layer", "Spec-EDSL").
        ref_label: Display name for the reference layer.
        subj_label: Display name for the subject layer.
        check_reverse: If True, also report reference fields missing from subject.
    """
    errors = []

    for contract, subj_fields in subject.items():
        if contract not in reference:
            if check_reverse:
                # Compiler specs may lack EDSL implementations (e.g. unverified demos)
                continue
            errors.append(
                f"{label}: {contract} has {subj_label} slots but no matching {ref_label} contract"
            )
            continue

        ref_fields = reference[contract]
        ref_map = {name: (ty, slot) for name, ty, slot in ref_fields}
        subj_map = {name: (ty, slot) for name, ty, slot in subj_fields}

        for name, (s_ty, s_slot) in subj_map.items():
            if name not in ref_map:
                errors.append(
                    f"{label}: {contract}.{name} in {subj_label} but not in {ref_label}"
                )
                continue

            r_ty, r_slot = ref_map[name]
            if s_slot != r_slot:
                errors.append(
                    f"{label}: {contract}.{name} slot mismatch: "
                    f"{ref_label}={r_slot}, {subj_label}={s_slot}"
                )
            if normalize_type(r_ty) != normalize_type(s_ty):
                errors.append(
                    f"{label}: {contract}.{name} type mismatch: "
                    f"{ref_label}={r_ty}, {subj_label}={s_ty}"
                )

        if check_reverse:
            for name in ref_map:
                if name not in subj_map:
                    errors.append(
                        f"{label}: {contract}.{name} in {ref_label} but not in {subj_label}"
                    )

    return errors


def check_spec_edsl_consistency(
    edsl: dict[str, list[tuple[str, str, int]]],
    spec: dict[str, list[tuple[str, str, int]]],
    compiler: dict[str, list[tuple[str, str, int]]],
    compiler_externals: dict[str, bool],
) -> list[str]:
    """Check Spec slot/type usage matches EDSL for compiled non-external contracts."""
    errors: list[str] = []

    required_contracts = sorted(
        c for c in compiler.keys() if not compiler_externals.get(c, False)
    )
    for contract in required_contracts:
        if contract not in edsl:
            errors.append(
                f"Spec-EDSL: {contract} in Compiler but missing from Verity/Examples"
            )
            continue
        if contract not in spec:
            errors.append(
                f"Spec-EDSL: {contract} in Compiler but missing Spec.lean slot usage"
            )
            continue

        edsl_slots = {(slot, normalize_type(ty)) for _name, ty, slot in edsl[contract]}
        spec_slots = {(slot, normalize_type(ty)) for _name, ty, slot in spec[contract]}

        for slot, ty in sorted(spec_slots):
            if (slot, ty) not in edsl_slots:
                errors.append(
                    f"Spec-EDSL: {contract}.slot{slot} ({ty}) in Spec but not in EDSL"
                )
        for slot, ty in sorted(edsl_slots):
            if (slot, ty) not in spec_slots:
                errors.append(
                    f"Spec-EDSL: {contract}.slot{slot} ({ty}) in EDSL but not in Spec"
                )

    return errors


def check_ast_compiler_consistency(
    ast: dict[str, list[tuple[str, str, int]]],
    compiler: dict[str, list[tuple[str, str, int]]],
) -> list[str]:
    """Check that AST slot usage matches Compiler slot assignments by slot number."""
    errors: list[str] = []
    for contract, ast_fields in ast.items():
        if contract not in compiler:
            errors.append(
                f"AST-Compiler: {contract} has AST slots but no matching Compiler contract"
            )
            continue

        ast_by_slot = {slot: ty for _name, ty, slot in ast_fields}
        comp_by_slot = {slot: (name, ty) for name, ty, slot in compiler[contract]}

        for slot, ast_ty in ast_by_slot.items():
            if slot not in comp_by_slot:
                errors.append(
                    f"AST-Compiler: {contract}.slot{slot} in AST but missing in Compiler"
                )
                continue
            comp_name, comp_ty = comp_by_slot[slot]
            if normalize_type(ast_ty) != normalize_type(comp_ty):
                errors.append(
                    f"AST-Compiler: {contract}.slot{slot} type mismatch: "
                    f"AST={ast_ty}, Compiler={comp_ty} (field '{comp_name}')"
                )

        for slot, (comp_name, _comp_ty) in comp_by_slot.items():
            if slot not in ast_by_slot:
                errors.append(
                    f"AST-Compiler: {contract}.{comp_name} (slot {slot}) in Compiler "
                    f"but not referenced in AST"
                )

    return errors


def generate_report(
    edsl: dict[str, list[tuple[str, str, int]]],
    compiler: dict[str, list[tuple[str, str, int]]],
    ast: dict[str, list[tuple[str, str, int]]] | None = None,
    fmt: str = "text",
) -> str:
    """Generate a storage layout report."""
    lines = []

    if fmt == "markdown":
        lines.append("## Storage Layout Report")
        lines.append("")
        ast = ast or {}
        all_contracts = sorted(set(list(edsl.keys()) + list(compiler.keys()) + list(ast.keys())))
        for contract in all_contracts:
            lines.append(f"### {contract}")
            lines.append("")
            lines.append("| Slot | Field | Type | Layers |")
            lines.append("|------|-------|------|--------|")

            edsl_fields = {
                name: (ty, slot) for name, ty, slot in edsl.get(contract, [])
            }
            compiler_fields = {
                name: (ty, slot) for name, ty, slot in compiler.get(contract, [])
            }
            ast_fields = {
                name: (ty, slot) for name, ty, slot in ast.get(contract, [])
            }
            all_fields = sorted(
                set(list(edsl_fields.keys()) + list(compiler_fields.keys()) + list(ast_fields.keys())),
                key=lambda n: edsl_fields.get(n, compiler_fields.get(n, ("", 99)))[1],
            )

            for name in all_fields:
                layers = []
                slot = "?"
                ty = "?"
                if name in edsl_fields:
                    layers.append("EDSL")
                    ty, slot = edsl_fields[name]
                if name in compiler_fields:
                    layers.append("Compiler")
                    if slot == "?":
                        ty, slot = compiler_fields[name]
                if name in ast_fields:
                    layers.append("AST")
                    if slot == "?":
                        ty, slot = ast_fields[name]
                lines.append(
                    f"| {slot} | `{name}` | `{ty}` | {', '.join(layers)} |"
                )

            lines.append("")
    else:
        lines.append("=" * 60)
        lines.append("STORAGE LAYOUT REPORT")
        lines.append("=" * 60)
        ast = ast or {}
        all_contracts = sorted(set(list(edsl.keys()) + list(compiler.keys()) + list(ast.keys())))
        for contract in all_contracts:
            lines.append("")
            lines.append(f"  {contract}")
            edsl_slots = edsl.get(contract, [])
            for name, ty, slot in sorted(edsl_slots, key=lambda x: x[2]):
                lines.append(f"    Slot {slot}: {name} ({ty})")
            if not edsl_slots:
                compiler_slots = compiler.get(contract, [])
                for name, ty, slot in sorted(compiler_slots, key=lambda x: x[2]):
                    lines.append(f"    Slot {slot}: {name} ({ty}) [compiler only]")
            ast_slots = ast.get(contract, [])
            if ast_slots:
                for name, ty, slot in sorted(ast_slots, key=lambda x: x[2]):
                    lines.append(f"    Slot {slot}: {name} ({ty}) [ast]")

    return "\n".join(lines)


def main():
    errors: list[str] = []

    # 1. Extract EDSL slots from Examples (use filename as contract name)
    edsl_all: dict[str, list[tuple[str, str, int]]] = {}
    examples_dir = ROOT / "Verity" / "Examples"
    for lean_file in sorted(examples_dir.glob("*.lean")):
        result = extract_edsl_slots(lean_file)
        # Use filename stem as contract name (more reliable than namespace)
        for _key, slots in result.items():
            if slots:
                edsl_all[lean_file.stem] = slots

    # 2. Extract Spec slots from literal state accesses in Spec.lean files
    spec_all: dict[str, list[tuple[str, str, int]]] = {}
    specs_dir = ROOT / "Verity" / "Specs"
    for spec_file in sorted(specs_dir.glob("*/Spec.lean")):
        contract_name = spec_file.parent.name
        slots, spec_errors = extract_spec_slots(spec_file)
        errors.extend(spec_errors)
        if slots:
            spec_all[contract_name] = slots

    # 3. Extract Compiler specs
    compiler_specs_file = ROOT / "Compiler" / "Specs.lean"
    compiler_all: dict[str, list[tuple[str, str, int]]] = {}
    if compiler_specs_file.exists():
        compiler_all = extract_compiler_specs(compiler_specs_file)
    compiler_externals: dict[str, bool] = {}
    if compiler_specs_file.exists():
        compiler_externals = extract_compiler_externals(compiler_specs_file)

    # 4. Extract AST slots for contracts wired in Compiler/ASTSpecs.lean
    ast_all: dict[str, list[tuple[str, str, int]]] = {}
    ast_contracts = extract_ast_contract_names(AST_SPEC_FILE)
    errors.extend(check_ast_spec_coverage(compiler_all, compiler_externals, ast_contracts))
    ast_dir = ROOT / "Verity" / "AST"
    for contract_name in sorted(ast_contracts):
        ast_file = ast_dir / f"{contract_name}.lean"
        if not ast_file.exists():
            errors.append(
                f"[AST] Missing AST file for contract '{contract_name}': {ast_file}"
            )
            continue
        slots, ast_errors = extract_ast_slots(ast_file)
        ast_all[contract_name] = slots
        errors.extend(ast_errors)

    # 5. Check intra-contract collisions (EDSL/Spec/Compiler)
    for contract, slots in edsl_all.items():
        errors.extend(check_intra_collisions(contract, slots, "EDSL"))
    for contract, slots in spec_all.items():
        errors.extend(check_intra_collisions(contract, slots, "Spec"))
    for contract, slots in compiler_all.items():
        errors.extend(check_intra_collisions(contract, slots, "Compiler"))

    # 6. Check cross-layer consistency (EDSL ↔ Compiler)
    errors.extend(check_layer_consistency(
        edsl_all, compiler_all, "Cross-layer",
        ref_label="EDSL", subj_label="Compiler", check_reverse=True,
    ))

    # 7. Check Spec-EDSL consistency (slot/type parity for compiled contracts)
    errors.extend(check_spec_edsl_consistency(
        edsl_all, spec_all, compiler_all, compiler_externals
    ))

    # 8. Check AST-Compiler slot/type consistency
    errors.extend(check_ast_compiler_consistency(ast_all, compiler_all))

    # 9. Report
    fmt = "markdown" if "--format=markdown" in sys.argv else "text"

    if errors:
        print("Storage layout validation FAILED.\n")
        for e in errors:
            print(f"  ERROR: {e}")
        print()
        sys.exit(1)

    print("Storage layout validation passed.\n")
    print(generate_report(edsl_all, compiler_all, ast_all, fmt))


if __name__ == "__main__":
    main()
