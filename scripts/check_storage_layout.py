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

from property_utils import ROOT

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


def extract_edsl_slots(filepath: Path) -> dict[str, list[tuple[str, str, int]]]:
    """Extract StorageSlot definitions from a Lean file.

    Returns dict mapping namespace/contract to list of (name, type, slot_number).
    """
    content = filepath.read_text()
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
    content = filepath.read_text()
    specs: dict[str, list[tuple[str, str, int]]] = {}

    # Split by spec definition
    # Pattern: def <specName> : ContractSpec := {
    spec_pattern = re.compile(
        r"def\s+\w+\s*:\s*ContractSpec\s*:=\s*\{(.*?)\n\}",
        re.DOTALL,
    )

    for spec_match in spec_pattern.finditer(content):
        block = spec_match.group(1)

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


def extract_ast_contract_names(filepath: Path) -> set[str]:
    """Extract contract names from Compiler/ASTSpecs.lean ASTContractSpec blocks."""
    if not filepath.exists():
        return set()

    content = filepath.read_text()
    names: set[str] = set()
    spec_pattern = re.compile(
        r"def\s+\w+Spec\s*:\s*ASTContractSpec\s*:=\s*\{(.*?)\n\}",
        re.DOTALL,
    )
    for spec_match in spec_pattern.finditer(content):
        block = spec_match.group(1)
        name_match = SPEC_NAME_RE.search(block)
        if name_match:
            names.add(name_match.group(1))
    return names


def extract_ast_slots(
    filepath: Path,
) -> tuple[list[tuple[str, str, int]], list[str]]:
    """Extract slot/type usage from a Verity AST file.

    Returns:
      - list of (name, type, slot_number) where name is synthetic "slot<N>"
      - list of consistency errors found inside the AST file itself
    """
    content = filepath.read_text()
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

    # 2. Extract Spec slots (use parent dir name as contract name)
    spec_all: dict[str, list[tuple[str, str, int]]] = {}
    specs_dir = ROOT / "Verity" / "Specs"
    for spec_file in sorted(specs_dir.glob("*/Spec.lean")):
        # Contract name comes from parent directory, not filename
        contract_name = spec_file.parent.name
        result = extract_edsl_slots(spec_file)
        # Re-key using the parent directory name
        for _key, slots in result.items():
            if slots:
                spec_all[contract_name] = slots

    # 3. Extract Compiler specs
    compiler_specs_file = ROOT / "Compiler" / "Specs.lean"
    compiler_all: dict[str, list[tuple[str, str, int]]] = {}
    if compiler_specs_file.exists():
        compiler_all = extract_compiler_specs(compiler_specs_file)

    # 4. Extract AST slots for contracts wired in Compiler/ASTSpecs.lean
    ast_all: dict[str, list[tuple[str, str, int]]] = {}
    ast_contracts = extract_ast_contract_names(AST_SPEC_FILE)
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

    # 7. Check Spec-EDSL consistency
    errors.extend(check_layer_consistency(
        edsl_all, spec_all, "Spec-EDSL",
        ref_label="EDSL", subj_label="Spec",
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
