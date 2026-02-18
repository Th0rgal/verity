#!/usr/bin/env python3
"""Validate storage layout consistency across EDSL, Spec, and Compiler layers.

Extracts storage slot definitions from:
1. EDSL layer:     Verity/Examples/*.lean  (StorageSlot definitions)
2. Spec layer:     Verity/Specs/*/Spec.lean (StorageSlot definitions)
3. Compiler layer: Compiler/Specs.lean            (ContractSpec field lists)

Checks:
- No intra-contract slot collisions within any layer
- Cross-layer consistency: EDSL slots match Compiler slot assignments
- Spec layer duplications match EDSL definitions
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

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

# Regex for Lean namespace:
#   namespace <name>
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)", re.MULTILINE)


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


def generate_report(
    edsl: dict[str, list[tuple[str, str, int]]],
    compiler: dict[str, list[tuple[str, str, int]]],
    fmt: str = "text",
) -> str:
    """Generate a storage layout report."""
    lines = []

    if fmt == "markdown":
        lines.append("## Storage Layout Report")
        lines.append("")
        all_contracts = sorted(set(list(edsl.keys()) + list(compiler.keys())))
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
            all_fields = sorted(
                set(list(edsl_fields.keys()) + list(compiler_fields.keys())),
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
                lines.append(
                    f"| {slot} | `{name}` | `{ty}` | {', '.join(layers)} |"
                )

            lines.append("")
    else:
        lines.append("=" * 60)
        lines.append("STORAGE LAYOUT REPORT")
        lines.append("=" * 60)
        all_contracts = sorted(set(list(edsl.keys()) + list(compiler.keys())))
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

    # 4. Check intra-contract collisions (all layers)
    for contract, slots in edsl_all.items():
        errors.extend(check_intra_collisions(contract, slots, "EDSL"))
    for contract, slots in spec_all.items():
        errors.extend(check_intra_collisions(contract, slots, "Spec"))
    for contract, slots in compiler_all.items():
        errors.extend(check_intra_collisions(contract, slots, "Compiler"))

    # 5. Check cross-layer consistency (EDSL ↔ Compiler)
    errors.extend(check_layer_consistency(
        edsl_all, compiler_all, "Cross-layer",
        ref_label="EDSL", subj_label="Compiler", check_reverse=True,
    ))

    # 6. Check Spec-EDSL consistency
    errors.extend(check_layer_consistency(
        edsl_all, spec_all, "Spec-EDSL",
        ref_label="EDSL", subj_label="Spec",
    ))

    # 7. Report
    fmt = "markdown" if "--format=markdown" in sys.argv else "text"

    if errors:
        print("Storage layout validation FAILED.\n")
        for e in errors:
            print(f"  ERROR: {e}")
        print()
        sys.exit(1)

    print("Storage layout validation passed.\n")
    print(generate_report(edsl_all, compiler_all, fmt))


if __name__ == "__main__":
    main()
