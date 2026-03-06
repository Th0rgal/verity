#!/usr/bin/env python3
"""Validate storage layout consistency across EDSL, Spec, and Compiler layers.

Extracts storage slot definitions from:
1. EDSL layer:     Contracts/*/Contract.lean  (StorageSlot definitions)
2. Spec layer:     Contracts/*/Spec.lean      (StorageSlot definitions)
3. Compiler layer: Compiler/Specs.lean        (CompilationModel field lists)

Checks:
- No intra-contract slot collisions within any layer
- Cross-layer consistency: EDSL slots match Compiler slot assignments
- Spec layer duplications match EDSL definitions
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
COMPILER_ALIAS_RE = re.compile(
    r"def\s+(\w+)\s*:\s*CompilationModel\s*:=\s*Contracts\.MacroContracts\.(\w+)\.spec"
)
COMPILER_FILTERED_ALIAS_RE = re.compile(
    r"def\s+(\w+)\s*:\s*CompilationModel\s*:=\s*"
    r"let\s+canonical\s*:=\s*Contracts\.MacroContracts\.(\w+)\.spec\s*"
    r"\{\s*canonical\s+with\s+functions\s*:=\s*canonical\.functions\.filter\s+fun\s+fn\s*=>\s*(.*?)\s*\}",
    re.DOTALL,
)
MACRO_STORAGE_LINE_RE = re.compile(
    r"^\s*(\w+)\s*:\s*(.+?)\s*:=\s*slot\s+(\d+)\s*$", re.MULTILINE
)

# Regex for CompilationModel name:
#   name := "<name>"
SPEC_NAME_RE = re.compile(r'name\s*:=\s*"(\w+)"')

# Regex for Lean namespace:
#   namespace <name>
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)", re.MULTILINE)

# Spec slot references in Contracts/*/Spec.lean:
#   s.storage <slot>, s'.storage <slot>
#   s.storageAddr <slot>, s'.storageAddr <slot>
#   s.storageMap <slot> <addr>, s'.storageMap <slot> <addr>
SPEC_UINT_SLOT_RE = re.compile(r"\bs'?\.(?:storage)\s+(\d+)\b")
SPEC_ADDR_SLOT_RE = re.compile(r"\bs'?\.(?:storageAddr)\s+(\d+)\b")
SPEC_MAPPING_SLOT_RE = re.compile(r"\bs'?\.(?:storageMap)\s+(\d+)\b")
SPEC_MAPPING_UINT_SLOT_RE = re.compile(r"\bs'?\.(?:storageMapUint)\s+(\d+)\b")
SPEC_MAPPING2_SLOT_RE = re.compile(r"\bs'?\.(?:storageMap2)\s+(\d+)\b")
SPEC_HELPER_SLOT_PATTERNS: tuple[tuple[re.Pattern[str], tuple[str, ...]], ...] = (
    (re.compile(r"\bstorageUpdateSpec\s+(\d+)\b"), ("uint256",)),
    (re.compile(r"\bstorageAddrUpdateSpec\s+(\d+)\b"), ("address",)),
    (re.compile(r"\bstorageAddrStorageUpdateSpec\s+(\d+)\s+(\d+)\b"), ("address", "uint256")),
    (re.compile(r"\bstorageAddrStorage2UpdateSpec\s+(\d+)\s+(\d+)\s+(\d+)\b"), ("address", "uint256", "uint256")),
    (re.compile(r"\bstorage2UpdateSpec\s+(\d+)\s+(\d+)\b"), ("uint256", "uint256")),
    (re.compile(r"\bstorageMapUpdateSpec\s+(\d+)\b"), ("mapping",)),
    (re.compile(r"\bstorageMapAndStorageUpdateSpec\s+(\d+)\s+\w+\s+\w+\s+(\d+)\b"), ("mapping", "uint256")),
    (re.compile(r"\bstorageMap2UpdateSpec\s+(\d+)\b"), ("mapping2",)),
)


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


def extract_macro_contract_slots(contract_name: str) -> list[tuple[str, str, int]]:
    """Extract storage field declarations from a `Contracts/MacroContracts/*.lean` file."""
    path = ROOT / "Contracts" / "MacroContracts" / f"{contract_name}.lean"
    if not path.exists():
        return []

    content = strip_lean_comments(path.read_text())
    storage_match = re.search(r"\bstorage\b", content)
    if not storage_match:
        return []

    end_markers = [
        pos
        for pos in (
            content.find("\n  constructor", storage_match.end()),
            content.find("\n  function", storage_match.end()),
            content.find("\nend ", storage_match.end()),
        )
        if pos != -1
    ]
    storage_end = min(end_markers) if end_markers else len(content)
    storage_block = content[storage_match.end() : storage_end]

    fields: list[tuple[str, str, int]] = []
    for m in MACRO_STORAGE_LINE_RE.finditer(storage_block):
        field_name, field_type, slot_num = m.group(1), m.group(2).strip(), int(m.group(3))
        fields.append((field_name, field_type, slot_num))
    return fields


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
    macro_slots = extract_macro_contract_slots(namespace)
    if macro_slots:
        return {
            namespace: [
                (normalize_field_name(name), ty, slot_num)
                for name, ty, slot_num in macro_slots
            ]
        }
    return {}


def extract_compiler_specs(filepath: Path) -> dict[str, list[tuple[str, str, int]]]:
    """Extract CompilationModel field definitions from Compiler/Specs.lean.

    Fields get automatic slot assignment based on list order (index-based).
    Returns dict mapping contract name to list of (name, type, slot_number).
    """
    content = strip_lean_comments(filepath.read_text())
    specs: dict[str, list[tuple[str, str, int]]] = {}

    spec_header_pattern = re.compile(
        r"def\s+\w+\s*:\s*CompilationModel\s*:=\s*\{"
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

    for _def_name, contract_name in COMPILER_ALIAS_RE.findall(content):
        if contract_name in specs:
            continue
        fields = extract_macro_contract_slots(contract_name)
        if fields:
            specs[contract_name] = fields

    for _def_name, contract_name, _filter_body in COMPILER_FILTERED_ALIAS_RE.findall(content):
        if contract_name in specs:
            continue
        fields = extract_macro_contract_slots(contract_name)
        if fields:
            specs[contract_name] = fields

    return specs


def extract_compiler_externals(filepath: Path) -> dict[str, bool]:
    """Extract whether each CompilationModel has non-empty externals."""
    content = strip_lean_comments(filepath.read_text())
    externals: dict[str, bool] = {}

    spec_header_pattern = re.compile(
        r"def\s+\w+\s*:\s*CompilationModel\s*:=\s*\{"
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
    for pattern, kinds in SPEC_HELPER_SLOT_PATTERNS:
        for m in pattern.finditer(content):
            for group_index, kind in enumerate(kinds, start=1):
                by_slot.setdefault(int(m.group(group_index)), set()).add(kind)

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


def normalize_field_name(name: str) -> str:
    """Normalize storage field names across legacy and macro-generated surfaces."""
    return name[:-4] if name.endswith("Slot") else name


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
        ref_map = {normalize_field_name(name): (ty, slot) for name, ty, slot in ref_fields}
        subj_map = {normalize_field_name(name): (ty, slot) for name, ty, slot in subj_fields}

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
                f"Spec-EDSL: {contract} in Compiler but missing from Contracts/"
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

    # 1. Extract EDSL slots from Contracts (use directory name as contract name)
    edsl_all: dict[str, list[tuple[str, str, int]]] = {}
    contracts_dir = ROOT / "Contracts"
    for contract_dir in sorted(contracts_dir.iterdir()):
        if not contract_dir.is_dir():
            continue
        lean_file = contract_dir / "Contract.lean"
        if not lean_file.exists():
            continue
        result = extract_edsl_slots(lean_file)
        # Use directory name as contract name
        for _key, slots in result.items():
            if slots:
                edsl_all[contract_dir.name] = slots

    # 2. Extract Spec slots from literal state accesses in Spec.lean files
    spec_all: dict[str, list[tuple[str, str, int]]] = {}
    for contract_dir in sorted(contracts_dir.iterdir()):
        if not contract_dir.is_dir():
            continue
        spec_file = contract_dir / "Spec.lean"
        if not spec_file.exists():
            continue
        contract_name = contract_dir.name
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

    # 4. Check intra-contract collisions (EDSL/Spec/Compiler)
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

    # 6. Check Spec-EDSL consistency (slot/type parity for compiled contracts)
    errors.extend(check_spec_edsl_consistency(
        edsl_all, spec_all, compiler_all, compiler_externals
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
