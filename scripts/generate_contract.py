#!/usr/bin/env python3
"""Generate scaffold files for a new DumbContracts contract.

Creates the complete file structure needed to add a new contract:
  - EDSL implementation (DumbContracts/Examples/{Name}.lean)
  - Formal specification (DumbContracts/Specs/{Name}/Spec.lean)
  - State invariants (DumbContracts/Specs/{Name}/Invariants.lean)
  - Basic proofs (DumbContracts/Proofs/{Name}/Basic.lean)
  - Correctness proofs (DumbContracts/Proofs/{Name}/Correctness.lean)
  - Compiler spec entry (printed to stdout for manual insertion)
  - Property tests (test/Property{Name}.t.sol)

Usage:
    python3 scripts/generate_contract.py MyContract
    python3 scripts/generate_contract.py MyContract --fields "value:uint256,owner:address"
    python3 scripts/generate_contract.py MyContract --fields "balances:mapping" --functions "deposit,withdraw,getBalance"
    python3 scripts/generate_contract.py MyContract --dry-run
"""

from __future__ import annotations

import argparse
import os
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import List

ROOT = Path(__file__).resolve().parent.parent


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

@dataclass
class Field:
    name: str
    ty: str  # "uint256", "address", "mapping"

    @property
    def lean_type(self) -> str:
        if self.ty == "uint256":
            return "Uint256"
        if self.ty == "address":
            return "Address"
        if self.ty == "mapping":
            return "Uint256"  # mapping storage uses storageMap
        return "Uint256"

    @property
    def is_mapping(self) -> bool:
        return self.ty == "mapping"

    @property
    def storage_kind(self) -> str:
        if self.ty == "address":
            return "StorageSlot Address"
        if self.ty == "mapping":
            return "Nat"  # mapping slot is just a Nat
        return "StorageSlot Uint256"


@dataclass
class Function:
    name: str


@dataclass
class ContractConfig:
    name: str
    fields: List[Field]
    functions: List[Function]


# ---------------------------------------------------------------------------
# Parsers
# ---------------------------------------------------------------------------

def parse_fields(spec: str) -> List[Field]:
    """Parse 'name:type,name:type,...' into Field list."""
    if not spec:
        return [Field("storedData", "uint256")]
    fields = []
    for part in spec.split(","):
        part = part.strip()
        if ":" in part:
            name, ty = part.split(":", 1)
            ty = ty.strip().lower()
            if ty not in ("uint256", "address", "mapping"):
                print(f"Warning: Unknown type '{ty}', defaulting to uint256", file=sys.stderr)
                ty = "uint256"
            fields.append(Field(name.strip(), ty))
        else:
            fields.append(Field(part.strip(), "uint256"))
    return fields


def parse_functions(spec: str, fields: List[Field]) -> List[Function]:
    """Parse 'func1,func2,...' or generate defaults from fields."""
    if spec:
        return [Function(f.strip()) for f in spec.split(",") if f.strip()]
    # Default: generate getter/setter for first field
    if fields:
        f = fields[0]
        setter = f"set{f.name[0].upper()}{f.name[1:]}"
        getter = f"get{f.name[0].upper()}{f.name[1:]}"
        return [Function(setter), Function(getter)]
    return [Function("setValue"), Function("getValue")]


# ---------------------------------------------------------------------------
# Template generators
# ---------------------------------------------------------------------------

def gen_example(cfg: ContractConfig) -> str:
    """Generate DumbContracts/Examples/{Name}.lean"""
    has_mapping = any(f.is_mapping for f in cfg.fields)

    imports = ["import DumbContracts.Core"]
    if has_mapping or len(cfg.fields) > 1:
        imports.append("import DumbContracts.EVM.Uint256")

    opens = ["open DumbContracts"]
    if has_mapping or len(cfg.fields) > 1:
        opens.append("open DumbContracts.EVM.Uint256")

    # Storage definitions
    storage_lines = []
    for i, f in enumerate(cfg.fields):
        if f.is_mapping:
            storage_lines.append(f"def {f.name}Slot : Nat := {i}")
        elif f.ty == "address":
            storage_lines.append(f"def {f.name} : StorageSlot Address := ⟨{i}⟩")
        else:
            storage_lines.append(f"def {f.name} : StorageSlot Uint256 := ⟨{i}⟩")

    # Function stubs
    func_lines = []
    for fn in cfg.functions:
        func_lines.append(f"-- TODO: Implement {fn.name}")
        func_lines.append(f"def {fn.name} : Contract Unit := do")
        func_lines.append(f"  pure ()")
        func_lines.append("")

    return f"""/-
  {cfg.name}: Contract Implementation

  This contract demonstrates:
  - {', '.join(f.name + ' (' + f.ty + ')' for f in cfg.fields)}

  TODO: Add contract description
-/

{chr(10).join(imports)}

namespace DumbContracts.Examples.{cfg.name}

{chr(10).join(opens)}

-- Storage layout
{chr(10).join(storage_lines)}

{chr(10).join(func_lines)}
end DumbContracts.Examples.{cfg.name}
"""


def gen_spec(cfg: ContractConfig) -> str:
    """Generate DumbContracts/Specs/{Name}/Spec.lean"""
    spec_defs = []
    for fn in cfg.functions:
        spec_defs.append(f"-- What {fn.name} should do")
        spec_defs.append(f"def {fn.name}_spec (s s' : ContractState) : Prop :=")
        spec_defs.append(f"  -- TODO: Define specification")
        spec_defs.append(f"  True")
        spec_defs.append("")

    return f"""/-
  {cfg.name}: Formal Specification

  This file defines the formal specification of what {cfg.name}
  should do, separate from how it's implemented.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common

namespace DumbContracts.Specs.{cfg.name}

open DumbContracts

{chr(10).join(spec_defs)}
end DumbContracts.Specs.{cfg.name}
"""


def gen_invariants(cfg: ContractConfig) -> str:
    """Generate DumbContracts/Specs/{Name}/Invariants.lean"""
    # Build isolation predicates based on fields
    # Address fields use storageAddr, uint256 fields use storage
    slot_isolation = []
    for i, f in enumerate(cfg.fields):
        if f.is_mapping:
            continue
        if f.ty == "address":
            slot_isolation.append(
                f"-- Address storage slot isolation for {f.name} (slot {i})\n"
                f"def {f.name}_isolated (s s' : ContractState) (slot : Nat) : Prop :=\n"
                f"  slot ≠ {i} → s'.storageAddr slot = s.storageAddr slot"
            )
        else:
            slot_isolation.append(
                f"-- Storage slot isolation for {f.name} (slot {i})\n"
                f"def {f.name}_isolated (s s' : ContractState) (slot : Nat) : Prop :=\n"
                f"  slot ≠ {i} → s'.storage slot = s.storage slot"
            )

    return f"""/-
  {cfg.name}: State Invariants

  This file defines properties that should hold for all valid
  ContractState instances used with {cfg.name}.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common

namespace DumbContracts.Specs.{cfg.name}

open DumbContracts

-- Basic well-formedness of ContractState
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""

{chr(10).join(slot_isolation) if slot_isolation else "-- TODO: Add state invariants"}

-- Context preservation: operations don't change sender/address
abbrev context_preserved := Specs.sameContext

end DumbContracts.Specs.{cfg.name}
"""


def gen_basic_proofs(cfg: ContractConfig) -> str:
    """Generate DumbContracts/Proofs/{Name}/Basic.lean"""
    proof_stubs = []
    for fn in cfg.functions:
        proof_stubs.append(f"-- TODO: Prove {fn.name} meets its specification")
        proof_stubs.append(f"theorem {fn.name}_meets_spec (s : ContractState) :")
        proof_stubs.append(f"  let s' := (({fn.name}).run s).snd")
        proof_stubs.append(f"  {fn.name}_spec s s' := by")
        proof_stubs.append(f"  sorry")
        proof_stubs.append("")

    return f"""/-
  {cfg.name}: Basic Correctness Proofs

  This file contains proofs of basic correctness properties for {cfg.name}.

  Status: Scaffold — proofs need implementation.
-/

import DumbContracts.Core
import DumbContracts.Examples.{cfg.name}
import DumbContracts.Specs.{cfg.name}.Spec
import DumbContracts.Specs.{cfg.name}.Invariants

namespace DumbContracts.Proofs.{cfg.name}

open DumbContracts
open DumbContracts.Examples.{cfg.name}
open DumbContracts.Specs.{cfg.name}

{chr(10).join(proof_stubs)}
end DumbContracts.Proofs.{cfg.name}
"""


def gen_correctness_proofs(cfg: ContractConfig) -> str:
    """Generate DumbContracts/Proofs/{Name}/Correctness.lean"""
    return f"""/-
  {cfg.name}: Advanced Correctness Proofs

  Proves deeper properties beyond Basic.lean:
  - Invariant preservation
  - State isolation
  - Well-formedness preservation

  Status: Scaffold — proofs need implementation.
-/

import DumbContracts.Core
import DumbContracts.Examples.{cfg.name}
import DumbContracts.Specs.{cfg.name}.Spec
import DumbContracts.Specs.{cfg.name}.Invariants
import DumbContracts.Proofs.{cfg.name}.Basic

namespace DumbContracts.Proofs.{cfg.name}.Correctness

open DumbContracts
open DumbContracts.Examples.{cfg.name}
open DumbContracts.Specs.{cfg.name}
open DumbContracts.Proofs.{cfg.name}

-- TODO: Add advanced correctness proofs
-- See DumbContracts/Proofs/SimpleStorage/Correctness.lean for reference

end DumbContracts.Proofs.{cfg.name}.Correctness
"""


def gen_property_tests(cfg: ContractConfig) -> str:
    """Generate test/Property{Name}.t.sol"""
    test_functions = []
    for i, fn in enumerate(cfg.functions):
        camel = fn.name[0].upper() + fn.name[1:]
        test_functions.append(f"""    /**
     * Property {i + 1}: {fn.name}_meets_spec
     * Theorem: {fn.name}() meets its formal specification
     */
    /// Property: {fn.name}_meets_spec
    function testProperty_{camel}_MeetsSpec() public {{
        // TODO: Implement property test
        // See PropertySimpleStorage.t.sol for reference
    }}
""")

    theorem_list = "\n".join(
        f" * {i + 1}. {fn.name}_meets_spec"
        for i, fn in enumerate(cfg.functions)
    )

    return f"""// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title Property{cfg.name}Test
 * @notice Property-based tests extracted from formally verified Lean theorems
 * @dev Maps theorems from DumbContracts/Proofs/{cfg.name}/ to executable tests
 *
 * This file contains property tests corresponding to proven theorems:
 *
 * From Basic.lean:
{theorem_list}
 */
contract Property{cfg.name}Test is YulTestBase {{
    address target;

    function setUp() public {{
        target = deployYul("{cfg.name}");
        require(target != address(0), "Deploy failed");
    }}

{chr(10).join(test_functions)}
    // Helper function to read storage
    function readStorage(uint256 slot) internal view returns (uint256) {{
        return uint256(vm.load(target, bytes32(slot)));
    }}
}}
"""


def gen_compiler_spec(cfg: ContractConfig) -> str:
    """Generate Compiler/Specs.lean entry (printed for manual insertion)."""
    fields_str = ",\n    ".join(
        f'{{ name := "{f.name}", ty := FieldType.{f.ty} }}'
        for f in cfg.fields
    )

    func_strs = []
    for fn in cfg.functions:
        func_strs.append(f"""    {{ name := "{fn.name}"
      params := []  -- TODO: Add parameters
      returnType := none  -- TODO: Set return type
      body := [
        Stmt.stop  -- TODO: Implement body
      ]
    }}""")
    functions_str = ",\n".join(func_strs)

    name_lower = cfg.name[0].lower() + cfg.name[1:]
    return f"""
/-!
## {cfg.name} Specification
-/

def {name_lower}Spec : ContractSpec := {{
  name := "{cfg.name}"
  fields := [
    {fields_str}
  ]
  constructor := none
  functions := [
{functions_str}
  ]
}}"""


def gen_all_lean_imports(cfg: ContractConfig) -> str:
    """Generate import lines for DumbContracts/All.lean."""
    return f"""
import DumbContracts.Examples.{cfg.name}
import DumbContracts.Specs.{cfg.name}.Spec
import DumbContracts.Specs.{cfg.name}.Invariants
import DumbContracts.Proofs.{cfg.name}.Basic
import DumbContracts.Proofs.{cfg.name}.Correctness"""


# ---------------------------------------------------------------------------
# File writer
# ---------------------------------------------------------------------------

def write_file(path: Path, content: str, dry_run: bool) -> None:
    """Write content to path, creating parent directories."""
    if dry_run:
        print(f"  [dry-run] Would create: {path.relative_to(ROOT)}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        print(f"  [skip] Already exists: {path.relative_to(ROOT)}", file=sys.stderr)
        return
    path.write_text(content)
    print(f"  [created] {path.relative_to(ROOT)}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate scaffold files for a new DumbContracts contract.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 scripts/generate_contract.py MyContract
  python3 scripts/generate_contract.py MyToken --fields "balances:mapping,totalSupply:uint256,owner:address"
  python3 scripts/generate_contract.py MyToken --fields "balances:mapping" --functions "deposit,withdraw,getBalance"
  python3 scripts/generate_contract.py MyContract --dry-run
        """,
    )
    parser.add_argument("name", help="Contract name in PascalCase (e.g. MyToken)")
    parser.add_argument(
        "--fields",
        default="",
        help="Storage fields as 'name:type,...' where type is uint256|address|mapping (default: storedData:uint256)",
    )
    parser.add_argument(
        "--functions",
        default="",
        help="Function names as 'func1,func2,...' (default: auto-generated getter/setter)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print what would be created without writing files",
    )
    args = parser.parse_args()

    # Validate name
    name = args.name
    if not name[0].isupper():
        print(f"Error: Contract name must be PascalCase (got '{name}')", file=sys.stderr)
        sys.exit(1)
    if not name.isalnum():
        print(f"Error: Contract name must be alphanumeric (got '{name}')", file=sys.stderr)
        sys.exit(1)

    fields = parse_fields(args.fields)
    functions = parse_functions(args.functions, fields)
    cfg = ContractConfig(name=name, fields=fields, functions=functions)

    print(f"Generating scaffold for contract: {cfg.name}")
    print(f"  Fields: {', '.join(f'{f.name}:{f.ty}' for f in cfg.fields)}")
    print(f"  Functions: {', '.join(f.name for f in cfg.functions)}")
    print()

    # Generate files
    files = [
        (ROOT / "DumbContracts" / "Examples" / f"{name}.lean", gen_example(cfg)),
        (ROOT / "DumbContracts" / "Specs" / name / "Spec.lean", gen_spec(cfg)),
        (ROOT / "DumbContracts" / "Specs" / name / "Invariants.lean", gen_invariants(cfg)),
        (ROOT / "DumbContracts" / "Proofs" / name / "Basic.lean", gen_basic_proofs(cfg)),
        (ROOT / "DumbContracts" / "Proofs" / name / "Correctness.lean", gen_correctness_proofs(cfg)),
        (ROOT / "test" / f"Property{name}.t.sol", gen_property_tests(cfg)),
    ]

    print("Files:")
    for path, content in files:
        write_file(path, content, args.dry_run)

    # Print manual steps
    print()
    print("=" * 60)
    print("Manual steps required:")
    print("=" * 60)
    print()

    print("1. Add imports to DumbContracts/All.lean:")
    print(gen_all_lean_imports(cfg))
    print()

    print("2. Add compiler spec to Compiler/Specs.lean:")
    print(gen_compiler_spec(cfg))
    print()

    print("3. Run validation:")
    print("   lake build")
    print(f"   forge test --match-contract Property{name}")
    print("   python3 scripts/check_property_coverage.py")
    print()

    print("See docs-site/content/add-contract.mdx for the full checklist.")


if __name__ == "__main__":
    main()
