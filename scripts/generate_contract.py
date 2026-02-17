#!/usr/bin/env python3
"""Generate scaffold files for a new Verity contract.

Creates the complete file structure needed to add a new contract:
  - EDSL implementation (Verity/Examples/{Name}.lean)
  - Formal specification (Verity/Specs/{Name}/Spec.lean)
  - State invariants (Verity/Specs/{Name}/Invariants.lean)
  - Layer 1 proof re-export (Verity/Specs/{Name}/Proofs.lean)
  - Basic proofs (Verity/Proofs/{Name}/Basic.lean)
  - Correctness proofs (Verity/Proofs/{Name}/Correctness.lean)
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

def _is_getter_name(name: str) -> bool:
    """Return True if *name* looks like a getter (camelCase: getX, isX, hasX).

    The prefix must be followed by an uppercase letter so that names like
    ``hash`` (starts with "has") or ``issue`` (starts with "is") are not
    misclassified.
    """
    for prefix in ("get", "is", "has"):
        if name.startswith(prefix) and len(name) > len(prefix) and name[len(prefix)].isupper():
            return True
    return False


def gen_example(cfg: ContractConfig) -> str:
    """Generate Verity/Examples/{Name}.lean"""
    has_mapping = any(f.is_mapping for f in cfg.fields)

    imports = ["import Verity.Core"]
    if has_mapping or len(cfg.fields) > 1:
        imports.append("import Verity.EVM.Uint256")

    opens = ["open Verity"]
    if has_mapping or len(cfg.fields) > 1:
        opens.append("open Verity.EVM.Uint256")

    # Storage definitions
    storage_lines = []
    for i, f in enumerate(cfg.fields):
        if f.is_mapping:
            storage_lines.append(f"def {f.name}Slot : Nat := {i}")
        elif f.ty == "address":
            storage_lines.append(f"def {f.name} : StorageSlot Address := ⟨{i}⟩")
        else:
            storage_lines.append(f"def {f.name} : StorageSlot Uint256 := ⟨{i}⟩")

    # Function stubs — detect getters to use the correct return type.
    # We require the prefix to be followed by an uppercase letter (camelCase
    # boundary) so that e.g. "hash" does not match "has" and "issue" does
    # not match "is".
    func_lines = []
    for fn in cfg.functions:
        is_getter = _is_getter_name(fn.name)
        ret_type = "Contract Uint256" if is_getter else "Contract Unit"
        ret_val = "pure 0" if is_getter else "pure ()"
        func_lines.append(f"-- TODO: Implement {fn.name}")
        func_lines.append(f"def {fn.name} : {ret_type} := do")
        func_lines.append(f"  {ret_val}")
        func_lines.append("")

    return f"""/-
  {cfg.name}: Contract Implementation

  This contract demonstrates:
  - {', '.join(f.name + ' (' + f.ty + ')' for f in cfg.fields)}

  TODO: Add contract description
-/

{chr(10).join(imports)}

namespace Verity.Examples.{cfg.name}

{chr(10).join(opens)}

-- Storage layout
{chr(10).join(storage_lines)}

{chr(10).join(func_lines)}
end Verity.Examples.{cfg.name}
"""


def gen_spec(cfg: ContractConfig) -> str:
    """Generate Verity/Specs/{Name}/Spec.lean"""
    spec_defs = []
    for fn in cfg.functions:
        spec_defs.append(f"-- What {fn.name} should do")
        spec_defs.append(f"-- For mutating ops:   def {fn.name}_spec (params...) (s s' : ContractState) : Prop")
        spec_defs.append(f"-- For read-only ops:  def {fn.name}_spec (result : Uint256) (s : ContractState) : Prop")
        spec_defs.append(f"def {fn.name}_spec (s s' : ContractState) : Prop :=")
        spec_defs.append(f"  -- TODO: Add function parameters before (s s'), define postconditions")
        spec_defs.append(f"  True")
        spec_defs.append("")

    return f"""/-
  {cfg.name}: Formal Specification

  This file defines the formal specification of what {cfg.name}
  should do, separate from how it's implemented.
-/

import Verity.Core
import Verity.Specs.Common

namespace Verity.Specs.{cfg.name}

open Verity

{chr(10).join(spec_defs)}
end Verity.Specs.{cfg.name}
"""


def gen_invariants(cfg: ContractConfig) -> str:
    """Generate Verity/Specs/{Name}/Invariants.lean"""
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

import Verity.Core
import Verity.Specs.Common

namespace Verity.Specs.{cfg.name}

open Verity

-- Basic well-formedness of ContractState
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""

{chr(10).join(slot_isolation) if slot_isolation else "-- TODO: Add state invariants"}

-- Context preservation: operations don't change sender/address
abbrev context_preserved := Specs.sameContext

end Verity.Specs.{cfg.name}
"""


def gen_spec_proofs(cfg: ContractConfig) -> str:
    """Generate Verity/Specs/{Name}/Proofs.lean — Layer 1 proof re-export.

    Every existing contract (SimpleStorage, Counter, Owned, etc.) has this file.
    It re-exports the SpecCorrectness proof so that downstream users have a
    stable path under Verity.Specs.{Name}.Proofs.

    For a newly scaffolded contract the SpecCorrectness module does not exist
    yet, so we emit a commented-out import with a TODO instead of a bare
    import that would break ``lake build``.
    """
    return f"""-- TODO: Uncomment once Compiler/Proofs/SpecCorrectness/{cfg.name}.lean exists
-- import Compiler.Proofs.SpecCorrectness.{cfg.name}

/-
  Layer 1 proof re-export.
  This keeps the user-facing path stable while reusing the core proof module.

  Once you have written the SpecCorrectness proof for {cfg.name}, uncomment
  the import above so that `import Verity.Specs.{cfg.name}.Proofs` pulls it in.
-/
"""


def gen_basic_proofs(cfg: ContractConfig) -> str:
    """Generate Verity/Proofs/{Name}/Basic.lean"""
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

import Verity.Core
import Verity.Examples.{cfg.name}
import Verity.Specs.{cfg.name}.Spec
import Verity.Specs.{cfg.name}.Invariants

namespace Verity.Proofs.{cfg.name}

open Verity
open Verity.Examples.{cfg.name}
open Verity.Specs.{cfg.name}

{chr(10).join(proof_stubs)}
end Verity.Proofs.{cfg.name}
"""


def gen_correctness_proofs(cfg: ContractConfig) -> str:
    """Generate Verity/Proofs/{Name}/Correctness.lean"""
    return f"""/-
  {cfg.name}: Advanced Correctness Proofs

  Proves deeper properties beyond Basic.lean:
  - Invariant preservation
  - State isolation
  - Well-formedness preservation

  Status: Scaffold — proofs need implementation.
-/

import Verity.Core
import Verity.Examples.{cfg.name}
import Verity.Specs.{cfg.name}.Spec
import Verity.Specs.{cfg.name}.Invariants
import Verity.Proofs.{cfg.name}.Basic

namespace Verity.Proofs.{cfg.name}.Correctness

open Verity
open Verity.Examples.{cfg.name}
open Verity.Specs.{cfg.name}
open Verity.Proofs.{cfg.name}

-- TODO: Add advanced correctness proofs
-- See Verity/Proofs/SimpleStorage/Correctness.lean for reference

end Verity.Proofs.{cfg.name}.Correctness
"""


def gen_property_tests(cfg: ContractConfig) -> str:
    """Generate test/Property{Name}.t.sol with working test implementations."""
    has_mapping = any(f.is_mapping for f in cfg.fields)

    test_functions = []
    for i, fn in enumerate(cfg.functions):
        camel = fn.name[0].upper() + fn.name[1:]
        is_getter = _is_getter_name(fn.name)
        test_functions.append(
            _gen_single_test(cfg, fn, camel, i, is_getter)
        )

    theorem_list = "\n".join(
        f" * {i + 1}. {fn.name}_meets_spec"
        for i, fn in enumerate(cfg.functions)
    )

    # Generate helper functions based on field types
    helpers = _gen_test_helpers(cfg)

    return f"""// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title Property{cfg.name}Test
 * @notice Property-based tests extracted from formally verified Lean theorems
 * @dev Maps theorems from Verity/Proofs/{cfg.name}/ to executable tests
 *
 * This file contains property tests corresponding to proven theorems:
 *
 * From Basic.lean:
{theorem_list}
 */
contract Property{cfg.name}Test is YulTestBase {{
    address target;
    address alice = address(0x1111);
    address bob = address(0x2222);

    function setUp() public {{
        target = deployYul("{cfg.name}");
        require(target != address(0), "Deploy failed");
    }}

{chr(10).join(test_functions)}
{helpers}}}
"""


def _gen_single_test(
    cfg: ContractConfig,
    fn: Function,
    camel: str,
    idx: int,
    is_getter: bool,
) -> str:
    """Generate a single working test function."""
    if is_getter:
        return f"""    //═══════════════════════════════════════════════════════════════════════
    // Property {idx + 1}: {fn.name}_meets_spec
    // Theorem: {fn.name}() meets its formal specification
    //═══════════════════════════════════════════════════════════════════════

    /// Property: {fn.name}_meets_spec
    function testProperty_{camel}_MeetsSpec() public {{
        // Read-only function: verify it returns expected value and
        // does not modify storage.
        uint256 slot0Before = readStorage(0);

        (bool success, bytes memory data) = target.call(
            abi.encodeWithSignature("{fn.name}()")
        );
        require(success, "{fn.name} call failed");

        // Storage should be unchanged after a read-only call
        assertEq(readStorage(0), slot0Before, "{fn.name} should not modify storage");
    }}
"""
    else:
        return f"""    //═══════════════════════════════════════════════════════════════════════
    // Property {idx + 1}: {fn.name}_meets_spec
    // Theorem: {fn.name}() meets its formal specification
    //═══════════════════════════════════════════════════════════════════════

    /// Property: {fn.name}_meets_spec
    function testProperty_{camel}_MeetsSpec() public {{
        uint256 slot0Before = readStorage(0);

        vm.prank(alice);
        (bool success,) = target.call(
            abi.encodeWithSignature("{fn.name}()")
        );
        require(success, "{fn.name} call failed");

        // TODO: Add assertions matching {fn.name}'s formal spec.
        // Examples:
        //   assertEq(readStorage(0), slot0Before + 1, "should increment");
        //   assertEq(readStorage(1), expectedValue, "should update slot 1");
    }}
"""


def _gen_test_helpers(cfg: ContractConfig) -> str:
    """Generate utility functions for the test contract."""
    helpers = []

    # Always include readStorage
    helpers.append("""    //═══════════════════════════════════════════════════════════════════════
    // Utility functions
    //═══════════════════════════════════════════════════════════════════════

    /// @notice Read a raw storage slot from the deployed contract
    function readStorage(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(target, bytes32(slot)));
    }""")

    # Add mapping helpers if any field is a mapping
    has_mapping = any(f.is_mapping for f in cfg.fields)
    if has_mapping:
        mapping_fields = [f for f in cfg.fields if f.is_mapping]
        for f in mapping_fields:
            slot_idx = cfg.fields.index(f)
            helpers.append(f"""
    /// @notice Read mapping entry for {f.name} (slot {slot_idx})
    /// @dev Solidity mapping layout: keccak256(abi.encode(key, baseSlot))
    function get{f.name[0].upper()}{f.name[1:]}FromStorage(address addr) internal view returns (uint256) {{
        bytes32 slot = keccak256(abi.encode(addr, uint256({slot_idx})));
        return uint256(vm.load(target, slot));
    }}

    /// @notice Write mapping entry for {f.name} (slot {slot_idx}) — for test setup
    function set{f.name[0].upper()}{f.name[1:]}InStorage(address addr, uint256 amount) internal {{
        bytes32 slot = keccak256(abi.encode(addr, uint256({slot_idx})));
        vm.store(target, slot, bytes32(amount));
    }}""")

    return "\n".join(helpers) + "\n"


def gen_compiler_spec(cfg: ContractConfig) -> str:
    """Generate Compiler/Specs.lean entry (printed for manual insertion)."""
    fields_str = ",\n    ".join(
        f'{{ name := "{f.name}", ty := FieldType.{f.ty} }}'
        for f in cfg.fields
    )

    func_strs = []
    for fn in cfg.functions:
        func_strs.append(f"""    {{ name := "{fn.name}"
      params := []  -- TODO: e.g. [{{ name := "value", ty := ParamType.uint256 }}]
      returnType := none  -- TODO: e.g. some FieldType.uint256
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
    """Generate import lines for Verity/All.lean."""
    return f"""
import Verity.Examples.{cfg.name}
import Verity.Specs.{cfg.name}.Spec
import Verity.Specs.{cfg.name}.Invariants
import Verity.Specs.{cfg.name}.Proofs
import Verity.Proofs.{cfg.name}.Basic
import Verity.Proofs.{cfg.name}.Correctness"""


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
        description="Generate scaffold files for a new Verity contract.",
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
        (ROOT / "Verity" / "Examples" / f"{name}.lean", gen_example(cfg)),
        (ROOT / "Verity" / "Specs" / name / "Spec.lean", gen_spec(cfg)),
        (ROOT / "Verity" / "Specs" / name / "Invariants.lean", gen_invariants(cfg)),
        (ROOT / "Verity" / "Specs" / name / "Proofs.lean", gen_spec_proofs(cfg)),
        (ROOT / "Verity" / "Proofs" / name / "Basic.lean", gen_basic_proofs(cfg)),
        (ROOT / "Verity" / "Proofs" / name / "Correctness.lean", gen_correctness_proofs(cfg)),
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

    print("1. Add imports to Verity/All.lean:")
    print(gen_all_lean_imports(cfg))
    print()

    name_lower = cfg.name[0].lower() + cfg.name[1:]
    print("2. Add compiler spec to Compiler/Specs.lean:")
    print(gen_compiler_spec(cfg))
    print()

    print(f"3. Register in allSpecs (Compiler/Specs.lean):")
    print(f"   Find 'def allSpecs' and add '{name_lower}Spec' to the list.")
    print()

    print("4. Run validation:")
    print("   lake build")
    print(f"   FOUNDRY_PROFILE=difftest forge test --match-contract Property{name}")
    print("   python3 scripts/check_property_coverage.py")
    print()

    print("See docs-site/content/add-contract.mdx for the full checklist.")


if __name__ == "__main__":
    main()
