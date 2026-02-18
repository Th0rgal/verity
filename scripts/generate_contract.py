#!/usr/bin/env python3
"""Generate scaffold files for a new Verity contract.

Creates the complete file structure needed to add a new contract:
  - EDSL implementation (Verity/Examples/{Name}.lean)
  - Formal specification (Verity/Specs/{Name}/Spec.lean)
  - State invariants (Verity/Specs/{Name}/Invariants.lean)
  - Layer 2 proof re-export (Verity/Specs/{Name}/Proofs.lean)
  - Basic proofs (Verity/Proofs/{Name}/Basic.lean)
  - Correctness proofs (Verity/Proofs/{Name}/Correctness.lean)
  - Compiler spec entry (printed to stdout for manual insertion)
  - Property tests (test/Property{Name}.t.sol)

Usage:
    python3 scripts/generate_contract.py MyContract
    python3 scripts/generate_contract.py MyContract --fields "value:uint256,owner:address"
    python3 scripts/generate_contract.py MyContract --fields "balances:mapping" --functions "deposit(uint256),withdraw(uint256),transfer(address,uint256),getBalance(address)"
    python3 scripts/generate_contract.py MyContract --fields "data:mapping(uint256)" --functions "store(uint256,uint256),get(uint256)"
    python3 scripts/generate_contract.py MyContract --dry-run
"""

from __future__ import annotations

import argparse
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
    ty: str  # "uint256", "address", "mapping", "mapping_uint"

    @property
    def lean_type(self) -> str:
        if self.ty == "uint256":
            return "Uint256"
        if self.ty == "address":
            return "Address"
        if self.ty == "mapping":
            return "Address → Uint256"
        if self.ty == "mapping_uint":
            return "Uint256 → Uint256"
        return "Uint256"

    @property
    def is_mapping(self) -> bool:
        return self.ty in ("mapping", "mapping_uint")

    @property
    def storage_kind(self) -> str:
        if self.ty == "address":
            return "StorageSlot Address"
        if self.ty == "mapping":
            return "StorageSlot (Address → Uint256)"
        if self.ty == "mapping_uint":
            return "StorageSlot (Uint256 → Uint256)"
        return "StorageSlot Uint256"

    @property
    def compiler_field_type(self) -> str:
        """FieldType variant for Compiler/Specs.lean."""
        if self.ty == "mapping_uint":
            return "FieldType.mappingTyped (.simple .uint256)"
        return f"FieldType.{self.ty}"

    @property
    def display_type(self) -> str:
        """Human-readable type name for output messages."""
        if self.ty == "mapping_uint":
            return "mapping(uint256)"
        return self.ty


@dataclass
class Param:
    name: str
    ty: str  # "uint256", "address"

    @property
    def lean_type(self) -> str:
        if self.ty == "address":
            return "Address"
        return "Uint256"

    @property
    def compiler_type(self) -> str:
        """ParamType variant for Compiler/Specs.lean."""
        if self.ty == "address":
            return "ParamType.address"
        return "ParamType.uint256"

    @property
    def solidity_type(self) -> str:
        if self.ty == "address":
            return "address"
        return "uint256"


@dataclass
class Function:
    name: str
    params: List[Param] = field(default_factory=list)


@dataclass
class ContractConfig:
    name: str
    fields: List[Field]
    functions: List[Function]


# ---------------------------------------------------------------------------
# Parsers
# ---------------------------------------------------------------------------

def _normalize_field_type(ty: str) -> str:
    """Normalize a field type string to an internal type name.

    Supported types:
      ``uint256``                → ``"uint256"``
      ``address``                → ``"address"``
      ``mapping``                → ``"mapping"``  (Address → Uint256)
      ``mapping(address)``       → ``"mapping"``  (Address → Uint256)
      ``mapping(uint256)``       → ``"mapping_uint"`` (Uint256 → Uint256)
    """
    ty = ty.strip().lower()
    if ty in ("uint256", "address"):
        return ty
    if ty == "mapping" or ty == "mapping(address)":
        return "mapping"
    if ty == "mapping(uint256)":
        return "mapping_uint"
    return ""  # unknown


def parse_fields(spec: str) -> List[Field]:
    """Parse 'name:type,name:type,...' into Field list.

    Supported field types: ``uint256``, ``address``, ``mapping``,
    ``mapping(address)`` (same as ``mapping``), ``mapping(uint256)``.
    """
    if not spec:
        return [Field("storedData", "uint256")]
    fields = []
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if ":" in part:
            name, ty_raw = part.split(":", 1)
            name = name.strip()
            if not name:
                print("Error: Field name cannot be empty (got ':<type>')", file=sys.stderr)
                sys.exit(1)
            ty = _normalize_field_type(ty_raw)
            if not ty:
                print(f"Warning: Unknown type '{ty_raw.strip()}', defaulting to uint256", file=sys.stderr)
                ty = "uint256"
            fields.append(Field(name, ty))
        else:
            fields.append(Field(part.strip(), "uint256"))
    return fields


_PARAM_NAME_COUNTERS: dict[str, int] = {}

def _auto_param_name(ty: str) -> str:
    """Generate a descriptive parameter name from its type.

    First call for a type returns the canonical name (e.g. "value" for uint256);
    subsequent calls within the same function append a counter ("value2").
    Call ``_PARAM_NAME_COUNTERS.clear()`` between functions.
    """
    base = "addr" if ty == "address" else "value"
    count = _PARAM_NAME_COUNTERS.get(base, 0) + 1
    _PARAM_NAME_COUNTERS[base] = count
    return base if count == 1 else f"{base}{count}"


def _parse_single_function(raw: str) -> Function:
    """Parse a single function spec like 'transfer(address,uint256)' or 'increment'.

    Supported forms:
      - ``increment``           → no params
      - ``store(uint256)``      → one uint256 param named "value"
      - ``transfer(address,uint256)`` → two params named "addr", "value"
    """
    raw = raw.strip()
    if "(" not in raw:
        return Function(name=raw)

    paren_idx = raw.index("(")
    name = raw[:paren_idx].strip()
    params_str = raw[paren_idx + 1:].rstrip(")")

    _PARAM_NAME_COUNTERS.clear()
    params = []
    for ty_raw in params_str.split(","):
        ty_raw = ty_raw.strip().lower()
        if not ty_raw:
            continue
        if ty_raw not in ("uint256", "address"):
            print(f"Warning: Unknown param type '{ty_raw}' in {name}, defaulting to uint256", file=sys.stderr)
            ty_raw = "uint256"
        params.append(Param(name=_auto_param_name(ty_raw), ty=ty_raw))

    return Function(name=name, params=params)


def parse_functions(spec: str, fields: List[Field]) -> List[Function]:
    """Parse 'func1,func2(type,...),...' or generate defaults from fields.

    Supports both bare names and typed signatures::

        --functions "deposit(uint256),transfer(address,uint256),getBalance(address)"

    Parameter names are auto-generated from types (addr, value, etc.).
    """
    if spec:
        # Split on commas that are NOT inside parentheses
        functions = []
        depth = 0
        current: list[str] = []
        for ch in spec:
            if ch == "(":
                depth += 1
                current.append(ch)
            elif ch == ")":
                depth -= 1
                current.append(ch)
            elif ch == "," and depth == 0:
                functions.append(_parse_single_function("".join(current)))
                current = []
            else:
                current.append(ch)
        if current:
            functions.append(_parse_single_function("".join(current)))
        return [f for f in functions if f.name]
    # Default: generate getter/setter for first field
    if fields:
        f = fields[0]
        setter = f"set{f.name[0].upper()}{f.name[1:]}"
        getter = f"get{f.name[0].upper()}{f.name[1:]}"
        if f.is_mapping:
            # Mappings need key + value params
            key_ty = "address" if f.ty == "mapping" else "uint256"
            return [
                Function(setter, [Param("key", key_ty), Param("value", "uint256")]),
                Function(getter, [Param("key", key_ty)]),
            ]
        else:
            # Scalar fields: setter takes the field's type as param
            return [
                Function(setter, [Param("value", f.ty)]),
                Function(getter),
            ]
    return [Function("setValue", [Param("value", "uint256")]), Function("getValue")]


# ---------------------------------------------------------------------------
# Template generators
# ---------------------------------------------------------------------------

def _getter_prefix(name: str) -> str | None:
    """Return the getter prefix if *name* looks like a getter, else ``None``.

    Recognized prefixes: ``get``, ``is``, ``has``.  The prefix must be
    followed by an uppercase letter (camelCase boundary) so that names like
    ``hash`` (starts with "has") or ``issue`` (starts with "is") are not
    misclassified.
    """
    for prefix in ("get", "is", "has"):
        if name.startswith(prefix) and len(name) > len(prefix) and name[len(prefix)].isupper():
            return prefix
    return None


def _getter_return_type(fn: Function, fields: List[Field]) -> str:
    """Determine the Lean return type for a getter function.

    Returns ``"Bool"`` for ``is``/``has``-prefix getters,
    ``"Address"`` for ``get``-prefix getters whose suffix matches an address
    field, and ``"Uint256"`` otherwise.
    """
    prefix = _getter_prefix(fn.name)
    if prefix is None:
        return "Uint256"  # not a getter, but safe fallback
    if prefix in ("is", "has"):
        return "Bool"
    # get-prefix: check if suffix matches an address field
    suffix = fn.name[len(prefix):]
    addr_field_names = {f.name.lower() for f in fields if f.ty == "address"}
    if suffix.lower() in addr_field_names:
        return "Address"
    return "Uint256"


def gen_example(cfg: ContractConfig) -> str:
    """Generate Verity/Examples/{Name}.lean"""
    has_mapping = any(f.is_mapping for f in cfg.fields)
    has_uint256 = any(f.ty == "uint256" for f in cfg.fields)
    has_uint256_param = any(p.ty == "uint256" for fn in cfg.functions for p in fn.params)
    has_uint256_getter = any(
        _getter_prefix(fn.name) is not None
        and _getter_return_type(fn, cfg.fields) == "Uint256"
        for fn in cfg.functions
    )
    needs_uint256 = has_mapping or has_uint256 or has_uint256_param or has_uint256_getter

    imports = ["import Verity.Core"]
    if needs_uint256:
        imports.append("import Verity.EVM.Uint256")

    opens = ["open Verity"]
    if needs_uint256:
        opens.append("open Verity.EVM.Uint256")

    # Storage definitions
    storage_lines = []
    for i, f in enumerate(cfg.fields):
        storage_lines.append(f"def {f.name} : {f.storage_kind} := ⟨{i}⟩")

    # Function stubs — detect getters to use the correct return type.
    # Match getter names to field types: getOwner → owner → address field.
    # "is"/"has"-prefix getters return Bool (e.g., isOwner → Contract Bool).
    addr_field_names = {f.name.lower() for f in cfg.fields if f.ty == "address"}
    func_lines = []
    for fn in cfg.functions:
        matched_prefix = _getter_prefix(fn.name)
        if matched_prefix is not None:
            suffix = fn.name[len(matched_prefix):]
            if matched_prefix in ("is", "has"):
                ret_type = "Contract Bool"
                ret_val = "pure false  -- TODO: implement predicate (see OwnedCounter.lean)"
            elif suffix.lower() in addr_field_names:
                ret_type = "Contract Address"
                ret_val = 'pure ""  -- TODO: use getStorageAddr <slot> (see Owned.lean)'
            else:
                ret_type = "Contract Uint256"
                ret_val = "pure 0  -- TODO: use getStorage <slot> (see SimpleStorage.lean)"
        else:
            ret_type = "Contract Unit"
            ret_val = "pure ()  -- TODO: implement (see Counter.lean for mutating ops)"
        # Build parameter list: (param1 : Type1) (param2 : Type2)
        param_str = ""
        if fn.params:
            param_str = " ".join(f"({p.name} : {p.lean_type})" for p in fn.params)
            param_str = " " + param_str
        func_lines.append(f"-- TODO: Implement {fn.name}")
        func_lines.append(f"def {fn.name}{param_str} : {ret_type} := do")
        func_lines.append(f"  {ret_val}")
        func_lines.append("")

    return f"""/-
  {cfg.name}: Contract Implementation

  This contract demonstrates:
  - {', '.join(f.name + ' (' + f.display_type + ')' for f in cfg.fields)}

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
    has_mapping = any(f.is_mapping for f in cfg.fields)

    spec_defs = []
    for fn in cfg.functions:
        is_getter = _getter_prefix(fn.name) is not None
        # Build Lean parameter declarations
        lean_params = " ".join(f"({p.name} : {p.lean_type})" for p in fn.params)
        spec_defs.append(f"-- What {fn.name} should do")
        if is_getter:
            # Getter spec: result-based (see getOwner_spec, isOwner_spec, getBalance_spec)
            ret_type = _getter_return_type(fn, cfg.fields)
            param_part = f" {lean_params}" if lean_params else ""
            spec_defs.append(f"def {fn.name}_spec{param_part} (result : {ret_type}) (s : ContractState) : Prop :=")
            spec_defs.append(f"  -- TODO: Define what the return value should be")
            spec_defs.append(f"  True")
        else:
            # Mutator spec: state-based (see deposit_spec, store_spec)
            param_part = f" {lean_params}" if lean_params else ""
            spec_defs.append(f"def {fn.name}_spec{param_part} (s s' : ContractState) : Prop :=")
            spec_defs.append(f"  -- TODO: Define postconditions on s'")
            spec_defs.append(f"  True")
        spec_defs.append("")

    imports = ["import Verity.Core", "import Verity.Specs.Common"]
    opens = ["open Verity"]
    # Only need Uint256 import if a getter actually returns Uint256 (not Address/Bool)
    has_uint256_getter = any(
        _getter_prefix(fn.name) is not None
        and _getter_return_type(fn, cfg.fields) == "Uint256"
        for fn in cfg.functions
    )
    has_uint256_param = any(p.ty == "uint256" for fn in cfg.functions for p in fn.params)
    if has_mapping or any(f.ty == "uint256" for f in cfg.fields) or has_uint256_param or has_uint256_getter:
        imports.append("import Verity.EVM.Uint256")
        opens.append("open Verity.EVM.Uint256")

    return f"""/-
  {cfg.name}: Formal Specification

  This file defines the formal specification of what {cfg.name}
  should do, separate from how it's implemented.
-/

{chr(10).join(imports)}

namespace Verity.Specs.{cfg.name}

{chr(10).join(opens)}

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
    """Generate Verity/Specs/{Name}/Proofs.lean — Layer 2 proof re-export.

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
  Layer 2 proof re-export.
  This keeps the user-facing path stable while reusing the core proof module.

  Once you have written the SpecCorrectness proof for {cfg.name}, uncomment
  the import above so that `import Verity.Specs.{cfg.name}.Proofs` pulls it in.
-/
"""


def gen_basic_proofs(cfg: ContractConfig) -> str:
    """Generate Verity/Proofs/{Name}/Basic.lean"""
    has_mapping = any(f.is_mapping for f in cfg.fields)

    proof_stubs = []
    for fn in cfg.functions:
        is_getter = _getter_prefix(fn.name) is not None
        # Build Lean parameter declarations: (param1 : Type1) (param2 : Type2)
        lean_params = " ".join(f"({p.name} : {p.lean_type})" for p in fn.params)
        # Build function call arguments: fn param1 param2
        call_args = " ".join(p.name for p in fn.params)
        fn_call = f"{fn.name} {call_args}" if call_args else fn.name
        # Build spec arguments: param1 param2
        spec_args = " ".join(p.name for p in fn.params)

        proof_stubs.append(f"-- TODO: Prove {fn.name} meets its specification")
        if is_getter:
            # Getter pattern: extract return value with .fst (see retrieve_meets_spec, getBalance_meets_spec)
            theorem_params = f"(s : ContractState) {lean_params}" if lean_params else "(s : ContractState)"
            proof_stubs.append(f"theorem {fn.name}_meets_spec {theorem_params} :")
            proof_stubs.append(f"  let result := (({fn_call}).run s).fst")
            spec_call = f"{fn.name}_spec {spec_args} result s" if spec_args else f"{fn.name}_spec result s"
            proof_stubs.append(f"  {spec_call} := by")
        else:
            # Mutator pattern: extract output state with .snd (see store_meets_spec, deposit_meets_spec)
            theorem_params = f"(s : ContractState) {lean_params}" if lean_params else "(s : ContractState)"
            proof_stubs.append(f"theorem {fn.name}_meets_spec {theorem_params} :")
            proof_stubs.append(f"  let s' := (({fn_call}).run s).snd")
            spec_call = f"{fn.name}_spec {spec_args} s s'" if spec_args else f"{fn.name}_spec s s'"
            proof_stubs.append(f"  {spec_call} := by")
        proof_stubs.append(f"  sorry  -- TODO: replace with proof (see debugging-proofs guide)")
        proof_stubs.append("")

    imports = [
        "import Verity.Core",
        f"import Verity.Examples.{cfg.name}",
        f"import Verity.Specs.{cfg.name}.Spec",
        f"import Verity.Specs.{cfg.name}.Invariants",
    ]
    opens = [
        "open Verity",
        f"open Verity.Examples.{cfg.name}",
        f"open Verity.Specs.{cfg.name}",
    ]
    has_uint256_param = any(p.ty == "uint256" for fn in cfg.functions for p in fn.params)
    has_uint256_getter = any(
        _getter_prefix(fn.name) is not None
        and _getter_return_type(fn, cfg.fields) == "Uint256"
        for fn in cfg.functions
    )
    if has_mapping or any(f.ty == "uint256" for f in cfg.fields) or has_uint256_param or has_uint256_getter:
        imports.insert(1, "import Verity.EVM.Uint256")
        opens.append("open Verity.EVM.Uint256")

    return f"""/-
  {cfg.name}: Basic Correctness Proofs

  This file contains proofs of basic correctness properties for {cfg.name}.

  Status: Scaffold — proofs need implementation.
-/

{chr(10).join(imports)}

namespace Verity.Proofs.{cfg.name}

{chr(10).join(opens)}

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
        is_getter = _getter_prefix(fn.name) is not None
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
    # Build Solidity signature: "funcName(uint256,address)"
    sol_sig = f"{fn.name}({','.join(p.solidity_type for p in fn.params)})"
    # Build call arguments for abi.encodeWithSignature
    if fn.params:
        # Generate example argument values
        call_args = []
        for p in fn.params:
            if p.ty == "address":
                call_args.append("alice")
            else:
                call_args.append("42")
        encode_args = ", ".join([f'"{sol_sig}"'] + call_args)
    else:
        encode_args = f'"{sol_sig}"'

    if is_getter:
        return f"""    //═══════════════════════════════════════════════════════════════════════
    // Property {idx + 1}: {fn.name}_meets_spec
    // Theorem: {fn.name}({', '.join(p.solidity_type for p in fn.params)}) meets its formal specification
    //═══════════════════════════════════════════════════════════════════════

    /// Property: {fn.name}_meets_spec
    function testProperty_{camel}_MeetsSpec() public {{
        // Read-only function: verify it returns expected value and
        // does not modify storage.
        uint256 slot0Before = readStorage(0);

        (bool success, bytes memory data) = target.call(
            abi.encodeWithSignature({encode_args})
        );
        require(success, "{fn.name} call failed");

        // Storage should be unchanged after a read-only call
        assertEq(readStorage(0), slot0Before, "{fn.name} should not modify storage");
    }}
"""
    else:
        return f"""    //═══════════════════════════════════════════════════════════════════════
    // Property {idx + 1}: {fn.name}_meets_spec
    // Theorem: {fn.name}({', '.join(p.solidity_type for p in fn.params)}) meets its formal specification
    //═══════════════════════════════════════════════════════════════════════

    /// Property: {fn.name}_meets_spec
    function testProperty_{camel}_MeetsSpec() public {{
        uint256 slot0Before = readStorage(0);

        vm.prank(alice);
        (bool success,) = target.call(
            abi.encodeWithSignature({encode_args})
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
            # Key type depends on mapping variant
            if f.ty == "mapping_uint":
                key_type = "uint256"
                key_name = "key"
            else:
                key_type = "address"
                key_name = "addr"
            helpers.append(f"""
    /// @notice Read mapping entry for {f.name} (slot {slot_idx})
    /// @dev Solidity mapping layout: keccak256(abi.encode(key, baseSlot))
    function get{f.name[0].upper()}{f.name[1:]}FromStorage({key_type} {key_name}) internal view returns (uint256) {{
        bytes32 slot = keccak256(abi.encode({key_name}, uint256({slot_idx})));
        return uint256(vm.load(target, slot));
    }}

    /// @notice Write mapping entry for {f.name} (slot {slot_idx}) — for test setup
    function set{f.name[0].upper()}{f.name[1:]}InStorage({key_type} {key_name}, uint256 amount) internal {{
        bytes32 slot = keccak256(abi.encode({key_name}, uint256({slot_idx})));
        vm.store(target, slot, bytes32(amount));
    }}""")

    return "\n".join(helpers) + "\n"


def gen_compiler_spec(cfg: ContractConfig) -> str:
    """Generate Compiler/Specs.lean entry (printed for manual insertion)."""
    fields_str = ",\n    ".join(
        f'{{ name := "{f.name}", ty := {f.compiler_field_type} }}'
        for f in cfg.fields
    )

    func_strs = []
    for fn in cfg.functions:
        is_getter = _getter_prefix(fn.name) is not None
        # Build params list
        if fn.params:
            params_entries = ",\n        ".join(
                f'{{ name := "{p.name}", ty := {p.compiler_type} }}'
                for p in fn.params
            )
            params_str = f"[{params_entries}]"
        else:
            params_str = "[]"
        if is_getter:
            # Getter: return a storage value (see getCount, getOwner, getBalance)
            ret_type = _getter_return_type(fn, cfg.fields)
            if ret_type == "Address":
                compiler_ret = "FieldType.address"
            else:
                compiler_ret = "FieldType.uint256"  # Bool maps to uint256 at EVM level
            func_strs.append(f"""    {{ name := "{fn.name}"
      params := {params_str}
      returnType := some {compiler_ret}
      body := [
        Stmt.return (Expr.storage "{cfg.fields[0].name if cfg.fields else 'field'}")  -- TODO: match actual field
      ]
    }}""")
        else:
            # Mutator: modifies state and stops (see increment, store, transfer)
            func_strs.append(f"""    {{ name := "{fn.name}"
      params := {params_str}
      returnType := none
      body := [
        Stmt.stop  -- TODO: Implement body (see Compiler/Specs.lean for examples)
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
  python3 scripts/generate_contract.py MyToken --fields "balances:mapping" --functions "deposit(uint256),withdraw(uint256),getBalance(address)"
  python3 scripts/generate_contract.py MyContract --dry-run
        """,
    )
    parser.add_argument("name", help="Contract name in PascalCase (e.g. MyToken)")
    parser.add_argument(
        "--fields",
        default="",
        help="Storage fields as 'name:type,...' where type is uint256|address|mapping|mapping(uint256) (default: storedData:uint256)",
    )
    parser.add_argument(
        "--functions",
        default="",
        help="Function signatures as 'func1(type,...),func2,...' e.g. 'deposit(uint256),transfer(address,uint256),getBalance(address)' (default: auto-generated getter/setter)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print what would be created without writing files",
    )
    args = parser.parse_args()

    # Validate name
    name = args.name
    if not name:
        print("Error: Contract name cannot be empty", file=sys.stderr)
        sys.exit(1)
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
    print(f"  Fields: {', '.join(f'{f.name}:{f.display_type}' for f in cfg.fields)}")
    def _fn_repr(fn: Function) -> str:
        if fn.params:
            return f"{fn.name}({','.join(p.ty for p in fn.params)})"
        return fn.name
    print(f"  Functions: {', '.join(_fn_repr(f) for f in cfg.functions)}")
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
    print(f"   Also add selectors for each function in Compiler/Selectors.lean")
    print(f"   (see existing selectors for the pattern using keccak256_first_4_bytes).")
    print()

    print(f"4. Create differential tests (not scaffolded):")
    print(f"   Copy test/DifferentialCounter.t.sol to test/Differential{name}.t.sol")
    print(f"   Inherit YulTestBase, DiffTestConfig, and DifferentialTestBase (all three required)")
    print()

    print("5. Run validation (see add-contract.mdx for the full checklist):")
    print("   lake build")
    print(f"   FOUNDRY_PROFILE=difftest forge test --match-contract {name}")
    print("   python3 scripts/check_property_manifest.py")
    print("   python3 scripts/check_property_manifest_sync.py")
    print("   python3 scripts/check_contract_structure.py")
    print("   python3 scripts/check_selectors.py")
    print("   python3 scripts/check_doc_counts.py")


if __name__ == "__main__":
    main()
