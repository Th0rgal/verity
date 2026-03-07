# Axioms in Verity

This file is the authoritative registry of axioms used by Verity proof code.

## Policy

Axioms are exceptional. When an axiom exists, it must have:

1. Explicit documentation in this file.
2. Source comment marking it as an axiom and linking to this file.
3. CI checks that validate usage assumptions.
4. A clear elimination path, when practical.

## Current Axioms

### 1. `keccak256_first_4_bytes`

**Location**: `Compiler/Selectors.lean:41`

**Statement**:
```lean
axiom keccak256_first_4_bytes (sig : String) : Nat
```

**Purpose**:
Computes function selectors (`bytes4(keccak256(signature))`) used in ABI dispatch.

**Why this is currently an axiom**:
Selector hashing is modeled as an external cryptographic primitive rather than reimplemented and proven in Lean.

**Soundness controls**:

- CI cross-checks selectors against `solc --hashes`.
- CI runs selector fixture checks to detect regressions.
- Compilation and tests fail if selector consistency drifts.

**Risk**: Low.

## Trusted Cryptographic Primitive (Non-Axiom)

### `ffi.KEC` (keccak256 via EVMYul FFI)

**Location**: used by `Compiler/Proofs/MappingSlot.lean` (`solidityMappingSlot`)

**Role**:
- Computes mapping storage slots as `keccak256(abi.encode(key, baseSlot))`.
- Aligns proof-level mapping addressing with Solidity/EVM flat storage layout.

**Why this is not listed as a Lean axiom**:
- It is a runtime external primitive (`@[extern]`-style FFI path), not a logical axiom in Lean's kernel.
- Trust is operational (correctness of linked crypto implementation), not proof-kernel extensibility.

**Operational trust assumptions**:
- Keccak implementation correctness in the linked FFI path.
- Standard collision-resistance assumptions for mapping-slot uniqueness/non-collision, matching Solidity/EVM assumptions.

**Soundness controls**:
- Mapping-slot abstraction boundary checks in CI.
- End-to-end proof/runtime regression suites that exercise mapping reads/writes through `mappingSlot`.

## External Call Module (ECM) Axioms

ECMs introduce trust assumptions via their `axioms` field. These are not Lean
kernel axioms — they are documented interface assumptions about external contracts
and precompiles. The compiler aggregates them at compile time and surfaces them
in `--verbose` output.

### Standard Module Axioms

| Module | Axiom | Meaning |
|--------|-------|---------|
| `ERC20.safeTransfer` | `erc20_transfer_interface` | Target implements ERC-20 `transfer(address,uint256)` |
| `ERC20.safeTransferFrom` | `erc20_transferFrom_interface` | Target implements ERC-20 `transferFrom(address,address,uint256)` |
| `ERC20.safeApprove` | `erc20_approve_interface` | Target implements ERC-20 `approve(address,uint256)` |
| `Precompiles.ecrecover` | `evm_ecrecover_precompile` | EVM precompile at address 0x01 behaves per Yellow Paper |
| `Callbacks.callback` | `callback_target_interface` | Callback target processes ABI-encoded arguments correctly |
| `Calls.withReturn` | `external_call_abi_interface` | Target contract function matches declared selector and ABI |

### Third-Party Module Axioms

Third-party ECMs (external Lean packages) document their axioms in their own
`AXIOMS.md`. All axioms — standard and third-party — are aggregated and reported
at compile time. See `docs/EXTERNAL_CALL_MODULES.md` for details.

**Risk**: Low. ECM axioms are interface assumptions (not proof-kernel extensions)
scoped to contracts that use the module.

## Eliminated Axioms (Historical)

The repository removed prior axioms related to IR and Yul expression and statement equivalence and address injectivity by making interpreters total and by using a bounded-nat `Address` representation.

These removals reduced prior axiom debt. The remaining Layer 3 switch-case bridge is now
an explicit theorem parameter (`SwitchCaseBodyBridge`) rather than a Lean kernel axiom.

## Non-Axiom: Arithmetic Semantics

Wrapping modular arithmetic at 2^256 is **proven**, not assumed. All 15 pure builtins (add, sub, mul, div, mod, lt, gt, eq, iszero, and, or, xor, not, shl, shr) have formal wrapping proofs in `Compiler/Proofs/ArithmeticProfile.lean`. The EVMYulLean bridge currently has universal equivalence lemmas for 12 of them (`add`, `sub`, `mul`, `div`, `mod`, `lt`, `gt`, `eq`, `iszero`, `and`, `or`, `xor`) in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean`, while `not`, `shl`, and `shr` are covered by concrete bridge checks in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeTest.lean`. This is a design choice matching EVM semantics, not a trust assumption. See [`docs/ARITHMETIC_PROFILE.md`](docs/ARITHMETIC_PROFILE.md) for the full specification.

## Trust Summary

- Active axioms: 1
- Production blockers from axioms: 0
- Enforcement: `scripts/check_axioms.py` ensures this file tracks exact source location.
- Compilation-path totalization work in `Compiler/CompilationModel.lean` does not
  add, remove, or modify Lean axioms; it only replaces `partial def` recursion
  with explicit structural termination proofs (including dynamic-param scope
  checks, statement read/write analyzers, statement-list validation walkers,
  and all Expr/Stmt validation walkers: scoped-identifier, interop,
  internal-call-shape, external-call-target, and event-argument-shape).
- Macro front-end extensions (including explicit `getMappingUint` /
  `setMappingUint` translation support in `Verity/Macro/Translate.lean`) do not
  add, remove, or modify Lean axioms.
- The semantic bridge and typed-IR migration work (Issues #998 and #1060:
  `Compiler/Proofs/EndToEnd.lean`, `Compiler/Proofs/SemanticBridge.lean`,
  `Verity/Macro/Bridge.lean`, and the `Compiler/TypedIR*` pipeline)
  does not add, remove, or modify Lean axioms. `SemanticBridge.lean` now has
  zero `sorry`. The typed-IR compilation path (`Compiler/TypedIRCompiler*.lean`) also
  has zero `sorry`.

## Maintenance Rule

Any commit that adds, removes, renames, or moves an axiom must update this file in the same commit.

If this file is stale, trust analysis is stale.

**Last Updated**: 2026-03-06
