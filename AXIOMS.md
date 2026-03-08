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

### 2. `exec_calldatasizeGuard_noop`

**Location**: `Compiler/Proofs/YulGeneration/Preservation.lean:161`

**Statement**:
```lean
private axiom exec_calldatasizeGuard_noop
```

**Purpose**:
Bridges the preservation proof over the generated `calldatasizeGuard` when calldata arity is sufficient.

**Why this is currently an axiom**:
The reduction from proof-runtime `calldatasize`/`lt` normalization to the intended arity check is still not fully mechanized in this theorem path.

**Risk**: Medium.

### 3. `eval_buildSwitch_hasSelectorExpr_eq_one`

**Location**: `Compiler/Proofs/YulGeneration/Preservation.lean:195`

**Statement**:
```lean
private axiom eval_buildSwitch_hasSelectorExpr_eq_one
```

**Purpose**:
Captures that the generated dispatch prelude computes `__has_selector = 1` because runtime calldata always contains the 4-byte selector word.

**Why this is currently an axiom**:
The execution fact is understood, but the modulo-aware builtin normalization for this exact `buildSwitch` path is still incomplete.

**Risk**: Medium.

### 4. `eval_iszero_hasSelector_after_set`

**Location**: `Compiler/Proofs/YulGeneration/Preservation.lean:204`

**Statement**:
```lean
private axiom eval_iszero_hasSelector_after_set
```

**Purpose**:
Bridges the local dispatch-state fact that after setting `__has_selector := 1`, evaluating `iszero(__has_selector)` yields `0`.

**Why this is currently an axiom**:
This is a small helper fact that currently sits inside the same partially-axiomatized dispatch-step proof boundary.

**Risk**: Low.

### 5. `execBuildSwitch_none_none_aux`

**Location**: `Compiler/Proofs/YulGeneration/Preservation.lean:250`

**Statement**:
```lean
private axiom execBuildSwitch_none_none_aux
```

**Purpose**:
Connects execution of the emitted `buildSwitch ... none none` block to the corresponding selector-switch step used in contract dispatch.

**Why this is currently an axiom**:
The step-by-step execution trace is known, but proving it directly through reducible `execYulFuel` remains technically brittle.

**Risk**: Medium.

### 6. `SwitchCaseBodyBridge`

**Location**: `Compiler/Proofs/YulGeneration/Preservation.lean:311`

**Statement**:
```lean
private axiom SwitchCaseBodyBridge
```

**Purpose**:
Bridges from the single-function body equivalence theorem to the actual generated runtime-dispatch execution shape (`switchCaseBody`, `__has_selector`, rollback shaping, and arity-guarded execution).

**Why this is currently an axiom**:
This remains the last contract-level proof gap between body-level Yul equivalence and full selector-dispatch preservation.

**Risk**: Medium.

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
- Machine-readable trust reports surface this runtime boundary as `keccak256_memory_slice_matches_evm` when contracts use `Expr.keccak256`.

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
| `ERC20.balanceOf` | `erc20_balanceOf_interface` | Target implements `balanceOf(address)` and returns one ABI-encoded `uint256` |
| `ERC20.allowance` | `erc20_allowance_interface` | Target implements `allowance(address,address)` and returns one ABI-encoded `uint256` |
| `ERC20.totalSupply` | `erc20_totalSupply_interface` | Target implements `totalSupply()` and returns one ABI-encoded `uint256` |
| `ERC4626.previewDeposit` | `erc4626_previewDeposit_interface` | Target implements `previewDeposit(uint256)` and returns one ABI-encoded `uint256` |
| `ERC4626.previewRedeem` | `erc4626_previewRedeem_interface` | Target implements `previewRedeem(uint256)` and returns one ABI-encoded `uint256` |
| `Oracle.oracleReadUint256` | `oracle_read_uint256_interface` | Target implements the selected read-only oracle interface and returns one ABI-encoded `uint256` |
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

These removals reduced prior axiom debt. The Layer 3 switch-case bridge still has
a small explicit preservation-side axiom boundary for dispatch-step normalization
and case-body bridging; those active axioms are tracked above.

## Non-Axiom: Arithmetic Semantics

Wrapping modular arithmetic at 2^256 is **proven**, not assumed. All 15 pure builtins (add, sub, mul, div, mod, lt, gt, eq, iszero, and, or, xor, not, shl, shr) have formal wrapping proofs in `Compiler/Proofs/ArithmeticProfile.lean`. The EVMYulLean bridge currently has universal equivalence lemmas for 15 of them (`add`, `sub`, `mul`, `div`, `mod`, `lt`, `gt`, `eq`, `iszero`, `and`, `or`, `xor`, `not`, `shl`, `shr`) in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean`, with no remaining pure builtins relying only on concrete bridge checks. This is a design choice matching EVM semantics, not a trust assumption. See [`docs/ARITHMETIC_PROFILE.md`](docs/ARITHMETIC_PROFILE.md) for the full specification.

## Trust Summary

- Active axioms: 6
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

**Last Updated**: 2026-03-08
