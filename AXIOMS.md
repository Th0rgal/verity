# Axioms in Verity

This file is the authoritative registry of axioms used by Verity proof code.

## Policy

Axioms are exceptional. When an axiom exists, it must have:

1. Explicit documentation in this file.
2. Source comment marking it as an axiom and linking to this file.
3. CI checks that validate usage assumptions.
4. A clear elimination path, when practical.

## Current Axioms

**None.** Verity has zero project-level Lean axioms.

- Active axioms: 0

The last remaining axiom (`solidityMappingSlot_lt_evmModulus`) was eliminated
by replacing the opaque FFI-based keccak256 call with the kernel-computable
Keccak engine (`Compiler/Keccak/Sponge.lean`), which exposes the 32-byte
output-length guarantee to Lean's proof system.

## Eliminated Axioms

### 1. `solidityMappingSlot_lt_evmModulus` (eliminated)

**Former location**: `Compiler/Proofs/MappingSlot.lean:125`

**Former statement**:
```lean
axiom solidityMappingSlot_lt_evmModulus (baseSlot key : Nat) :
    solidityMappingSlot baseSlot key < Compiler.Constants.evmModulus
```

**How it was eliminated**:
1. `solidityMappingSlot` was redefined to use `KeccakEngine.keccak256` (kernel-computable)
   instead of `ffi.KEC` (opaque FFI).
2. `squeeze256_size` proves the output is always exactly 32 bytes.
3. `fromByteArrayBigEndian_lt_of_size` proves a ≤32-byte big-endian value is < 2^256.
4. The axiom became a theorem: `solidityMappingSlot_lt_evmModulus` is now proved,
   not assumed.

**Runtime performance**: An `@[implemented_by]` annotation optionally redirects to
the FFI version at runtime for speed, without affecting proof soundness.

### 2. Selector computation (eliminated earlier)

Function selector derivation (`bytes4(keccak256(signature))`) was previously
axiomatic. It is now kernel-computable via the vendored unrolled Keccak engine
in `Compiler/Keccak/` and `Compiler/Selectors.lean`.

### 3. Layer 2 body-simulation axiom (eliminated earlier)

The generic body-simulation axiom in Layer 2 was eliminated through explicit
proof work (issue #1618). `supported_function_correct` is now a real theorem.

### 4. Layer 3 dispatch bridge (eliminated earlier)

The dispatch bridge in Layer 3 was converted from a Lean axiom to an explicit
theorem hypothesis in `Compiler/Proofs/YulGeneration/Preservation.lean`.

## Trusted Cryptographic Primitives (Non-Axiom)

### Kernel-computable selector Keccak-256

**Location**: `Compiler/Selectors.lean`, `Compiler/Keccak/*.lean`

**Role**:
Computes function selectors (`bytes4(keccak256(signature))`) inside Lean's
kernel using a vendored unrolled Keccak-256 engine. This is now a definitional
computation, not a Lean axiom.

**Soundness controls**:
- Fixed selector examples in `Compiler/Selectors.lean`.
- CI cross-checks selectors against `solc --hashes`.
- Selector fixture checks still run as defense in depth.

### Kernel-computable mapping-slot Keccak-256

**Location**: `Compiler/Proofs/MappingSlot.lean`, `Compiler/Keccak/*.lean`

**Role**:
Computes mapping storage slots as `keccak256(abi.encode(key, baseSlot))` using
the same kernel-computable Keccak engine. The output-length bound is proved
structurally via `Compiler/Keccak/SpongeProperties.lean`.

**What we trust**:
- The kernel Keccak implementation matches the EVM's keccak256 (CI cross-checked).
- Two different inputs won't hash to the same slot (standard cryptographic
  assumption — Solidity makes the same one).

**Soundness controls**:
- Mapping-slot abstraction boundary checks in CI.
- End-to-end regression suites that exercise mapping reads/writes.
- CI cross-checks kernel Keccak output against FFI Keccak output.

## External Call Module (ECM) Assumptions

When your contract calls an external contract (like an ERC-20 token), Verity
can't prove that the *other* contract works correctly. Instead, it documents
the assumption: "we assume this address implements the expected interface."

These are **not** proof-system axioms — they are interface assumptions scoped
to contracts that use the module. The compiler lists all of them at compile
time in `--verbose` output. Use `--deny-unchecked-dependencies` to make
compilation fail if any assumption hasn't been reviewed.

### Standard Module Assumptions

| Module | Assumption | Meaning |
|--------|------------|---------|
| `ERC20.safeTransfer` | `erc20_transfer_interface` | Target implements ERC-20 `transfer(address,uint256)` |
| `ERC20.safeTransferFrom` | `erc20_transferFrom_interface` | Target implements ERC-20 `transferFrom(address,address,uint256)` |
| `ERC20.safeApprove` | `erc20_approve_interface` | Target implements ERC-20 `approve(address,uint256)` |
| `ERC20.balanceOf` | `erc20_balanceOf_interface` | Target implements `balanceOf(address)` and returns a `uint256` |
| `ERC20.allowance` | `erc20_allowance_interface` | Target implements `allowance(address,address)` and returns a `uint256` |
| `ERC20.totalSupply` | `erc20_totalSupply_interface` | Target implements `totalSupply()` and returns a `uint256` |
| `ERC4626.previewDeposit` | `erc4626_previewDeposit_interface` | Target implements `previewDeposit(uint256)` and returns a `uint256` |
| `ERC4626.previewMint` | `erc4626_previewMint_interface` | Target implements `previewMint(uint256)` and returns a `uint256` |
| `ERC4626.previewWithdraw` | `erc4626_previewWithdraw_interface` | Target implements `previewWithdraw(uint256)` and returns a `uint256` |
| `ERC4626.previewRedeem` | `erc4626_previewRedeem_interface` | Target implements `previewRedeem(uint256)` and returns a `uint256` |
| `ERC4626.convertToAssets` | `erc4626_convertToAssets_interface` | Target implements `convertToAssets(uint256)` and returns a `uint256` |
| `ERC4626.convertToShares` | `erc4626_convertToShares_interface` | Target implements `convertToShares(uint256)` and returns a `uint256` |
| `ERC4626.totalAssets` | `erc4626_totalAssets_interface` | Target implements `totalAssets()` and returns a `uint256` |
| `ERC4626.asset` | `erc4626_asset_interface` | Target implements `asset()` and returns an `address` |
| `ERC4626.maxDeposit` | `erc4626_maxDeposit_interface` | Target implements `maxDeposit(address)` and returns a `uint256` |
| `ERC4626.maxMint` | `erc4626_maxMint_interface` | Target implements `maxMint(address)` and returns a `uint256` |
| `ERC4626.maxWithdraw` | `erc4626_maxWithdraw_interface` | Target implements `maxWithdraw(address)` and returns a `uint256` |
| `ERC4626.maxRedeem` | `erc4626_maxRedeem_interface` | Target implements `maxRedeem(address)` and returns a `uint256` |
| `ERC4626.deposit` | `erc4626_deposit_interface` | Target implements `deposit(uint256,address)` and returns a `uint256` |
| `Oracle.oracleReadUint256` | `oracle_read_uint256_interface` | Target implements the selected oracle read interface and returns a `uint256` |
| `Precompiles.ecrecover` | `evm_ecrecover_precompile` | EVM precompile at address 0x01 behaves per Yellow Paper |
| `Callbacks.callback` | `callback_target_interface` | Callback target processes ABI-encoded arguments correctly |
| `Calls.withReturn` | `external_call_abi_interface` | Target contract function matches declared selector and ABI |

### Third-Party Module Assumptions

Third-party ECMs (external Lean packages) document their assumptions in their own
`AXIOMS.md`. All assumptions — standard and third-party — are listed at compile
time. See `docs/EXTERNAL_CALL_MODULES.md` for details.

**Risk**: Low. These are interface assumptions (not proof-system extensions)
scoped to contracts that use the module.

## Non-Axiom: Arithmetic

All 18 low-level EVM arithmetic builtins are **proven correct** — not assumed.
The proofs show that Verity's arithmetic matches EVM arithmetic (wrapping at
2^256) for *all* possible inputs, not just test cases. The EVMYulLean bridge
currently has universal equivalence lemmas for 18 of them (`add`, `sub`, `mul`,
`div`, `mod`, `addmod`, `mulmod`, `lt`, `gt`, `eq`, `iszero`, `and`, `or`,
`xor`, `not`, `shl`, `shr`, `byte`), with no remaining pure builtins relying
only on concrete bridge checks.

Additionally, 8 higher-level expression operators have proven compilation
correctness in the `ExprCompileCore` fragment: `min`, `max`, `ceilDiv`, `ite`
(conditional), `wMulDown`, `wDivUp`, `mulDivDown`, and `mulDivUp`. See
[`docs/ARITHMETIC_PROFILE.md`](docs/ARITHMETIC_PROFILE.md) for the full
specification.

## Trust Summary

- Active axioms: 0
- Production blockers from axioms: 0
- Enforcement: `scripts/check_axioms.py` ensures this file tracks exact source locations.
- All internal compiler functions are proven to terminate (no axioms involved).
- The macro front-end and typed-IR pipeline do not use any
  axioms. The typed-IR compiler has zero `sorry`.

## Maintenance Rule

Any commit that adds, removes, renames, or moves an axiom must update this file in the same commit.

If this file is stale, trust analysis is stale.

**Last Updated**: 2026-04-09
