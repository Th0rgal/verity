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
When a smart contract has multiple functions, the EVM uses the first 4 bytes of
`keccak256("functionName(argTypes)")` to decide which function to call. This axiom
tells Lean "trust the external keccak256 implementation for this computation."

**Why this is currently an axiom**:
Reimplementing and proving keccak256 correct inside Lean would be a large effort
with little benefit — the real keccak256 is a well-tested cryptographic standard.
Instead, Verity treats it as a black box and validates its outputs in CI.

**Soundness controls**:

- CI cross-checks selectors against `solc --hashes`.
- CI runs selector fixture checks to detect regressions.
- Compilation and tests fail if selector consistency drifts.

**Risk**: Low.

### 2. `supported_function_body_correct_from_exact_state`

**Location**: `Compiler/Proofs/IRGeneration/Function.lean:915`

**Statement**:
```lean
axiom supported_function_body_correct_from_exact_state
```

**Purpose**:
Says that if the contract's storage and runtime state are set up correctly,
then the compiled version of a function body behaves identically to the
original source code.

**Why this is currently an axiom**:
Proving that compiled code matches source code for every supported statement
type requires a large induction proof. The project is building this proof
incrementally:

- **Proved:** Simple ("core") statement patterns — let bindings, assignments,
  require checks, return, and stop.
- **Proved:** Terminal control flow — if/else branching and the full
  terminal-core recursion.
- **Remaining:** Storage writes, mapping writes, and other complex statement
  patterns.

Each time a new pattern is proved, this axiom's scope shrinks. The goal is to
eliminate it entirely. The exact-state setup proof is already done, and the
compiler now bypasses this axiom for both `StmtListCompileCore` and
`StmtListTerminalCore` bodies.

The terminal `ite` branch-entry blocker described in issue `#1564` is now
discharged: the remaining gap is no longer about entering checked terminal
branches, but about proving the broader non-terminal supported statement shapes
such as storage writes and mapping writes.

**Technical note on fuel:**
The proof system uses a "fuel" counter to bound how many steps the interpreter
can take. Nested code blocks (like if-statements inside if-statements) need more
fuel than flat code. This axiom requires that enough fuel is provided to handle
the nesting depth of the function body. The caller provides this automatically
based on the body's structure.

**Risk**: Medium.

## Trusted Cryptographic Primitive (Non-Axiom)

### `ffi.KEC` (keccak256 via FFI)

**Location**: used by `Compiler/Proofs/MappingSlot.lean` (`solidityMappingSlot`)

**Role**:
Computes mapping storage slots as `keccak256(abi.encode(key, baseSlot))`.
In Solidity, mappings don't store values at sequential slots — they hash the
key with the base slot to get a storage address. This function does that
hashing so proofs can reason about where mapping values live.

**Why this is NOT a Lean axiom**:
This is a call to an external keccak256 library (like calling a C function
from Lean), not a logical assumption in the proof system. The proofs don't
claim keccak256 is correct — they call the real implementation at runtime.
The trust here is the same trust every Ethereum node already places in their
keccak implementation.

**What we trust**:
- The keccak256 implementation is correct.
- Two different inputs won't hash to the same slot (standard cryptographic
  assumption — Solidity makes the same one).

**How this is tracked**: The compiler flags this as a runtime trust boundary
in `--verbose` output.

**Soundness controls**:
- Mapping-slot abstraction boundary checks in CI.
- End-to-end regression suites that exercise mapping reads/writes.

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

All 15 arithmetic operations (add, sub, mul, div, mod, lt, gt, eq, iszero,
and, or, xor, not, shl, shr) are **proven correct** — not assumed. The proofs
show that Verity's arithmetic matches EVM arithmetic (wrapping at 2^256) for
*all* possible inputs, not just test cases. The EVMYulLean bridge currently has
universal equivalence lemmas for 15 of them (`add`, `sub`, `mul`, `div`,
`mod`, `lt`, `gt`, `eq`, `iszero`, `and`, `or`, `xor`, `not`, `shl`, `shr`),
with no remaining pure builtins relying only on concrete bridge checks. See
[`docs/ARITHMETIC_PROFILE.md`](docs/ARITHMETIC_PROFILE.md) for the full
specification.

## Trust Summary

- Active axioms: 2
- Production blockers from axioms: 0
- Enforcement: `scripts/check_axioms.py` ensures this file tracks exact source locations.
- All internal compiler functions are proven to terminate (no axioms involved).
- The macro front-end, semantic bridge, and typed-IR pipeline do not use any
  axioms. Both `SemanticBridge.lean` and the typed-IR compiler have zero `sorry`.

## Maintenance Rule

Any commit that adds, removes, renames, or moves an axiom must update this file in the same commit.

If this file is stale, trust analysis is stale.

**Last Updated**: 2026-03-11
