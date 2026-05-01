# Prompt: Unlink Audit Readiness In Verity Core

You are working in the `lfglabs-dev/verity` repository. The priority is to make
the Verity-core language/compiler surface clean enough for a line-by-line Unlink
audit model, while keeping Unlink-specific cryptographic and protocol
assumptions out of Verity core.

Do not implement an Unlink model in this repository. Do not add built-in
Poseidon, Permit2, Lazy-IMT, or Groth16 verifier semantics to Verity core. Those
belong in a separate `unlink-verity` package as external declarations or
package-local ECMs with explicit axiom names and proof-status tags.

## Goal

Implement and document the generic Verity-core features needed to express
Unlink cleanly:

1. ETH-aware generic external call ECM.
2. ECM/trust-boundary documentation sync.
3. Verification/docs for mutable accumulators in `forEach`.
4. Verification/docs for multi-value internal helper returns.
5. `abiEncodePacked` helper.
6. `sha256` / `sha256Packed` helper.
7. BN254 scalar field constant and `modField` helper.

## Current Status Checkpoint

Before starting new work, inspect the current repository state and avoid
reimplementing items that are already present. As of this checkpoint, the
expected Verity-core surface is:

- `Compiler.Modules.Calls.bubblingValueCall` for generic
  `call{value: v}(data)` over explicit memory slices, with revert-returndata
  bubbling and trust-report metadata.
- `Compiler.Modules.Precompiles.sha256Memory` and the shorter
  `Compiler.Modules.Precompiles.sha256` alias for SHA-256 precompile 0x02 over
  caller-provided memory slices.
- `Compiler.Modules.Hashing.abiEncodePackedWords` /
  `Compiler.Modules.Hashing.abiEncodePacked` and
  `Compiler.Modules.Hashing.sha256PackedWords` /
  `Compiler.Modules.Hashing.sha256Packed` for static 32-byte-word packed
  preimages.
- `Compiler.Modules.Hashing.abiEncodePackedStaticSegments` and
  `Compiler.Modules.Hashing.sha256PackedStaticSegments` for explicit 1- to
  32-byte static segments such as address-sized preimages.
- `Verity.Stdlib.Math.SNARK_SCALAR_FIELD` and
  `Verity.Stdlib.Math.modField`.
- Compilation-model tests for mutable `Stmt.assignVar` inside `Stmt.forEach`
  and macro smoke coverage for tuple-return helper bindings lowering to
  `Stmt.internalCallAssign`.

Known remaining limitation: `verity_contract` executable fallback source still
rejects mutating a Lean `let mut` local from inside a nested `forEach` body.
The compilation model supports the desired accumulator shape directly via
`Stmt.assignVar`; macro-authored contracts that need executable fallback tests
should use explicit scratch storage/memory until the fallback limitation is
removed.

Good follow-up work should either remove that fallback limitation cleanly, add
tests/docs around a genuinely missing edge case, or tighten trust-boundary
documentation. Do not keep adding parallel helper names for already-covered
static packed hashing semantics.

## Required Implementation Order

### 1. ETH-aware generic external call ECM

Add a reusable module under `Compiler/Modules/Calls.lean` for Solidity-style
arbitrary external calls equivalent to:

```solidity
(bool ok, bytes memory returndata) = target.call{value: value}(data);
if (!ok) {
    assembly {
        revert(add(returndata, 32), mload(returndata))
    }
}
```

The API should be protocol-agnostic and usable by UnlinkAdapter-style execution
of arbitrary call data. It should support:

- target address
- ETH value
- calldata/input offset and size, or the closest existing bytes-like Verity
  surface if one already exists
- configurable output handling if the existing ECM design supports it
- exact revert-data bubbling on failed calls
- correct `writesState`, `readsState`, `axioms`, and `proofStatus` metadata
- clear validation errors for unsupported argument shapes

Do not weaken CEI or mutability checks. If the module writes state, it must be
marked accordingly.

Add compile-time tests in `Compiler/CompilationModelFeatureTest.lean` covering:

- lowering uses `call`, not `staticcall`
- the call value operand is wired from the user argument
- failure path copies `returndatasize()` bytes and reverts with that payload
- invalid argument counts fail closed
- trust-report / ECM metadata remains visible through existing reporting paths
  if there is an existing test pattern for that

### 2. Documentation sync

Update:

- `docs/EXTERNAL_CALL_MODULES.md`
- `docs/INTERPRETER_FEATURE_MATRIX.md`
- `docs/ROADMAP.md`

The docs must state the package split:

- Verity core owns generic Solidity/EVM modeling surfaces such as low-level call
  mechanics, returndata bubbling, ABI helper ergonomics, loop/mutable-local
  syntax, multi-value helper return syntax, and trust reporting.
- `unlink-verity` owns Unlink-specific assumptions for Poseidon, Permit2,
  Lazy-IMT, and Groth16 verifier behavior.

Avoid wording that implies the full Unlink model or Unlink-specific assumptions
should live in Verity core.

### 3. Mutable accumulators inside `forEach`

Check whether macro syntax already supports this pattern:

```lean
let mut total := 0
forEach "i" (arrayLength notes) (do
  let amount := (arrayElement notes i).amount
  total := add total amount)
return total
```

If it already works, add a focused smoke/feature test and docs example. If it
does not work, first preserve the current boundary with a regression test and
docs. Then implement the smallest macro/EDSL change needed so assignment to a
mutable local inside `forEach` lowers to `Stmt.assignVar`, including whatever
executable fallback adjustment is needed for `verity_contract` source terms.

Do not introduce a separate `forEachAccum` unless the existing assignment syntax
cannot be made to work cleanly.

### 4. Multi-value internal helper returns

Check whether macro syntax already supports `_buildPublicSignals`-style helper
returns. Prefer a syntax that maps to existing `Stmt.internalCallAssign`, for
example a tuple binding if that is already supported by local conventions.

Add a smoke/feature test and docs example. If macro support is missing, add the
smallest syntax extension that reuses the existing compilation-model
`Stmt.internalCallAssign` machinery.

### 5. `abiEncodePacked` helper

Add helpers for static packed encoding used in hash preimages. The first version
may support only a list of word-sized `Expr` values; a higher-ROI follow-up is a
static segment helper with explicit 1- to 32-byte widths for address-sized and
other sub-word preimages.

Expected behavior:

- writes each word at consecutive 32-byte offsets
- for segment helpers, left-aligns sub-word values and places subsequent
  segments at byte-precise offsets
- computes the correct total byte length
- returns `keccak256(offset, length)` or expands to existing `Expr.keccak256`
  support
- avoids ad hoc offset arithmetic in user contracts

Add tests that inspect generated Yul or compilation-model output for correct
offsets and length.

### 6. `sha256` / `sha256Packed` helper

Add a helper for SHA-256 precompile 0x02:

- emits `staticcall(gas(), 2, inputOffset, inputSize, outputOffset, 32)`
- reverts on precompile failure
- returns `mload(outputOffset)` as the digest word

If `sha256Packed` is added, it should reuse the same packed memory layout as
`abiEncodePacked` but route to the SHA-256 precompile instead of `keccak256`.

Add generated-Yul tests for precompile address, input size, output size, and
failure handling.

### 7. BN254 scalar helper

Add a generic, documented helper for circuit-facing field reductions:

```lean
SNARK_SCALAR_FIELD =
21888242871839275222246405745257275088548364400416034343698204186575808495617

modField x = mod x SNARK_SCALAR_FIELD
```

Place it in a generic arithmetic/ZK helper location consistent with the repo's
existing module layout. Add a small test or compile-time check.

## Already Done: Do Not Reimplement

- `address(this).balance` / `selfbalance()` support has already landed.
- Named struct field access on calldata array elements is already supported via
  `struct` declarations and `(arrayElement xs i).field`.
- ERC-20 `balanceOf`, `allowance`, and `totalSupply` ECMs already exist in
  `Compiler/Modules/ERC20.lean`.
- Low-level primitives such as `mstore`, `keccak256`, `staticcall`, `call`,
  `returndataSize`, `returndataCopy`, and `revertReturndata` already exist at
  the macro or compilation-model level.

## Verification

Before opening a PR, run as much local validation as practical:

```bash
lake build Contracts Compiler PrintAxioms
python3 scripts/generate_print_axioms.py --check
make check
```

If a narrower test is added for a specific feature, run it directly as well.
Report any tests that could not be run and why.

## PR Expectations

Keep the PR Verity-core only. The final PR description should include:

- summary of implemented generic features
- tests run
- exact docs changed
- explicit statement that Poseidon, Permit2, Lazy-IMT, Groth16, and the full
  Unlink model remain in `unlink-verity`
- trust-boundary notes for every new ECM or helper that emits low-level calls
