# Standard External Call Modules

This directory contains Verity's standard ECM (External Call Module) library.
Each module packages a reusable external call pattern as a typed, auditable Lean
structure that the compiler can plug in without modification.

## Available Modules

| File | Modules | Replaces |
|------|---------|----------|
| `ERC20.lean` | `safeTransfer`, `safeTransferFrom`, `safeApprove`, `balanceOf`, `allowance`, `totalSupply` | `Stmt.safeTransfer`, `Stmt.safeTransferFrom`, canonical ERC-20 read wrappers |
| `ERC4626.lean` | `previewDeposit`, `previewMint`, `previewWithdraw`, `previewRedeem`, `convertToAssets`, `convertToShares`, `totalAssets`, `asset`, `maxDeposit`, `maxMint`, `maxWithdraw`, `maxRedeem`, `deposit` | canonical vault preview/conversion wrappers plus a standard deposit wrapper |
| `Hashing.lean` | `abiEncodePackedWords` / `abiEncodePacked`, `sha256PackedWords` / `sha256Packed`, `abiEncodePackedStaticSegments`, `sha256PackedStaticSegments` | handwritten static packed hash preimage `mstore` choreography |
| `Oracle.lean` | `oracleReadUint256` | canonical oracle read wrappers |
| `Precompiles.lean` | `ecrecover`, `sha256Memory` / `sha256` | `Stmt.ecrecover`, handwritten SHA-256 precompile calls |
| `Callbacks.lean` | `callback` | `Stmt.callback` |
| `Calls.lean` | `withReturn`, `bubblingValueCall`, `bubblingValueCallNoOutput` | `Stmt.externalCallWithReturn`, handwritten low-level `call{value: ...}` wrappers |

## Usage

```lean
import Compiler.Modules.ERC20

-- In a function body:
body := [
  Modules.ERC20.safeTransfer
    (Expr.storage "token")
    (Expr.param "to")
    (Expr.param "amount"),
  Stmt.stop
]
```

Static-word packed hashing helpers are available for ZK/audit preimages whose
items are already 32-byte words:

```lean
Modules.Hashing.abiEncodePackedWords
  "digest"
  [Expr.param "root", Expr.param "contextHash", Expr.param "nullifier"]

Modules.Hashing.sha256PackedWords
  "publicSignalDigest"
  [Expr.param "root", Expr.param "contextHash"]
```

The shorter `Modules.Hashing.abiEncodePacked` and
`Modules.Hashing.sha256Packed` aliases are available for the same static-word
semantics. These helpers write words contiguously at scratch memory offset zero.
For static packed preimages with byte-width segments such as address-sized
values, use the segment helpers:

```lean
Modules.Hashing.abiEncodePackedStaticSegments
  "digest"
  [(Expr.param "who", 20), (Expr.param "amount", 32)]

Modules.Hashing.sha256PackedStaticSegments
  "publicSignalDigest"
  [(Expr.param "who", 20), (Expr.param "contextHash", 32)]
```

Segment widths are explicit byte counts from 1 to 32. Sub-word values are
left-aligned before `mstore`, and subsequent segments are placed at byte-precise
offsets. These helpers still do not implement dynamic Solidity packed encoding
for `bytes` or `string`.

## Writing a New Standard Module

1. Create `Compiler/Modules/YourModule.lean`.
2. Import `Compiler.ECM` and `Compiler.CompilationModel`.
3. Define an `ExternalCallModule` structure with:
   - `name`: human-readable identifier for error messages
   - `numArgs`: expected argument count
   - `resultVars`: names of local variables this module binds (empty for fire-and-forget)
   - `writesState` / `readsState`: mutability flags (govern view/pure enforcement)
   - `compile`: function producing `List YulStmt` from compiled `YulExpr` arguments
   - `axioms`: trust assumptions this module introduces
4. Add a convenience wrapper that returns `Stmt.ecm yourModule args`.
5. Add compile-time tests in `CompilationModelFeatureTest.lean`.

### Checklist

- [ ] Module compiles (`lake build Compiler.Modules.YourModule`)
- [ ] Convenience wrapper returns `Stmt.ecm` with correct argument list
- [ ] `writesState`/`readsState` flags are accurate (tested via view/pure rejection)
- [ ] `axioms` list documents all trust assumptions
- [ ] Compile-time smoke test added to `CompilationModelFeatureTest.lean`
- [ ] Any validation (selector bounds, parameter names) is in `compile`, not deferred

## Standard vs. Third-Party

Standard modules live here and ship with Verity. They cover widely-used patterns
(ERC-20 writes and reads, ERC-4626 preview calls, oracle reads, EVM precompiles,
flash-loan callbacks, generic ABI calls).

Protocol-specific modules (Uniswap, Chainlink, Aave) should live in external Lean
packages that depend on `Compiler.ECM`. See `docs/EXTERNAL_CALL_MODULES.md` for
the full guide.
