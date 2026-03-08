# Standard External Call Modules

This directory contains Verity's standard ECM (External Call Module) library.
Each module packages a reusable external call pattern as a typed, auditable Lean
structure that the compiler can plug in without modification.

## Available Modules

| File | Modules | Replaces |
|------|---------|----------|
| `ERC20.lean` | `safeTransfer`, `safeTransferFrom`, `safeApprove`, `balanceOf`, `allowance`, `totalSupply` | `Stmt.safeTransfer`, `Stmt.safeTransferFrom`, canonical ERC-20 read wrappers |
| `ERC4626.lean` | `previewDeposit`, `previewRedeem` | canonical vault preview wrappers |
| `Oracle.lean` | `oracleReadUint256` | canonical oracle read wrappers |
| `Precompiles.lean` | `ecrecover` | `Stmt.ecrecover` |
| `Callbacks.lean` | `callback` | `Stmt.callback` |
| `Calls.lean` | `withReturn` | `Stmt.externalCallWithReturn` |

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
(ERC-20 writes and reads, ERC-4626 preview/redeem calls, oracle reads, EVM precompiles,
flash-loan callbacks, generic ABI calls).

Protocol-specific modules (Uniswap, Chainlink, Aave) should live in external Lean
packages that depend on `Compiler.ECM`. See `docs/EXTERNAL_CALL_MODULES.md` for
the full guide.
