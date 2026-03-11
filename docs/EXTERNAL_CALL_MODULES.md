# External Call Modules (ECM)

External Call Modules are Verity's extension mechanism for external call patterns.
They replace the former hardcoded `Stmt` variants (`safeTransfer`, `callback`,
`ecrecover`, etc.) with a single generic `Stmt.ecm` variant backed by typed,
auditable Lean structures.

## Motivation

Verity's EDSL deliberately restricts raw external calls for safety. Every call
pattern must be explicitly known to the compiler. Before ECMs, adding a new
pattern (e.g., `safeApprove`, `permit`, Uniswap swaps) required modifying the
core `Stmt` inductive type and updating pattern matches across 11+ functions.

ECMs decouple call patterns from the compiler core. Standard patterns ship
in-tree under `Compiler/Modules/`. Third parties can publish their own as
separate Lean packages.

## Architecture

```
ExternalCallModule (Compiler/ECM.lean)
  ├── name : String
  ├── numArgs : Nat
  ├── resultVars : List String
  ├── writesState : Bool
  ├── readsState : Bool
  ├── compile : CompilationContext → List YulExpr → Except String (List YulStmt)
  ├── axioms : List String
  └── proofStatus : proved | assumed | unchecked

Stmt.ecm (mod : ExternalCallModule) (args : List Expr)
```

When the compiler encounters `Stmt.ecm mod args`, it:

1. Validates argument count matches `mod.numArgs`
2. Checks `mod.writesState`/`mod.readsState` against function mutability
3. Validates result variable scoping (no shadowing, no redeclaration)
4. Compiles each `Expr` argument to `YulExpr`
5. Calls `mod.compile ctx compiledArgs` to get `List YulStmt`
6. Injects the result

## Using ECMs in Contract Specs

```lean
import Compiler.Modules.ERC20
import Compiler.Modules.Precompiles

def vaultSpec : CompilationModel := {
  name := "Vault"
  fields := [{ name := "token", ty := .uint256 }]
  functions := [{
    name := "withdraw"
    params := [⟨"to", .address⟩, ⟨"amount", .uint256⟩]
    body := [
      Modules.ERC20.safeTransfer
        (Expr.storage "token")
        (Expr.param "to")
        (Expr.param "amount"),
      Stmt.stop
    ]
  }]
}
```

## Standard Modules

Standard modules ship in `Compiler/Modules/`:

| Module | Function | What it does | Axioms |
|--------|----------|--------------|--------|
| `ERC20.safeTransfer` | `transfer(to, amount)` | ERC-20 transfer with optional-bool-return handling | `erc20_transfer_interface` |
| `ERC20.safeTransferFrom` | `transferFrom(from, to, amount)` | ERC-20 transferFrom with optional-bool-return handling | `erc20_transferFrom_interface` |
| `ERC20.safeApprove` | `approve(spender, amount)` | ERC-20 approve with optional-bool-return handling | `erc20_approve_interface` |
| `Precompiles.ecrecover` | Precompile 0x01 | ECDSA recovery, binds result address | `evm_ecrecover_precompile` |
| `Callbacks.callback` | Parameterized | ABI-encode selector + static args + bytes, call target | `callback_target_interface` |
| `Calls.withReturn` | Parameterized | Generic call/staticcall with single uint256 return | `external_call_abi_interface` |

See `Compiler/Modules/README.md` for the full checklist on adding new standard modules.

## Writing Your Own ECM

### Minimal Example

```lean
import Compiler.ECM
import Compiler.CompilationModel

namespace MyProtocol

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr)

def myCallModule : ExternalCallModule where
  name := "myCall"
  numArgs := 2  -- token, amount
  writesState := true
  readsState := false
  axioms := ["my_protocol_interface"]
  proofStatus := .assumed
  compile := fun _ctx args => do
    let [token, amount] := args | throw "myCall expects 2 arguments"
    -- Your Yul generation logic here
    pure [YulStmt.expr (YulExpr.call "call" [
      YulExpr.call "gas" [], token, YulExpr.lit 0,
      YulExpr.lit 0, YulExpr.lit 0, YulExpr.lit 0, YulExpr.lit 0
    ])]

def myCall (token amount : Expr) : Stmt :=
  .ecm myCallModule [token, amount]
```

### CompilationContext

The `compile` function receives a `CompilationContext` with:

- `isDynamicFromCalldata : Bool` — whether dynamic data (bytes, arrays) comes
  from calldata (external functions) or memory (internal functions). Use this
  to emit `calldatacopy` vs `mcopy` as appropriate.

### Validation

Module-specific validation (selector bounds, parameter name checks, etc.)
should be performed in the `compile` function, which returns `Except String`.
The generic `Stmt.ecm` path handles:

- Argument count validation
- View/pure mutability enforcement via `writesState`/`readsState`
- Result variable shadowing and redeclaration checks

### Testing

Add compile-time tests in `Compiler/CompilationModelFeatureTest.lean` using
`#eval! do` blocks. At minimum, test:

1. Successful compilation (smoke test)
2. Mutability rejection (if `writesState = true`, test view rejection)
3. Any module-specific validation (e.g., selector overflow)

## Third-Party Modules

Protocol-specific modules should live in external Lean packages:

```
my-verity-ecm/
├── MyProtocol/
│   ├── Swap.lean
│   └── Oracle.lean
├── AXIOMS.md        -- Document all trust assumptions
└── lakefile.lean    -- depends on verity (specifically Compiler.ECM)
```

In `lakefile.lean`:
```lean
require verity from git "https://github.com/Th0rgal/verity.git" @ "main"
```

Import path: `import MyProtocol.Swap`.

## Axiom Aggregation

Every ECM declares its trust assumptions in the `axioms` field and tags the
surface with `proofStatus`. When compiling with `--verbose`, the compiler
aggregates both the assumptions and the status buckets, emitting a
localized `Usage-site trust report` section before the contract-level reports:

```
ECM axiom report:
  MorphoBlue:
    [safeTransfer] erc20_transfer_interface
    [safeTransferFrom] erc20_transferFrom_interface
    [callback] callback_target_interface
    [ecrecover] evm_ecrecover_precompile
```

Each assumption is tagged `proved`, `assumed`, or `unchecked`, and localized to the constructor or function that introduced it.

For a machine-readable version, run `verity-compiler --trust-report <path>`. The JSON covers ECM assumptions, linked externals, axiomatized primitives, low-level mechanics, proof-gap categories, and a `hasUncheckedDependencies` flag for CI gating. See [VERIFICATION_STATUS.md](./VERIFICATION_STATUS.md#solidity-interop-support-matrix-issue-586) for the full trust-report schema.

**Fail-closed flags**: a set of `--deny-*` flags lets you reject specific trust surfaces at compile time. Each flag fails the build and reports the exact usage site. See the [full flag table in VERIFICATION_STATUS.md](./VERIFICATION_STATUS.md#solidity-interop-support-matrix-issue-586) for the complete list. The most relevant for ECM users:

| Flag | Rejects |
|------|---------|
| `--deny-unchecked-dependencies` | Any `unchecked` linked external or ECM module |
| `--deny-assumed-dependencies` | Any `assumed` or `unchecked` linked external or ECM module |

## Trust Model

- The compiler trusts that `mod.compile` produces Yul that correctly implements
  the pattern described by the module's name, documentation, and axioms.
- This trust is scoped: a bug in one module does not affect contracts that don't
  use it.
- Standard modules in `Compiler/Modules/` are maintained and audited alongside
  the compiler.
- Third-party modules are outside the Verity team's trust boundary.

See `TRUST_ASSUMPTIONS.md` section 7 and `AXIOMS.md` for details.
