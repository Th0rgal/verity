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
aggregates both the assumptions and the status buckets, and now emits a
localized `Usage-site trust report` section before the contract-level reports:

```
ECM axiom report:
  MorphoBlue:
    [safeTransfer] erc20_transfer_interface
    [safeTransferFrom] erc20_transferFrom_interface
    [callback] callback_target_interface
    [ecrecover] evm_ecrecover_precompile
```

This makes the trust boundary explicit and auditable. A team choosing which
modules to use is choosing which trust assumptions to accept, and whether the
surface is merely `assumed` or fully `unchecked`. The localized usage-site
section mirrors the same boundary at the constructor/function level, including
low-level mechanics, linked external/module `proofStatus`, and per-site axioms.

For machine-readable audit trails, `verity-compiler --trust-report <path>` now
emits per-contract JSON that includes:
- first-class low-level call / returndata mechanics used by the spec
- not-modeled raw event-emission mechanics used by the spec (`rawLog`)
- axiomatized primitives used directly by the spec (for example `keccak256`)
- linked external assumptions with `status`
- ECM assumption entries (`module`, `assumption`) plus per-module `status`
- explicit `proofStatus.proved` / `proofStatus.assumed` / `proofStatus.unchecked`
  buckets for foreign trust surfaces
- `usageSites` entries that localize those mechanics and assumptions to the
  constructor or individual function that introduced them
- `notModeledProxyUpgradeability` entries that isolate `delegatecall` as the
  current proxy / upgradeability proof gap tracked under issue `#1420`
- `partiallyModeledLinearMemoryMechanics` entries that isolate the current
  linear-memory proof gap (`mload`, `mstore`, `calldatacopy`,
  `returndataCopy`, `returndataOptionalBoolAt`) at both contract and
  usage-site granularity
- `partiallyModeledRuntimeIntrospection` entries that isolate the current
  runtime-introspection proof gap (`blockNumber`, `contractAddress`,
  `chainid`) at both contract and usage-site granularity
- `hasUncheckedDependencies` so CI/reporting layers can fail or warn on
  contracts that are not eligible for full-verification claims

For verification-oriented compiles, `verity-compiler --deny-unchecked-dependencies`
turns that report into a hard gate: compilation exits nonzero if any selected
contract still depends on an `unchecked` linked external or ECM module, and the
failure now cites the exact constructor/function usage site that introduced the
unchecked dependency. For proof-strict runs that require fully proved foreign
surfaces, `verity-compiler --deny-assumed-dependencies` fails closed on both
`assumed` and `unchecked` linked externals / ECM modules and localizes the
diagnostic to the exact usage site. For primitive-proof-strict runs,
`verity-compiler --deny-axiomatized-primitives` fails closed when any selected
contract still uses axiomatized primitives such as `keccak256`, again citing
the exact constructor/function usage site. For memory-proof-strict runs,
`verity-compiler --deny-linear-memory-mechanics` fails closed when any selected
contract still uses partially modeled linear-memory mechanics, again citing the
exact constructor/function usage site. For event-proof-strict runs,
`verity-compiler --deny-event-emission` fails closed when any selected contract
still uses raw `rawLog` event emission, again citing the exact
constructor/function usage site. For low-level-proof-strict runs,
`verity-compiler --deny-low-level-mechanics` fails closed when any selected
contract still uses first-class low-level call / returndata mechanics, again
citing the exact constructor/function usage site. For proxy-proof-strict runs,
`verity-compiler --deny-proxy-upgradeability` fails closed when any selected
contract still uses `delegatecall`, again citing the exact constructor/function
usage site. For runtime-proof-strict runs,
`verity-compiler --deny-runtime-introspection` fails closed when any selected
contract still uses partially modeled runtime-introspection primitives, again
citing the exact constructor/function usage site.

## Trust Model

- The compiler trusts that `mod.compile` produces Yul that correctly implements
  the pattern described by the module's name, documentation, and axioms.
- This trust is scoped: a bug in one module does not affect contracts that don't
  use it.
- Standard modules in `Compiler/Modules/` are maintained and audited alongside
  the compiler.
- Third-party modules are outside the Verity team's trust boundary.

See `TRUST_ASSUMPTIONS.md` section 7 and `AXIOMS.md` for details.
