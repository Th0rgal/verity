/- 
  Compiler.Specs: Declarative Contract Specifications

  Shipped compiler inputs are the macro-generated `CompilationModel` values
  emitted by `verity_contract`. This module keeps compatibility aliases for
  existing tests and the manual `cryptoHashSpec` special case.
-/

import Compiler.CompilationModel
import Contracts.MacroContracts

namespace Compiler.Specs

open Compiler.CompilationModel

/-!
## Macro-Generated Specification Aliases
-/

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def simpleStorageSpec : CompilationModel := Contracts.MacroContracts.SimpleStorage.spec

/-- Legacy compatibility shim preserving the historical 3-function Counter surface. -/
def counterSpec : CompilationModel :=
  let canonical := Contracts.MacroContracts.Counter.spec
  { canonical with
    functions := canonical.functions.filter fun fn =>
      fn.name = "increment" || fn.name = "decrement" || fn.name = "getCount" }

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def ownedSpec : CompilationModel := Contracts.MacroContracts.Owned.spec

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def ledgerSpec : CompilationModel := Contracts.MacroContracts.Ledger.spec

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def ownedCounterSpec : CompilationModel := Contracts.MacroContracts.OwnedCounter.spec

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def simpleTokenSpec : CompilationModel := Contracts.MacroContracts.SimpleToken.spec

/-- Legacy compatibility alias. Canonical source is macro-generated. -/
def safeCounterSpec : CompilationModel := Contracts.MacroContracts.SafeCounter.spec

/-- ERC20 spec alias for test/proof convenience. Uses the macro-generated spec. -/
def erc20Spec : CompilationModel := Contracts.MacroContracts.ERC20.spec

/-- ERC721 spec alias for test/proof convenience. Uses the macro-generated spec. -/
def erc721Spec : CompilationModel := Contracts.MacroContracts.ERC721.spec

/-!
## CryptoHash Specification (External Library Linking Demo)

Demonstrates `Expr.externalCall` for linking external Yul libraries at
compile time. The EDSL placeholder in `Contracts/CryptoHash/Contract.lean`
uses simple addition; the `CompilationModel` below calls the real library
functions (`PoseidonT3_hash`, `PoseidonT4_hash`) which are injected by
the Linker when you pass `--link examples/external-libs/PoseidonT3.yul`.
-/

def cryptoHashSpec : CompilationModel := {
  name := "CryptoHash"
  fields := [
    { name := "lastHash", ty := FieldType.uint256 }
  ]
  «constructor» := none
  externals := [
    { name := "PoseidonT3_hash"
      params := [ParamType.uint256, ParamType.uint256]
      returnType := some ParamType.uint256
      axiomNames := ["poseidon_t3_deterministic", "poseidon_t3_collision_resistant"] },
    { name := "PoseidonT4_hash"
      params := [ParamType.uint256, ParamType.uint256, ParamType.uint256]
      returnType := some ParamType.uint256
      axiomNames := ["poseidon_t4_deterministic", "poseidon_t4_collision_resistant"] }
  ]
  functions := [
    { name := "storeHashTwo"
      params := [
        { name := "a", ty := ParamType.uint256 },
        { name := "b", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.letVar "h" (Expr.externalCall "PoseidonT3_hash" [Expr.param "a", Expr.param "b"]),
        Stmt.setStorage "lastHash" (Expr.localVar "h"),
        Stmt.stop
      ]
    },
    { name := "storeHashThree"
      params := [
        { name := "a", ty := ParamType.uint256 },
        { name := "b", ty := ParamType.uint256 },
        { name := "c", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.letVar "h" (Expr.externalCall "PoseidonT4_hash" [Expr.param "a", Expr.param "b", Expr.param "c"]),
        Stmt.setStorage "lastHash" (Expr.localVar "h"),
        Stmt.stop
      ]
    },
    { name := "getLastHash"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "lastHash")
      ]
    }
  ]
}

/-!
## Generate All Contracts

`allSpecs` lists every contract that compiles without external dependencies.
`cryptoHashSpec` is excluded because it requires `--link` flags for external
Yul libraries (PoseidonT3/T4). Use `lake exe verity-compiler --link ...` to
compile it separately.

**Adding a new contract (canonical path)**: add a `verity_contract` declaration
in `Contracts/MacroContracts/`, then add the generated `<Name>.spec`
to `allSpecs` below.

`Compiler.Specs.*Spec` values are compatibility aliases only, except for
linked-library workflows like `cryptoHashSpec`.
Selectors are still auto-computed by `computeSelectors`.
-/

def allSpecs : List CompilationModel := [
  simpleStorageSpec,
  counterSpec,
  ownedSpec,
  ledgerSpec,
  ownedCounterSpec,
  simpleTokenSpec,
  safeCounterSpec,
  erc20Spec
]

end Compiler.Specs
