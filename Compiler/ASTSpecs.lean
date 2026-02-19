/-
  Compiler.ASTSpecs: AST-Based Contract Specifications

  Defines `ASTContractSpec` — a lightweight contract descriptor that pairs
  Verity.AST.Stmt function bodies with ABI metadata (Solidity names, param
  types). Used by `ASTDriver` to compile unified AST directly to Yul,
  bypassing the ContractSpec layer.

  This is Phase 4 of issue #364 (Unify EDSL/ContractSpec).
-/

import Verity.AST
import Verity.AST.SimpleStorage
import Verity.AST.Counter
import Verity.AST.Owned
import Verity.AST.OwnedCounter
import Verity.AST.Ledger
import Verity.AST.SafeCounter
import Verity.AST.SimpleToken
import Compiler.ContractSpec

namespace Compiler.ASTSpecs

open Verity.AST
open Compiler.ContractSpec (ParamType Param FieldType)

/-!
## AST Contract Specification

A minimal record that holds everything needed to compile an AST contract:
- Contract name (for output filename and Yul object name)
- Function list (Solidity name, ABI params, body as `Verity.AST.Stmt`)
- Optional constructor body
- Whether the contract uses mappings (for `mappingSlot` helper injection)
-/

/-- ABI-level parameter type for AST functions. Reuses ContractSpec.ParamType. -/
inductive ASTReturnType
  | uint256
  | address
  | unit
  deriving Repr

structure ASTFunctionSpec where
  /-- Solidity-facing function name (used for selector computation). -/
  name : String
  /-- ABI parameters (used for calldata loading and selector computation). -/
  params : List Param
  /-- Return type. -/
  returnType : ASTReturnType
  /-- Function body as a unified AST statement. -/
  body : Stmt
  deriving Repr

structure ASTConstructorSpec where
  /-- Constructor parameters (loaded from end of bytecode). -/
  params : List Param
  /-- Constructor body as a unified AST statement. -/
  body : Stmt
  deriving Repr

structure ASTContractSpec where
  /-- Contract name (determines output filename). -/
  name : String
  /-- Optional constructor. -/
  constructor : Option ASTConstructorSpec := none
  /-- External functions (dispatched via selector). -/
  functions : List ASTFunctionSpec
  /-- Whether the contract uses mapping storage. -/
  usesMapping : Bool := false
  deriving Repr

/-!
## Contract Definitions

Each contract pairs its Solidity ABI metadata with the AST function bodies
defined in `Verity/AST/*.lean`.
-/

def simpleStorageSpec : ASTContractSpec := {
  name := "SimpleStorage"
  functions := [
    { name := "store"
      params := [{ name := "value", ty := ParamType.uint256 }]
      returnType := .unit
      body := SimpleStorage.storeAST },
    { name := "retrieve"
      params := []
      returnType := .uint256
      body := SimpleStorage.retrieveAST }
  ]
}

def counterSpec : ASTContractSpec := {
  name := "Counter"
  functions := [
    { name := "increment"
      params := []
      returnType := .unit
      body := Counter.incrementAST },
    { name := "decrement"
      params := []
      returnType := .unit
      body := Counter.decrementAST },
    { name := "getCount"
      params := []
      returnType := .uint256
      body := Counter.getCountAST }
  ]
}

def ownedSpec : ASTContractSpec := {
  name := "Owned"
  constructor := some {
    params := [{ name := "initialOwner", ty := ParamType.address }]
    body := Owned.constructorAST
  }
  functions := [
    { name := "transferOwnership"
      params := [{ name := "newOwner", ty := ParamType.address }]
      returnType := .unit
      body := Owned.transferOwnershipAST },
    { name := "getOwner"
      params := []
      returnType := .address
      body := Owned.getOwnerAST }
  ]
}

def ownedCounterSpec : ASTContractSpec := {
  name := "OwnedCounter"
  constructor := some {
    params := [{ name := "initialOwner", ty := ParamType.address }]
    body := OwnedCounter.constructorAST
  }
  functions := [
    { name := "increment"
      params := []
      returnType := .unit
      body := OwnedCounter.incrementAST },
    { name := "decrement"
      params := []
      returnType := .unit
      body := OwnedCounter.decrementAST },
    { name := "getCount"
      params := []
      returnType := .uint256
      body := OwnedCounter.getCountAST },
    { name := "getOwner"
      params := []
      returnType := .address
      body := OwnedCounter.getOwnerAST },
    { name := "transferOwnership"
      params := [{ name := "newOwner", ty := ParamType.address }]
      returnType := .unit
      body := OwnedCounter.transferOwnershipAST }
  ]
}

def ledgerSpec : ASTContractSpec := {
  name := "Ledger"
  usesMapping := true
  functions := [
    { name := "deposit"
      params := [{ name := "amount", ty := ParamType.uint256 }]
      returnType := .unit
      body := Ledger.depositAST },
    { name := "withdraw"
      params := [{ name := "amount", ty := ParamType.uint256 }]
      returnType := .unit
      body := Ledger.withdrawAST },
    { name := "transfer"
      params := [
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := .unit
      body := Ledger.transferAST },
    { name := "getBalance"
      params := [{ name := "addr", ty := ParamType.address }]
      returnType := .uint256
      body := Ledger.getBalanceAST }
  ]
}

def safeCounterSpec : ASTContractSpec := {
  name := "SafeCounter"
  functions := [
    { name := "increment"
      params := []
      returnType := .unit
      body := SafeCounter.incrementAST },
    { name := "decrement"
      params := []
      returnType := .unit
      body := SafeCounter.decrementAST },
    { name := "getCount"
      params := []
      returnType := .uint256
      body := SafeCounter.getCountAST }
  ]
}

def simpleTokenSpec : ASTContractSpec := {
  name := "SimpleToken"
  usesMapping := true
  constructor := some {
    params := [{ name := "initialOwner", ty := ParamType.address }]
    body := SimpleToken.constructorAST
  }
  functions := [
    { name := "mint"
      params := [
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := .unit
      body := SimpleToken.mintAST },
    { name := "transfer"
      params := [
        { name := "to", ty := ParamType.address },
        { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := .unit
      body := SimpleToken.transferAST },
    { name := "balanceOf"
      params := [{ name := "addr", ty := ParamType.address }]
      returnType := .uint256
      body := SimpleToken.balanceOfAST },
    { name := "totalSupply"
      params := []
      returnType := .uint256
      body := SimpleToken.getTotalSupplyAST },
    { name := "owner"
      params := []
      returnType := .address
      body := SimpleToken.getOwnerAST }
  ]
}

/-- All AST-based contract specs (excludes CryptoHash which uses external calls). -/
def allSpecs : List ASTContractSpec := [
  simpleStorageSpec,
  counterSpec,
  ownedSpec,
  ledgerSpec,
  ownedCounterSpec,
  simpleTokenSpec,
  safeCounterSpec
]

end Compiler.ASTSpecs
