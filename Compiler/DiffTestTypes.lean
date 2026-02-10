/-
  Compiler.DiffTestTypes: Shared Types for Differential Testing

  Common types used by both RandomGen and Interpreter modules.
  Extracted to avoid duplication and resolve conflicting main function issue.
-/

import DumbContracts.Core

namespace Compiler.DiffTestTypes

open DumbContracts

/-!
## Transaction Model

Represents a transaction that can be executed on both EDSL and compiled EVM.
-/

structure Transaction where
  sender : Address
  functionName : String
  args : List Nat  -- Simplified: all args as uint256 for now

/-!
## Contract Type

Enumeration of all contracts available for differential testing.
-/

inductive ContractType
  | simpleStorage
  | counter
  | owned
  | ledger
  | ownedCounter
  | simpleToken
  | safeCounter
  deriving Repr, DecidableEq

end Compiler.DiffTestTypes
