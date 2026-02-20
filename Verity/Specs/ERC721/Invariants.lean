/-
  State invariants for the ERC721 foundation scaffold.
-/

import Verity.Specs.Common

namespace Verity.Specs.ERC721

open Verity

/-- Basic well-formedness constraints for contract context and owner slot. -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0
  owner_nonzero : s.storageAddr 0 ≠ 0

/-- Token supply equals the next token id in sequential-mint mode. -/
def sequential_supply (s : ContractState) : Prop :=
  s.storage 1 = s.storage 2

/-- Context fields are preserved by state transitions. -/
abbrev context_preserved := Specs.sameContext

/-- setApprovalForAll only updates operator-approval table. -/
def setApprovalForAll_is_balance_neutral (s s' : ContractState) : Prop :=
  s'.storage = s.storage ∧
  s'.storageAddr = s.storageAddr ∧
  s'.storageMap = s.storageMap ∧
  s'.storageMapUint = s.storageMapUint

end Verity.Specs.ERC721
