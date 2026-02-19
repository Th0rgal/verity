/-
  State invariants for Counter contract.

  Defines properties that should always hold, regardless of operations.
-/

import Verity.Core
import Verity.Specs.Common

namespace Verity.Specs.Counter

open Verity

/-! ## State Invariants

Properties that should be maintained by all operations.
-/

/-- Well-formed contract state:
    - Sender address is non-empty
    - Contract address is non-empty
-/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""

/-- Storage isolation: Operations on slot 0 (count) don't affect other slots -/
def storage_isolated (s s' : ContractState) (slot : Nat) : Prop :=
  slot ≠ 0 → s'.storage slot = s.storage slot

/-- Address storage unchanged: Uint256 operations don't touch Address storage -/
abbrev addr_storage_unchanged := Specs.sameStorageAddr

/-- Mapping storage unchanged: Counter operations don't touch mapping storage -/
abbrev map_storage_unchanged := Specs.sameStorageMap

/-- Contract context preserved: Operations don't change sender or contract address -/
abbrev context_preserved := Specs.sameContext

/-- Complete state preservation except for count:
    Everything except slot 0 remains unchanged
-/
def state_preserved_except_count (s s' : ContractState) : Prop :=
  storage_isolated s s' 0 ∧
  addr_storage_unchanged s s' ∧
  map_storage_unchanged s s' ∧
  context_preserved s s'

end Verity.Specs.Counter
