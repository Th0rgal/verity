/-
  State invariants for Owned contract.

  Defines properties that should always hold, regardless of operations.
-/

import Verity.Core
import Verity.Specs.Common

namespace Verity.Specs.Owned

open Verity

/-! ## State Invariants

Properties that should be maintained by all operations.
-/

/-- Well-formed contract state:
    - Sender address is non-empty
    - Contract address is non-empty
    - Owner address is non-empty (after construction)
-/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""
  owner_nonempty : s.storageAddr 0 ≠ ""

/-- Mapping storage unchanged: Owner operations don't touch mapping storage -/
abbrev map_storage_unchanged := Specs.sameStorageMap

/-- Contract context preserved: Operations don't change sender or contract address -/
abbrev context_preserved := Specs.sameContext

end Verity.Specs.Owned
