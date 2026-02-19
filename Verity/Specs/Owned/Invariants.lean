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

end Verity.Specs.Owned
