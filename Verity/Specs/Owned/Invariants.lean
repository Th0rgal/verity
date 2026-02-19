/-
  State invariants for Owned contract.

  Defines properties that should always hold, regardless of operations.
-/

import Verity.Specs.Common

namespace Verity.Specs.Owned

open Verity

/-! ## State Invariants

Properties that should be maintained by all operations.
-/

/-- Well-formed contract state:
    - Sender address is nonzero
    - Contract address is nonzero
    - Owner address is nonzero (after construction)
-/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0
  owner_nonzero : s.storageAddr 0 ≠ 0

end Verity.Specs.Owned
