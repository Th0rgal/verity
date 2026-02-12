/-
  Invariants for Safe Multisig base (Scaffold).

  TODO:
  - Owner set must be non-empty
  - Threshold must be > 0 and <= owner count
  - Module guards (if present) must be consistent
-/

import DumbContracts.Core

namespace DumbContracts.Specs.SafeMultisigBase

open DumbContracts

/-- Placeholder invariant: always true. Replace with real invariants. -/
def safeMultisigBaseInvariant (_s : ContractState) : Prop :=
  True

end DumbContracts.Specs.SafeMultisigBase
