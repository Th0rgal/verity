/-
  Invariants for Safe Multisig base (Scaffold).

  TODO:
  - Owner set must be non-empty
  - Threshold must be > 0 and <= owner count
  - Module guards (if present) must be consistent
-/

import DumbContracts.Core
import DumbContracts.Examples.SafeMultisigBase

namespace DumbContracts.Specs.SafeMultisigBase

open DumbContracts
open DumbContracts.Examples.SafeMultisigBase

/-- Helper: read owner count from storage. -/
def ownerCountVal (s : ContractState) : Uint256 :=
  s.storage ownerCount.slot

/-- Helper: read threshold from storage. -/
def thresholdVal (s : ContractState) : Uint256 :=
  s.storage threshold.slot

/--
  Baseline Safe invariants:
  - Owner count is positive
  - Threshold is positive
  - Threshold does not exceed owner count

  This intentionally omits the full linked-list owners invariant for now,
  but provides a minimal correctness envelope for `setup` and ownership ops.
-/
def safeMultisigBaseInvariant (s : ContractState) : Prop :=
  (0 : Uint256) < ownerCountVal s ∧
  (0 : Uint256) < thresholdVal s ∧
  thresholdVal s ≤ ownerCountVal s

end DumbContracts.Specs.SafeMultisigBase
