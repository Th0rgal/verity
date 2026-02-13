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

/-
  Linked-list owners invariant (Safe OwnerManager):
  The owners mapping encodes a singly-linked list with a sentinel head.
  This is a stronger invariant than the baseline checks above.

  NOTE: In Solidity, `owners` maps address -> address. The EDSL models
  this as `Address -> Uint256`, so we treat the stored value as an encoded
  address. The encoding function is left opaque for now and will be tied
  to ABI encoding rules when address modeling lands in the EDSL.
-/

def ownerNextVal (s : ContractState) (owner : Address) : Uint256 :=
  s.storageMap owners.slot owner

def ownerAddressValid (s : ContractState) (owner : Address) : Prop :=
  owner ≠ zeroAddress ∧ owner ≠ ownersSentinel ∧ owner ≠ s.thisAddress

def ownersLinkedList (s : ContractState) (ownersList : List Address) : Prop :=
  let rec go (prev : Address) (rest : List Address) : Prop :=
    match rest with
    | [] => ownerNextVal s prev = encodeAddress ownersSentinel
    | next :: tail =>
        ownerNextVal s prev = encodeAddress next ∧
        go next tail
  match ownersList with
  | [] => ownerNextVal s ownersSentinel = encodeAddress ownersSentinel
  | _ => go ownersSentinel ownersList

def safeMultisigOwnersLinkedListInvariant (s : ContractState) (ownersList : List Address) : Prop :=
  ownersList ≠ [] ∧
  ownersList.Nodup ∧
  (∀ owner ∈ ownersList, ownerAddressValid s owner) ∧
  ownerCountVal s = (ownersList.length : Nat) ∧
  ownersLinkedList s ownersList

end DumbContracts.Specs.SafeMultisigBase
