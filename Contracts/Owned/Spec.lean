/-
  Formal specifications for Owned contract operations.

  Defines what each access control operation SHOULD do, independent of implementation.
-/

import DumbContracts.Core
import Contracts.Owned.Impl

namespace Contracts.Owned.Spec

open DumbContracts
open Contracts.Owned

/-! ## Operation Specifications

These define the expected behavior of each Owned operation.
-/

/-- Specification for constructor operation:
    - Sets the owner to the provided address
    - Preserves all other storage
    - Preserves contract context
-/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = initialOwner ∧
  (∀ slot : Nat, slot ≠ 0 → s'.storageAddr slot = s.storageAddr slot) ∧
  s'.storage = s.storage ∧
  s'.storageMap = s.storageMap ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.blockTimestamp = s.blockTimestamp

/-- Specification for getOwner operation:
    - Returns the current owner address
    - Does not modify state
-/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

/-- Specification for transferOwnership operation:
    - Updates owner to the new address
    - Preserves all other storage
    - Preserves contract context
    - Note: Requires caller is current owner (enforced by onlyOwner)
-/
def transferOwnership_spec (newOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = newOwner ∧
  (∀ slot : Nat, slot ≠ 0 → s'.storageAddr slot = s.storageAddr slot) ∧
  s'.storage = s.storage ∧
  s'.storageMap = s.storageMap ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.blockTimestamp = s.blockTimestamp

/-- Specification for isOwner check:
    - Returns true if sender equals current owner
    - Returns false otherwise
    - Does not modify state
-/
def isOwner_spec (result : Bool) (s : ContractState) : Prop :=
  result = (s.sender == s.storageAddr 0)

/-! ## Combined Specifications

Properties about sequences of operations.
-/

/-- Constructor followed by getOwner returns the initial owner -/
def constructor_getOwner_spec (initialOwner : Address) (_s : ContractState) (result : Address) : Prop :=
  result = initialOwner

/-- TransferOwnership followed by getOwner returns the new owner -/
def transfer_getOwner_spec (newOwner : Address) (_s : ContractState) (result : Address) : Prop :=
  result = newOwner

end Contracts.Owned.Spec
