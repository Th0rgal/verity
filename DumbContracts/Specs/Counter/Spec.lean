/-
  Formal specifications for Counter contract operations.

  Defines what each operation SHOULD do, independent of implementation.
-/

import DumbContracts.Core
import DumbContracts.Examples.Counter

namespace DumbContracts.Specs.Counter

open DumbContracts
open DumbContracts.Examples.Counter

/-! ## Operation Specifications

These define the expected behavior of each Counter operation.
-/

/-- Specification for increment operation:
    - Increases the count by exactly 1
    - Preserves all other storage
    - Preserves contract context (sender, address)
-/
def increment_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = s.storage 0 + 1 ∧
  (∀ slot : Nat, slot ≠ 0 → s'.storage slot = s.storage slot) ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.storageAddr = s.storageAddr ∧
  s'.storageMap = s.storageMap

/-- Specification for decrement operation:
    - Decreases the count by exactly 1
    - Preserves all other storage
    - Preserves contract context
-/
def decrement_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = s.storage 0 - 1 ∧
  (∀ slot : Nat, slot ≠ 0 → s'.storage slot = s.storage slot) ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.storageAddr = s.storageAddr ∧
  s'.storageMap = s.storageMap

/-- Specification for getCount operation:
    - Returns the current count (value at slot 0)
    - Does not modify state
-/
def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0

/-! ## Combined Specifications

Properties about sequences of operations.
-/

/-- Increment followed by getCount returns the incremented value -/
def increment_getCount_spec (s : ContractState) (result : Uint256) : Prop :=
  result = s.storage 0 + 1

/-- Decrement followed by getCount returns the decremented value -/
def decrement_getCount_spec (s : ContractState) (result : Uint256) : Prop :=
  result = s.storage 0 - 1

/-- Increment then decrement returns to original value -/
def increment_decrement_cancel (s s' : ContractState) : Prop :=
  s'.storage 0 = s.storage 0

/-- Two increments add 2 to the count -/
def two_increments_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = s.storage 0 + 2

end DumbContracts.Specs.Counter
