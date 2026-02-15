/-
  Formal specifications for Counter operations.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common
import DumbContracts.EVM.Uint256
import DumbContracts.Examples.Counter

namespace DumbContracts.Specs.Counter

open DumbContracts
open DumbContracts.Examples.Counter
open DumbContracts.EVM.Uint256

/-! ## Operation Specifications -/

/-- Increment: increases count by 1 -/
def increment_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = add (s.storage 0) 1 ∧
  storageUnchangedExcept 0 s s' ∧
  sameAddrMapContext s s'

/-- Decrement: decreases count by 1 -/
def decrement_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = sub (s.storage 0) 1 ∧
  storageUnchangedExcept 0 s s' ∧
  sameAddrMapContext s s'

/-- getCount: returns the current count -/
def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0

/-! ## Combined Specifications -/

/-- Increment followed by getCount returns the incremented value -/
def increment_getCount_spec (s : ContractState) (result : Uint256) : Prop :=
  result = add (s.storage 0) 1

/-- Decrement followed by getCount returns the decremented value -/
def decrement_getCount_spec (s : ContractState) (result : Uint256) : Prop :=
  result = sub (s.storage 0) 1

/-- Increment then decrement returns to original value -/
def increment_decrement_cancel (s s' : ContractState) : Prop :=
  s'.storage 0 = s.storage 0

/-- Two increments add 2 to the count -/
def two_increments_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = add (add (s.storage 0) 1) 1

end DumbContracts.Specs.Counter
