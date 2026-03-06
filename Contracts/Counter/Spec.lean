/-
  Formal specifications for Counter operations.
-/

import Verity.Specs.Common
import Verity.EVM.Uint256
import Contracts.MacroContracts.Core

namespace Contracts.Counter.Spec

open Verity
open Verity.Specs
open Contracts.MacroContracts.Counter
open Verity.EVM.Uint256

/-! ## Operation Specifications -/

/-- Increment: increases count by 1 -/
def increment_spec (s s' : ContractState) : Prop :=
  storageUpdateSpec 0 (fun st => add (st.storage 0) 1) sameAddrMapContext s s'

/-- Decrement: decreases count by 1 -/
def decrement_spec (s s' : ContractState) : Prop :=
  storageUpdateSpec 0 (fun st => sub (st.storage 0) 1) sameAddrMapContext s s'

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

end Contracts.Counter.Spec
