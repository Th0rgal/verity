/-
  Formal specifications for SafeCounter operations.
-/

import Verity.Specs.Common
import Verity.Stdlib.Math
import Verity.EVM.Uint256
import Contracts.MacroContracts.Core

namespace Verity.Specs.SafeCounter

open Verity
open Verity.Stdlib.Math
open Verity.EVM.Uint256
open Verity.Examples.MacroContracts.SafeCounter

/-! ## Operation Specifications -/

/-- increment: increases count by 1 (with overflow check) -/
def increment_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = add (s.storage 0) 1 ∧
  storageUnchangedExcept 0 s s' ∧
  sameAddrMapContext s s'

/-- decrement: decreases count by 1 (with underflow check) -/
def decrement_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = sub (s.storage 0) 1 ∧
  storageUnchangedExcept 0 s s' ∧
  sameAddrMapContext s s'

/-- getCount: returns current count -/
def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0

end Verity.Specs.SafeCounter
