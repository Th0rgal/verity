/-
  Formal specifications for SafeCounter operations.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common
import DumbContracts.Stdlib.Math
import DumbContracts.EVM.Uint256
import DumbContracts.Examples.SafeCounter

namespace DumbContracts.Specs.SafeCounter

open DumbContracts
open DumbContracts.Stdlib.Math
open DumbContracts.EVM.Uint256

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

end DumbContracts.Specs.SafeCounter
