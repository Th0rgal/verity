/-
  Formal specifications for SafeCounter contract operations.

  SafeCounter uses checked arithmetic (safeAdd/safeSub) to prevent
  overflow/underflow. Operations revert when bounds are exceeded.

  Storage layout:
  - Slot 0 (Uint256): count
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

/-- increment (when no overflow): count increases by 1, everything else preserved -/
def increment_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = add (s.storage 0) 1 ∧
  storageUnchangedExcept 0 s s' ∧
  sameAddrMapContext s s'

/-- decrement (when no underflow): count decreases by 1, everything else preserved -/
def decrement_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = sub (s.storage 0) 1 ∧
  storageUnchangedExcept 0 s s' ∧
  sameAddrMapContext s s'

/-- getCount: returns current count, no state change -/
def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0

end DumbContracts.Specs.SafeCounter
