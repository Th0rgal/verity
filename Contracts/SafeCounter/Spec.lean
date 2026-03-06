/-
  Formal specifications for SafeCounter operations.
-/

import Verity.Specs.Common
import Verity.Macro
import Verity.Stdlib.Math
import Verity.EVM.Uint256
import Contracts.MacroContracts.Core

namespace Contracts.SafeCounter.Spec

open Verity
open Verity.Specs
open Verity.Stdlib.Math
open Verity.EVM.Uint256
open Contracts.MacroContracts.SafeCounter

/-! ## Operation Specifications -/

-- increment: increases count by 1 (with overflow check)
#gen_spec increment_spec (0, (fun st => add (st.storage 0) 1), sameAddrMapContext)

-- decrement: decreases count by 1 (with underflow check)
#gen_spec decrement_spec (0, (fun st => sub (st.storage 0) 1), sameAddrMapContext)

/-- getCount: returns current count -/
def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0

end Contracts.SafeCounter.Spec
