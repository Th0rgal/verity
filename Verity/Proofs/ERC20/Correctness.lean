/-
  Correctness helpers for ERC20 foundation scaffold.
-/

import Verity.Proofs.ERC20.Basic
import Verity.Specs.ERC20.Invariants

namespace Verity.Proofs.ERC20

open Verity
open Verity.Specs.ERC20

/-- Read-only `balanceOf` preserves state. -/
theorem balanceOf_preserves_state (s : ContractState) (addr : Address) :
    ((Verity.Examples.ERC20.balanceOf addr).runState s) = s := by
  simp [Verity.Examples.ERC20.balanceOf, getMapping, Contract.runState]

/-- Read-only `allowanceOf` preserves state. -/
theorem allowanceOf_preserves_state (s : ContractState) (ownerAddr spender : Address) :
    ((Verity.Examples.ERC20.allowanceOf ownerAddr spender).runState s) = s := by
  simp [Verity.Examples.ERC20.allowanceOf, getMapping2, Contract.runState]

end Verity.Proofs.ERC20
