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

/-- Read-only `getTotalSupply` preserves state. -/
theorem getTotalSupply_preserves_state (s : ContractState) :
    ((Verity.Examples.ERC20.getTotalSupply).runState s) = s := by
  simp [Verity.Examples.ERC20.getTotalSupply, getStorage, Contract.runState]

/-- Read-only `getOwner` preserves state. -/
theorem getOwner_preserves_state (s : ContractState) :
    ((Verity.Examples.ERC20.getOwner).runState s) = s := by
  simp [Verity.Examples.ERC20.getOwner, getStorageAddr, Contract.runState]

/-- `approve` satisfies the balance-neutral invariant helper. -/
theorem approve_is_balance_neutral_holds (s : ContractState) (spender : Address) (amount : Uint256) :
    approve_is_balance_neutral s ((Verity.Examples.ERC20.approve spender amount).runState s) := by
  have h := approve_meets_spec s spender amount
  rcases h with ⟨_, _, _, h_storage, _, h_storageMap, _⟩
  exact ⟨h_storage, h_storageMap⟩

/-- `transfer` preserves total supply under successful-path preconditions. -/
theorem transfer_preserves_totalSupply_when_sufficient
    (s : ContractState) (to : Address) (amount : Uint256)
    (h_balance : s.storageMap 2 s.sender ≥ amount)
    (h_no_overflow : s.sender ≠ to →
      (s.storageMap 2 to : Nat) + (amount : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256) :
    ((Verity.Examples.ERC20.transfer to amount).runState s).storage 1 = s.storage 1 := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance h_no_overflow
  exact h.2.2.2.2.1

/-- `transfer` preserves owner storage under successful-path preconditions. -/
theorem transfer_preserves_owner_when_sufficient
    (s : ContractState) (to : Address) (amount : Uint256)
    (h_balance : s.storageMap 2 s.sender ≥ amount)
    (h_no_overflow : s.sender ≠ to →
      (s.storageMap 2 to : Nat) + (amount : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256) :
    ((Verity.Examples.ERC20.transfer to amount).runState s).storageAddr 0 = s.storageAddr 0 := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance h_no_overflow
  exact h.2.2.2.2.2.1

end Verity.Proofs.ERC20
