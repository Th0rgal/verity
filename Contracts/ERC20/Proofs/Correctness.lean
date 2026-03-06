/-
  Correctness helpers for ERC20 foundation scaffold.
-/

import Contracts.ERC20.Proofs.Basic
import Contracts.ERC20.Invariants

namespace Contracts.ERC20.Proofs

open Verity
open Contracts.ERC20.Spec
open Contracts.ERC20.Invariants

/-- Read-only `balanceOf` preserves state. -/
theorem balanceOf_preserves_state (s : ContractState) (addr : Address) :
    ((Contracts.MacroContracts.ERC20.balanceOf addr).runState s) = s := by
  simp [Contracts.MacroContracts.ERC20.balanceOf, getMapping, Contract.runState, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure]

/-- Read-only `allowanceOf` preserves state. -/
theorem allowanceOf_preserves_state (s : ContractState) (ownerAddr spender : Address) :
    ((Contracts.MacroContracts.ERC20.allowanceOf ownerAddr spender).runState s) = s := by
  simp [Contracts.MacroContracts.ERC20.allowanceOf, getMapping2, Contract.runState, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure]

/-- Read-only `getTotalSupply` preserves state. -/
theorem getTotalSupply_preserves_state (s : ContractState) :
    ((Contracts.MacroContracts.ERC20.getTotalSupply).runState s) = s := by
  simp [Contracts.MacroContracts.ERC20.getTotalSupply, Contracts.MacroContracts.ERC20.totalSupply,
    getStorage, Contract.runState, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

/-- Read-only `getOwner` preserves state. -/
theorem getOwner_preserves_state (s : ContractState) :
    ((Contracts.MacroContracts.ERC20.getOwner).runState s) = s := by
  simp [Contracts.MacroContracts.ERC20.getOwner, Contracts.MacroContracts.ERC20.owner,
    getStorageAddr, Contract.runState, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

/-- `approve` satisfies the balance-neutral invariant helper. -/
theorem approve_is_balance_neutral_holds (s : ContractState) (spender : Address) (amount : Uint256) :
    approve_is_balance_neutral s ((Contracts.MacroContracts.ERC20.approve spender amount).runState s) := by
  have h := approve_meets_spec s spender amount
  rcases h with ⟨_, _, h_frame⟩
  rcases h_frame with ⟨h_storage, _, h_storageMap, _⟩
  exact ⟨h_storage, h_storageMap⟩

/-- `transfer` preserves total supply under successful-path preconditions. -/
theorem transfer_preserves_totalSupply_when_sufficient
    (s : ContractState) (to : Address) (amount : Uint256)
    (h_balance : s.storageMap 2 s.sender ≥ amount)
    (h_no_overflow : s.sender ≠ to →
      (s.storageMap 2 to : Nat) + (amount : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256) :
    ((Contracts.MacroContracts.ERC20.transfer to amount).runState s).storage 1 = s.storage 1 := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance h_no_overflow
  exact h.2.2.2.2.1

/-- `transfer` preserves owner storage under successful-path preconditions. -/
theorem transfer_preserves_owner_when_sufficient
    (s : ContractState) (to : Address) (amount : Uint256)
    (h_balance : s.storageMap 2 s.sender ≥ amount)
    (h_no_overflow : s.sender ≠ to →
      (s.storageMap 2 to : Nat) + (amount : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256) :
    ((Contracts.MacroContracts.ERC20.transfer to amount).runState s).storageAddr 0 = s.storageAddr 0 := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance h_no_overflow
  exact h.2.2.2.2.2.1

end Contracts.ERC20.Proofs
