/-
  Correctness helpers for ERC721 foundation scaffold.
-/

import Contracts.ERC721.Proofs.Basic
import Contracts.ERC721.Invariants

namespace Contracts.ERC721.Proofs

open Verity
open Contracts.ERC721.Spec
open Contracts.ERC721.Invariants

/-- Read-only `balanceOf` preserves state. -/
theorem balanceOf_preserves_state (s : ContractState) (addr : Address) :
    ((Contracts.ERC721.balanceOf addr).runState s) = s := by
  rw [Contracts.ERC721.balanceOf]
  change ((Verity.bind (getMapping Contracts.ERC721.balances addr) Verity.pure).runState s) = s
  rw [Verity.Proofs.Stdlib.Automation.bind_pure_right]
  exact Verity.Proofs.Stdlib.Automation.getMapping_runState
    Contracts.ERC721.balances addr s

/-- Read-only `ownerOf` preserves state. -/
theorem ownerOf_preserves_state (s : ContractState) (tokenId : Uint256) :
    ((Contracts.ERC721.ownerOf tokenId).runState s) = s := by
  cases h_owner : (s.storageMapUint Contracts.ERC721.owners.slot tokenId != 0) <;>
    simp [Contracts.ERC721.ownerOf, getMappingUint, Contract.runState, Verity.bind, Bind.bind,
      require, Pure.pure, Verity.pure, h_owner]

/-- Read-only `getApproved` preserves state. -/
theorem getApproved_preserves_state (s : ContractState) (tokenId : Uint256) :
    ((Contracts.ERC721.getApproved tokenId).runState s) = s := by
  cases h_owner : (s.storageMapUint Contracts.ERC721.owners.slot tokenId != 0) <;>
    simp [Contracts.ERC721.getApproved, getMappingUint, getMappingUintAddr,
      Contract.runState, Verity.bind, Bind.bind, require, Pure.pure, Verity.pure, h_owner]

/-- Read-only `isApprovedForAll` preserves state. -/
theorem isApprovedForAll_preserves_state (s : ContractState) (ownerAddr operator : Address) :
    ((Contracts.ERC721.isApprovedForAll ownerAddr operator).runState s) = s := by
  simp [Contracts.ERC721.isApprovedForAll, getMapping2, Contract.runState, Verity.bind, Bind.bind]
  simp [Pure.pure, Verity.pure]

/-- `setApprovalForAll` satisfies the balance-neutral invariant helper. -/
theorem setApprovalForAll_is_balance_neutral_holds
    (s : ContractState) (operator : Address) (approved : Bool) :
    setApprovalForAll_is_balance_neutral s ((Contracts.ERC721.setApprovalForAll operator approved).runState s) := by
  have h := setApprovalForAll_meets_spec s operator approved
  rcases h with ⟨_, _, h_frame⟩
  rcases h_frame with ⟨h_storage, h_storageAddr, h_storageMap, h_storageMapUint, _⟩
  exact ⟨h_storage, h_storageAddr, h_storageMap, h_storageMapUint⟩

end Contracts.ERC721.Proofs
