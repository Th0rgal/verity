/-
  Correctness helpers for ERC721 foundation scaffold.
-/

import Verity.Proofs.ERC721.Basic
import Verity.Specs.ERC721.Invariants

namespace Verity.Proofs.ERC721

open Verity
open Verity.Specs.ERC721

/-- Read-only `balanceOf` preserves state. -/
theorem balanceOf_preserves_state (s : ContractState) (addr : Address) :
    ((Verity.Examples.MacroContracts.ERC721Addressed.balanceOf addr).runState s) = s := by
  simp [Verity.Examples.MacroContracts.ERC721Addressed.balanceOf, getMapping, Contract.runState]

/-- Read-only `ownerOf` preserves state. -/
theorem ownerOf_preserves_state (s : ContractState) (tokenId : Uint256) :
    ((Verity.Examples.MacroContracts.ERC721Addressed.ownerOf tokenId).runState s) = s := by
  cases h_owner : (s.storageMapUint Verity.Examples.MacroContracts.ERC721Addressed.owners.slot tokenId != 0) <;>
    simp [Verity.Examples.MacroContracts.ERC721Addressed.ownerOf, getMappingUint, Contract.runState, Verity.bind, Bind.bind,
      require, Pure.pure, Verity.pure, h_owner]

/-- Read-only `getApproved` preserves state. -/
theorem getApproved_preserves_state (s : ContractState) (tokenId : Uint256) :
    ((Verity.Examples.MacroContracts.ERC721Addressed.getApproved tokenId).runState s) = s := by
  cases h_owner : (s.storageMapUint Verity.Examples.MacroContracts.ERC721Addressed.owners.slot tokenId != 0) <;>
    simp [Verity.Examples.MacroContracts.ERC721Addressed.getApproved, getMappingUint, Contract.runState, Verity.bind, Bind.bind,
      require, Pure.pure, Verity.pure, h_owner]

/-- Read-only `isApprovedForAll` preserves state. -/
theorem isApprovedForAll_preserves_state (s : ContractState) (ownerAddr operator : Address) :
    ((Verity.Examples.MacroContracts.ERC721Addressed.isApprovedForAll ownerAddr operator).runState s) = s := by
  simp [Verity.Examples.MacroContracts.ERC721Addressed.isApprovedForAll, getMapping2, Contract.runState, Verity.bind, Bind.bind]
  simp [Pure.pure, Verity.pure]

/-- `setApprovalForAll` satisfies the balance-neutral invariant helper. -/
theorem setApprovalForAll_is_balance_neutral_holds
    (s : ContractState) (operator : Address) (approved : Bool) :
    setApprovalForAll_is_balance_neutral s ((Verity.Examples.MacroContracts.ERC721Addressed.setApprovalForAll operator approved).runState s) := by
  have h := setApprovalForAll_meets_spec s operator approved
  rcases h with ⟨_, _, _, h_storage, h_storageAddr, h_storageMap, h_storageMapUint, _⟩
  exact ⟨h_storage, h_storageAddr, h_storageMap, h_storageMapUint⟩

end Verity.Proofs.ERC721
