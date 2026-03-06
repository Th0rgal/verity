/-
  Basic proofs for ERC721 foundation scaffold.
-/

import Contracts.ERC721.Spec
import Contracts.ERC721.ERC721
import Verity.Proofs.Stdlib.Automation

namespace Contracts.ERC721.Proofs

open Verity
open Contracts.ERC721.Spec

/-- `constructor` sets owner slot 0 and zero-initializes supply/counter slots. -/
theorem constructor_meets_spec (s : ContractState) (initialOwner : Address) :
    constructor_spec initialOwner s ((Contracts.ERC721.«constructor» initialOwner).runState s) := by
  unfold constructor_spec Specs.storageAddrStorage2UpdateSpec Specs.sameStorageMapsContext
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Contracts.ERC721.«constructor», Contracts.ERC721.owner,
      Contracts.ERC721.totalSupply, Contracts.ERC721.nextTokenId,
      setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Contracts.ERC721.«constructor», Contracts.ERC721.owner,
      Contracts.ERC721.totalSupply, Contracts.ERC721.nextTokenId,
      setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Contracts.ERC721.«constructor», Contracts.ERC721.owner,
      Contracts.ERC721.totalSupply, Contracts.ERC721.nextTokenId,
      setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]
  · intro other h_neq
    simp [Contracts.ERC721.«constructor», Contracts.ERC721.owner,
      Contracts.ERC721.totalSupply, Contracts.ERC721.nextTokenId,
      setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind, h_neq]
  · intro other h_slot1 h_slot2
    simp [Contracts.ERC721.«constructor», Contracts.ERC721.owner,
      Contracts.ERC721.totalSupply, Contracts.ERC721.nextTokenId,
      setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind, h_slot1, h_slot2]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · simp [Specs.sameContext, Contracts.ERC721.«constructor», Contracts.ERC721.owner,
        Contracts.ERC721.totalSupply, Contracts.ERC721.nextTokenId,
        setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]

/-- `balanceOf` returns balances slot 3 at address `addr`. -/
theorem balanceOf_meets_spec (s : ContractState) (addr : Address) :
    balanceOf_spec addr ((Contracts.ERC721.balanceOf addr).runValue s) s := by
  simpa [balanceOf_spec, Contracts.ERC721.balanceOf] using
    (Verity.Proofs.Stdlib.Automation.getMapping_runValue
      Contracts.ERC721.balances addr s)

/-- `ownerOf` reverts for unminted tokens and returns owner for minted tokens. -/
theorem ownerOf_meets_spec (s : ContractState) (tokenId : Uint256) :
    ownerOf_spec tokenId ((Contracts.ERC721.ownerOf tokenId).run s) s := by
  cases h_owner : (s.storageMapUint 4 tokenId != 0) <;>
    simp [ownerOf_spec, Contracts.ERC721.ownerOf, Contract.run, Verity.bind, Bind.bind,
      getMappingUint, Contracts.ERC721.owners,
      Contracts.ERC721.Spec.wordToAddress, Pure.pure, Verity.pure,
      require, h_owner]

/-- `getApproved` reverts for unminted tokens and returns approval for minted tokens. -/
theorem getApproved_meets_spec (s : ContractState) (tokenId : Uint256) :
    getApproved_spec tokenId ((Contracts.ERC721.getApproved tokenId).run s) s := by
  cases h_owner : (s.storageMapUint 4 tokenId != 0) <;>
    simp [getApproved_spec, Contracts.ERC721.getApproved, Contract.run, Verity.bind, Bind.bind,
      getMappingUint, Contracts.ERC721.owners, Contracts.ERC721.tokenApprovals,
      Contracts.ERC721.Spec.wordToAddress, Pure.pure, Verity.pure,
      require, h_owner]

/-- `isApprovedForAll` checks nonzero operator-approval flag in slot 6. -/
theorem isApprovedForAll_meets_spec (s : ContractState) (ownerAddr operator : Address) :
    isApprovedForAll_spec ownerAddr operator ((Contracts.ERC721.isApprovedForAll ownerAddr operator).runValue s) s := by
  simp [isApprovedForAll_spec, Contracts.ERC721.isApprovedForAll, Contract.runValue, Verity.bind, Bind.bind,
    getMapping2, Contracts.ERC721.operatorApprovals]
  simp [Pure.pure, Verity.pure]

/-- `setApprovalForAll` writes sender/operator flag and leaves other state unchanged. -/
theorem setApprovalForAll_meets_spec (s : ContractState) (operator : Address) (approved : Bool) :
    setApprovalForAll_spec s.sender operator approved s ((Contracts.ERC721.setApprovalForAll operator approved).runState s) := by
  unfold setApprovalForAll_spec Specs.storageMap2UpdateSpec Specs.storageMap2UnchangedExceptKeyPair
    Specs.sameStorageAddrMapUintContext
  refine ⟨?_, ?_, ?_⟩
  · cases approved <;>
      simp [Contracts.ERC721.setApprovalForAll, Contracts.ERC721.operatorApprovals,
        setMapping2, Contracts.ERC721.Spec.boolToWord,
        msgSender, Contract.runState, Verity.bind, Bind.bind]
  · refine ⟨?_, ?_⟩
    · intro o' op' h_neq
      simp [Contracts.ERC721.setApprovalForAll, Contracts.ERC721.operatorApprovals,
        setMapping2,
        msgSender, Contract.runState, Verity.bind, Bind.bind, h_neq]
    · intro op' h_neq
      simp [Contracts.ERC721.setApprovalForAll, Contracts.ERC721.operatorApprovals,
        setMapping2,
        msgSender, Contract.runState, Verity.bind, Bind.bind, h_neq]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Specs.sameStorage, Contracts.ERC721.setApprovalForAll, Contracts.ERC721.operatorApprovals,
      setMapping2,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
    · simp [Specs.sameStorageAddr, Contracts.ERC721.setApprovalForAll, Contracts.ERC721.operatorApprovals,
      setMapping2,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
    · simp [Specs.sameStorageMap, Contracts.ERC721.setApprovalForAll, Contracts.ERC721.operatorApprovals,
      setMapping2,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
    · simp [Specs.sameStorageMapUint, Contracts.ERC721.setApprovalForAll,
      Contracts.ERC721.operatorApprovals, setMapping2,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
    · simp [Specs.sameContext, Contracts.ERC721.setApprovalForAll,
      Contracts.ERC721.operatorApprovals, setMapping2,
      msgSender, Contract.runState, Verity.bind, Bind.bind]

end Contracts.ERC721.Proofs
