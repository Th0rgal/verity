/-
  Basic proofs for ERC721 foundation scaffold.
-/

import Contracts.ERC721.Spec
import Contracts.MacroContracts.ERC721Addressed

namespace Contracts.ERC721.Proofs

open Verity
open Contracts.ERC721.Spec

/-- `constructor` sets owner slot 0 and zero-initializes supply/counter slots. -/
theorem constructor_meets_spec (s : ContractState) (initialOwner : Address) :
    constructor_spec initialOwner s ((Contracts.MacroContracts.ERC721Addressed.constructor initialOwner).runState s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Contracts.MacroContracts.ERC721Addressed.constructor, Contracts.MacroContracts.ERC721Addressed.owner, setStorageAddr,
      setStorage, Contract.runState, Verity.bind, Bind.bind]
  · simp [Contracts.MacroContracts.ERC721Addressed.constructor, Contracts.MacroContracts.ERC721Addressed.totalSupply, setStorageAddr,
      setStorage, Contract.runState, Verity.bind, Bind.bind]
  · simp [Contracts.MacroContracts.ERC721Addressed.constructor, Contracts.MacroContracts.ERC721Addressed.nextTokenId, setStorageAddr,
      setStorage, Contract.runState, Verity.bind, Bind.bind]
  · intro slot h_neq
    simp [Contracts.MacroContracts.ERC721Addressed.constructor, Contracts.MacroContracts.ERC721Addressed.owner,
      Contracts.MacroContracts.ERC721Addressed.totalSupply, Contracts.MacroContracts.ERC721Addressed.nextTokenId, setStorageAddr,
      setStorage,
      Contract.runState, Verity.bind, Bind.bind, h_neq]
  · intro slot h_slot1 h_slot2
    simp [Contracts.MacroContracts.ERC721Addressed.constructor, Contracts.MacroContracts.ERC721Addressed.owner,
      Contracts.MacroContracts.ERC721Addressed.totalSupply, Contracts.MacroContracts.ERC721Addressed.nextTokenId, setStorageAddr,
      setStorage,
      Contract.runState, Verity.bind, Bind.bind, h_slot1, h_slot2]
  · simp [Specs.sameStorageMap, Contracts.MacroContracts.ERC721Addressed.constructor, Contracts.MacroContracts.ERC721Addressed.owner,
      Contracts.MacroContracts.ERC721Addressed.totalSupply, Contracts.MacroContracts.ERC721Addressed.nextTokenId,
      setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]
  · rfl
  · rfl
  · simp [Specs.sameContext, Contracts.MacroContracts.ERC721Addressed.constructor, Contracts.MacroContracts.ERC721Addressed.owner,
      Contracts.MacroContracts.ERC721Addressed.totalSupply, Contracts.MacroContracts.ERC721Addressed.nextTokenId,
      setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]

/-- `balanceOf` returns balances slot 3 at address `addr`. -/
theorem balanceOf_meets_spec (s : ContractState) (addr : Address) :
    balanceOf_spec addr ((Contracts.MacroContracts.ERC721Addressed.balanceOf addr).runValue s) s := by
  simp [Contracts.MacroContracts.ERC721Addressed.balanceOf, balanceOf_spec, getMapping, Contract.runValue,
    Contracts.MacroContracts.ERC721Addressed.balances]

/-- `ownerOf` reverts for unminted tokens and returns owner for minted tokens. -/
theorem ownerOf_meets_spec (s : ContractState) (tokenId : Uint256) :
    ownerOf_spec tokenId ((Contracts.MacroContracts.ERC721Addressed.ownerOf tokenId).run s) s := by
  cases h_owner : (s.storageMapUint 4 tokenId != 0) <;>
    simp [ownerOf_spec, Contracts.MacroContracts.ERC721Addressed.ownerOf, Contract.run, Verity.bind, Bind.bind,
      getMappingUint, Contracts.MacroContracts.ERC721Addressed.owners, Contracts.MacroContracts.ERC721Addressed.wordToAddress,
      Contracts.ERC721.Spec.wordToAddress, Pure.pure, Verity.pure,
      require, h_owner]

/-- `getApproved` reverts for unminted tokens and returns approval for minted tokens. -/
theorem getApproved_meets_spec (s : ContractState) (tokenId : Uint256) :
    getApproved_spec tokenId ((Contracts.MacroContracts.ERC721Addressed.getApproved tokenId).run s) s := by
  cases h_owner : (s.storageMapUint 4 tokenId != 0) <;>
    simp [getApproved_spec, Contracts.MacroContracts.ERC721Addressed.getApproved, Contract.run, Verity.bind, Bind.bind,
      getMappingUint, Contracts.MacroContracts.ERC721Addressed.owners, Contracts.MacroContracts.ERC721Addressed.tokenApprovals,
      Contracts.MacroContracts.ERC721Addressed.wordToAddress, Contracts.ERC721.Spec.wordToAddress, Pure.pure, Verity.pure,
      require, h_owner]

/-- `isApprovedForAll` checks nonzero operator-approval flag in slot 6. -/
theorem isApprovedForAll_meets_spec (s : ContractState) (ownerAddr operator : Address) :
    isApprovedForAll_spec ownerAddr operator ((Contracts.MacroContracts.ERC721Addressed.isApprovedForAll ownerAddr operator).runValue s) s := by
  simp [isApprovedForAll_spec, Contracts.MacroContracts.ERC721Addressed.isApprovedForAll, Contract.runValue, Verity.bind, Bind.bind,
    getMapping2, Contracts.MacroContracts.ERC721Addressed.operatorApprovals]
  simp [Pure.pure, Verity.pure]

/-- `setApprovalForAll` writes sender/operator flag and leaves other state unchanged. -/
theorem setApprovalForAll_meets_spec (s : ContractState) (operator : Address) (approved : Bool) :
    setApprovalForAll_spec s.sender operator approved s ((Contracts.MacroContracts.ERC721Addressed.setApprovalForAll operator approved).runState s) := by
  refine ⟨?_, ?_, ?_⟩
  · cases approved <;>
      simp [Contracts.MacroContracts.ERC721Addressed.setApprovalForAll, Contracts.MacroContracts.ERC721Addressed.operatorApprovals,
        setMapping2, Contracts.MacroContracts.ERC721Addressed.boolToWord, Contracts.ERC721.Spec.boolToWord,
        msgSender, Contract.runState, Verity.bind, Bind.bind]
  · refine ⟨?_, ?_⟩
    · intro o' op' h_neq
      simp [Contracts.MacroContracts.ERC721Addressed.setApprovalForAll, Contracts.MacroContracts.ERC721Addressed.operatorApprovals,
        setMapping2, Contracts.MacroContracts.ERC721Addressed.boolToWord,
        msgSender, Contract.runState, Verity.bind, Bind.bind, h_neq]
    · intro op' h_neq
      simp [Contracts.MacroContracts.ERC721Addressed.setApprovalForAll, Contracts.MacroContracts.ERC721Addressed.operatorApprovals,
        setMapping2, Contracts.MacroContracts.ERC721Addressed.boolToWord,
        msgSender, Contract.runState, Verity.bind, Bind.bind, h_neq]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Specs.sameStorage, Contracts.MacroContracts.ERC721Addressed.setApprovalForAll, Contracts.MacroContracts.ERC721Addressed.operatorApprovals,
      setMapping2, Contracts.MacroContracts.ERC721Addressed.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
    · simp [Specs.sameStorageAddr, Contracts.MacroContracts.ERC721Addressed.setApprovalForAll, Contracts.MacroContracts.ERC721Addressed.operatorApprovals,
      setMapping2, Contracts.MacroContracts.ERC721Addressed.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
    · simp [Specs.sameStorageMap, Contracts.MacroContracts.ERC721Addressed.setApprovalForAll, Contracts.MacroContracts.ERC721Addressed.operatorApprovals,
      setMapping2, Contracts.MacroContracts.ERC721Addressed.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
    · simp [Specs.sameStorageMapUint, Contracts.MacroContracts.ERC721Addressed.setApprovalForAll,
      Contracts.MacroContracts.ERC721Addressed.operatorApprovals, setMapping2,
      Contracts.MacroContracts.ERC721Addressed.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
    · simp [Specs.sameContext, Contracts.MacroContracts.ERC721Addressed.setApprovalForAll,
      Contracts.MacroContracts.ERC721Addressed.operatorApprovals, setMapping2,
      Contracts.MacroContracts.ERC721Addressed.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind]

end Contracts.ERC721.Proofs
