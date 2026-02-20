/-
  Basic proofs for ERC721 foundation scaffold.
-/

import Verity.Specs.ERC721.Spec
import Verity.Examples.ERC721

namespace Verity.Proofs.ERC721

open Verity
open Verity.Specs.ERC721

/-- `constructor` sets owner slot 0 and zero-initializes supply/counter slots. -/
theorem constructor_meets_spec (s : ContractState) (initialOwner : Address) :
    constructor_spec initialOwner s ((Verity.Examples.ERC721.constructor initialOwner).runState s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Verity.Examples.ERC721.constructor, Verity.Examples.ERC721.owner, setStorageAddr,
      setStorage, Contract.runState, Verity.bind, Bind.bind]
  · simp [Verity.Examples.ERC721.constructor, Verity.Examples.ERC721.totalSupply, setStorageAddr,
      setStorage, Contract.runState, Verity.bind, Bind.bind]
  · simp [Verity.Examples.ERC721.constructor, Verity.Examples.ERC721.nextTokenId, setStorageAddr,
      setStorage, Contract.runState, Verity.bind, Bind.bind]
  · intro slot h_neq
    simp [Verity.Examples.ERC721.constructor, Verity.Examples.ERC721.owner,
      Verity.Examples.ERC721.totalSupply, Verity.Examples.ERC721.nextTokenId, setStorageAddr,
      setStorage,
      Contract.runState, Verity.bind, Bind.bind, h_neq]
  · intro slot h_slot1 h_slot2
    simp [Verity.Examples.ERC721.constructor, Verity.Examples.ERC721.owner,
      Verity.Examples.ERC721.totalSupply, Verity.Examples.ERC721.nextTokenId, setStorageAddr,
      setStorage,
      Contract.runState, Verity.bind, Bind.bind, h_slot1, h_slot2]
  · simp [Specs.sameStorageMap, Verity.Examples.ERC721.constructor, Verity.Examples.ERC721.owner,
      Verity.Examples.ERC721.totalSupply, Verity.Examples.ERC721.nextTokenId,
      setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageMap2, Verity.Examples.ERC721.constructor, Verity.Examples.ERC721.owner,
      Verity.Examples.ERC721.totalSupply, Verity.Examples.ERC721.nextTokenId,
      setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageMapUint, Verity.Examples.ERC721.constructor, Verity.Examples.ERC721.owner,
      Verity.Examples.ERC721.totalSupply, Verity.Examples.ERC721.nextTokenId,
      setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameContext, Verity.Examples.ERC721.constructor, Verity.Examples.ERC721.owner,
      Verity.Examples.ERC721.totalSupply, Verity.Examples.ERC721.nextTokenId,
      setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]

/-- `balanceOf` returns balances slot 3 at address `addr`. -/
theorem balanceOf_meets_spec (s : ContractState) (addr : Address) :
    balanceOf_spec addr ((Verity.Examples.ERC721.balanceOf addr).runValue s) s := by
  simp [Verity.Examples.ERC721.balanceOf, balanceOf_spec, getMapping, Contract.runValue,
    Verity.Examples.ERC721.balances]

/-- `ownerOf` decodes owner word in slot 4 for `tokenId`. -/
theorem ownerOf_meets_spec (s : ContractState) (tokenId : Uint256) :
    ownerOf_spec tokenId ((Verity.Examples.ERC721.ownerOf tokenId).runValue s) s := by
  simp [ownerOf_spec, Verity.Examples.ERC721.ownerOf, Contract.runValue, Verity.bind, Bind.bind,
    getMappingUint, Verity.Examples.ERC721.owners,
    Verity.Examples.ERC721.wordToAddress, Verity.Specs.ERC721.wordToAddress]
  simp [Pure.pure, Verity.pure]

/-- `getApproved` decodes approval word in slot 5 for `tokenId`. -/
theorem getApproved_meets_spec (s : ContractState) (tokenId : Uint256) :
    getApproved_spec tokenId ((Verity.Examples.ERC721.getApproved tokenId).runValue s) s := by
  simp [getApproved_spec, Verity.Examples.ERC721.getApproved, Contract.runValue, Verity.bind, Bind.bind,
    getMappingUint, Verity.Examples.ERC721.tokenApprovals,
    Verity.Examples.ERC721.wordToAddress, Verity.Specs.ERC721.wordToAddress]
  simp [Pure.pure, Verity.pure]

/-- `isApprovedForAll` checks nonzero operator-approval flag in slot 6. -/
theorem isApprovedForAll_meets_spec (s : ContractState) (ownerAddr operator : Address) :
    isApprovedForAll_spec ownerAddr operator ((Verity.Examples.ERC721.isApprovedForAll ownerAddr operator).runValue s) s := by
  simp [isApprovedForAll_spec, Verity.Examples.ERC721.isApprovedForAll, Contract.runValue, Verity.bind, Bind.bind,
    getMapping2, Verity.Examples.ERC721.operatorApprovals]
  simp [Pure.pure, Verity.pure]

/-- `setApprovalForAll` writes sender/operator flag and leaves other state unchanged. -/
theorem setApprovalForAll_meets_spec (s : ContractState) (operator : Address) (approved : Bool) :
    setApprovalForAll_spec s.sender operator approved s ((Verity.Examples.ERC721.setApprovalForAll operator approved).runState s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases approved <;>
      simp [Verity.Examples.ERC721.setApprovalForAll, Verity.Examples.ERC721.operatorApprovals,
        setMapping2, Verity.Examples.ERC721.boolToWord, Verity.Specs.ERC721.boolToWord,
        msgSender, Contract.runState, Verity.bind, Bind.bind]
  · intro o' op' h_neq
    simp [Verity.Examples.ERC721.setApprovalForAll, Verity.Examples.ERC721.operatorApprovals,
      setMapping2, Verity.Examples.ERC721.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind, h_neq]
  · intro op' h_neq
    simp [Verity.Examples.ERC721.setApprovalForAll, Verity.Examples.ERC721.operatorApprovals,
      setMapping2, Verity.Examples.ERC721.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind, h_neq]
  · simp [Specs.sameStorage, Verity.Examples.ERC721.setApprovalForAll, Verity.Examples.ERC721.operatorApprovals,
      setMapping2, Verity.Examples.ERC721.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageAddr, Verity.Examples.ERC721.setApprovalForAll, Verity.Examples.ERC721.operatorApprovals,
      setMapping2, Verity.Examples.ERC721.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageMap, Verity.Examples.ERC721.setApprovalForAll, Verity.Examples.ERC721.operatorApprovals,
      setMapping2, Verity.Examples.ERC721.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageMapUint, Verity.Examples.ERC721.setApprovalForAll,
      Verity.Examples.ERC721.operatorApprovals, setMapping2,
      Verity.Examples.ERC721.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameContext, Verity.Examples.ERC721.setApprovalForAll,
      Verity.Examples.ERC721.operatorApprovals, setMapping2,
      Verity.Examples.ERC721.boolToWord,
      msgSender, Contract.runState, Verity.bind, Bind.bind]

end Verity.Proofs.ERC721
