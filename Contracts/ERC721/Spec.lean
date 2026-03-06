/-
  Formal specifications for ERC721 foundation operations.
-/

import Verity.Specs.Common
import Verity.EVM.Uint256

namespace Contracts.ERC721.Spec

open Verity
open Verity.Specs

def addressToWord (a : Address) : Uint256 :=
  (a.toNat : Uint256)

def wordToAddress (w : Uint256) : Address :=
  Verity.Core.Address.ofNat (w : Nat)

def boolToWord (b : Bool) : Uint256 :=
  if b then 1 else 0

/-- constructor: sets owner and initializes counters to zero -/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = initialOwner ∧
  storageAddrUnchangedExcept 0 s s' ∧
  storage2UpdateSpec
    1 2
    (fun _ => 0)
    (fun _ => 0)
    (fun st st' => sameStorageMap st st' ∧ sameStorageMap2 st st' ∧ sameStorageMapUint st st' ∧ sameContext st st')
    s s'

/-- balanceOf: returns current balance of `addr` -/
def balanceOf_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 3 addr

/-- ownerOf: reverts when `tokenId` is unminted, otherwise returns token owner -/
def ownerOf_spec (tokenId : Uint256) (result : ContractResult Address) (s : ContractState) : Prop :=
  let ownerWord := s.storageMapUint 4 tokenId
  if ownerWord != 0 then
    result = ContractResult.success (wordToAddress ownerWord) s
  else
    result = ContractResult.revert "Token does not exist" s

/-- getApproved: reverts when `tokenId` is unminted, otherwise returns approval -/
def getApproved_spec (tokenId : Uint256) (result : ContractResult Address) (s : ContractState) : Prop :=
  let ownerWord := s.storageMapUint 4 tokenId
  if ownerWord != 0 then
    result = ContractResult.success (wordToAddress (s.storageMapUint 5 tokenId)) s
  else
    result = ContractResult.revert "Token does not exist" s

/-- isApprovedForAll: nonzero flag means approved -/
def isApprovedForAll_spec (ownerAddr operator : Address) (result : Bool) (s : ContractState) : Prop :=
  result = (s.storageMap2 6 ownerAddr operator != 0)

/-- setApprovalForAll: updates only sender->operator flag in slot 6 -/
def setApprovalForAll_spec
    (sender operator : Address) (approved : Bool) (s s' : ContractState) : Prop :=
  s'.storageMap2 6 sender operator = boolToWord approved ∧
  (∀ o' : Address, ∀ op' : Address,
    o' ≠ sender → s'.storageMap2 6 o' op' = s.storageMap2 6 o' op') ∧
  (∀ op' : Address,
    op' ≠ operator → s'.storageMap2 6 sender op' = s.storageMap2 6 sender op') ∧
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageMapUint s s' ∧
  sameContext s s'

end Contracts.ERC721.Spec
