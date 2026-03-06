/-
  Formal specifications for ERC721 foundation operations.
-/

import Verity.Specs.Common
import Verity.Macro
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
  storageAddrStorage2UpdateSpec
    0 1 2
    (fun _ => initialOwner)
    (fun _ => 0)
    (fun _ => 0)
    sameStorageMapsContext
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

-- setApprovalForAll: updates only sender->operator flag in slot 6
#gen_spec_map2 setApprovalForAll_spec for3
  (sender : Address) (operator : Address) (approved : Bool)
  (6, sender, operator, (fun _ => boolToWord approved), sameStorageAddrMapUintContext)

end Contracts.ERC721.Spec
