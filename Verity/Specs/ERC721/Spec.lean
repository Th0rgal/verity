/-
  Formal specifications for ERC721 foundation operations.
-/

import Verity.Specs.Common
import Verity.EVM.Uint256

namespace Verity.Specs.ERC721

open Verity

def addressToWord (a : Address) : Uint256 :=
  (a.toNat : Uint256)

def wordToAddress (w : Uint256) : Address :=
  Verity.Core.Address.ofNat (w : Nat)

def boolToWord (b : Bool) : Uint256 :=
  if b then 1 else 0

/-- constructor: sets owner and initializes counters to zero -/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = initialOwner ∧
  s'.storage 1 = 0 ∧
  s'.storage 2 = 0 ∧
  storageAddrUnchangedExcept 0 s s' ∧
  (∀ slot : Nat, slot ≠ 1 → slot ≠ 2 → s'.storage slot = s.storage slot) ∧
  sameStorageMap s s' ∧
  sameStorageMap2 s s' ∧
  sameStorageMapUint s s' ∧
  sameContext s s'

/-- balanceOf: returns current balance of `addr` -/
def balanceOf_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 3 addr

/-- ownerOf: returns the decoded owner word for `tokenId` -/
def ownerOf_spec (tokenId : Uint256) (result : Address) (s : ContractState) : Prop :=
  result = wordToAddress (s.storageMapUint 4 tokenId)

/-- getApproved: returns the decoded approval word for `tokenId` -/
def getApproved_spec (tokenId : Uint256) (result : Address) (s : ContractState) : Prop :=
  result = wordToAddress (s.storageMapUint 5 tokenId)

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

end Verity.Specs.ERC721
