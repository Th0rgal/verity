/-
  Formal specifications for SimpleToken operations.
-/

import Verity.Core
import Verity.Specs.Common
import Verity.EVM.Uint256

namespace Verity.Specs.SimpleToken

open Verity
open Verity.EVM.Uint256

/-! ## Operation Specifications -/

/-- Constructor: sets owner and initializes total supply to 0 -/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = initialOwner ∧
  s'.storage 2 = 0 ∧
  storageAddrUnchangedExcept 0 s s' ∧
  storageUnchangedExcept 2 s s' ∧
  sameStorageMap s s' ∧
  sameContext s s'

/-- Mint: increases balance and total supply by amount (owner only) -/
def mint_spec (to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 1 to = add (s.storageMap 1 to) amount ∧
  s'.storage 2 = add (s.storage 2) amount ∧
  storageMapUnchangedExceptKeyAtSlot 1 to s s' ∧
  s'.storageAddr 0 = s.storageAddr 0 ∧
  storageUnchangedExcept 2 s s' ∧
  sameContext s s'

/-- Transfer: moves amount from sender to recipient, preserves total supply -/
def transfer_spec (sender to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s.storageMap 1 sender ≥ amount ∧
  (if sender == to
    then s'.storageMap 1 sender = s.storageMap 1 sender
    else s'.storageMap 1 sender = sub (s.storageMap 1 sender) amount) ∧
  (if sender == to
    then s'.storageMap 1 to = s.storageMap 1 to
    else s'.storageMap 1 to = add (s.storageMap 1 to) amount) ∧
  (if sender == to
    then storageMapUnchangedExceptKeyAtSlot 1 sender s s'
    else storageMapUnchangedExceptKeysAtSlot 1 sender to s s') ∧
  s'.storageAddr 0 = s.storageAddr 0 ∧
  sameStorageAddrContext s s'

/-- balanceOf: returns the balance of the given address -/
def balanceOf_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 1 addr

/-- getTotalSupply: returns the current total supply -/
def getTotalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 2

/-- getOwner: returns the current owner address -/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

/-! ## Combined Specifications -/

/-- Constructor followed by getTotalSupply returns 0 -/
def constructor_getTotalSupply_spec (_initialOwner : Address) (_s : ContractState) (result : Uint256) : Prop :=
  result = 0

end Verity.Specs.SimpleToken
