/-
  Formal specifications for SimpleToken operations.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common
import DumbContracts.EVM.Uint256

namespace DumbContracts.Specs.SimpleToken

open DumbContracts
open DumbContracts.EVM.Uint256

/-! ## Storage Slot Definitions -/

def owner : StorageSlot Address := ⟨0⟩
def balances : StorageSlot (Address → Uint256) := ⟨1⟩
def totalSupply : StorageSlot Uint256 := ⟨2⟩

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

/-- Mint followed by balanceOf returns increased balance -/
def mint_balanceOf_spec (to : Address) (amount : Uint256) (s : ContractState) (result : Uint256) : Prop :=
  result = add (s.storageMap 1 to) amount

/-- Transfer followed by balanceOf (sender) returns decreased balance -/
def transfer_balanceOf_sender_spec (sender _to : Address) (amount : Uint256) (s : ContractState) (result : Uint256) : Prop :=
  s.storageMap 1 sender ≥ amount →
  result = sub (s.storageMap 1 sender) amount

/-- Transfer followed by balanceOf (recipient) returns increased balance -/
def transfer_balanceOf_recipient_spec (sender to : Address) (amount : Uint256) (s : ContractState) (result : Uint256) : Prop :=
  s.storageMap 1 sender ≥ amount →
  result = add (s.storageMap 1 to) amount

end DumbContracts.Specs.SimpleToken
