/-
  Formal specifications for SimpleToken operations

  This file defines the expected behavior of each SimpleToken operation
  in terms of state transitions and return values.
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

/-! ## Operation Specifications

These define the expected behavior of each SimpleToken operation.
-/

/-- Specification for constructor operation:
    - Sets the owner to the provided address
    - Initializes total supply to 0
    - Preserves balances mapping (implicitly 0)
    - Preserves contract context
-/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = initialOwner ∧
  s'.storage 2 = 0 ∧
  storageAddrUnchangedExcept 0 s s' ∧
  storageUnchangedExcept 2 s s' ∧
  sameStorageMap s s' ∧
  sameContext s s'

/-- Specification for mint operation (when caller is owner):
    - Increases balance of 'to' address by 'amount'
    - Increases total supply by 'amount'
    - Preserves other balances
    - Preserves owner
-/
def mint_spec (to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 1 to = add (s.storageMap 1 to) amount ∧
  s'.storage 2 = add (s.storage 2) amount ∧
  storageMapUnchangedExceptKey 1 to s s' ∧
  s'.storageAddr 0 = s.storageAddr 0 ∧
  storageMapUnchangedExceptSlot 1 s s' ∧
  storageUnchangedExcept 2 s s' ∧
  sameContext s s'

/-- Specification for transfer operation (when sender has sufficient balance):
    - Decreases sender's balance by 'amount'
    - Increases recipient's balance by 'amount'
    - Preserves total supply
    - Preserves other balances
    - Preserves owner
-/
def transfer_spec (sender to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s.storageMap 1 sender ≥ amount ∧
  s'.storageMap 1 sender = sub (s.storageMap 1 sender) amount ∧
  s'.storageMap 1 to = add (s.storageMap 1 to) amount ∧
  storageMapUnchangedExceptKeys 1 sender to s s' ∧
  s'.storageAddr 0 = s.storageAddr 0 ∧
  storageMapUnchangedExceptSlot 1 s s' ∧
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameContext s s'

/-- Specification for balanceOf operation:
    - Returns the balance of the given address
    - Does not modify state
-/
def balanceOf_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 1 addr

/-- Specification for getTotalSupply operation:
    - Returns the current total supply
    - Does not modify state
-/
def getTotalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 2

/-- Specification for getOwner operation:
    - Returns the current owner address
    - Does not modify state
-/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

/-! ## Combined Specifications

Properties about sequences of operations.
-/

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
