/-
  Formal specifications for ERC20 foundation operations.
-/

import Verity.Specs.Common
import Verity.EVM.Uint256

namespace Contracts.ERC20.Spec

open Verity
open Verity.EVM.Uint256
open Verity.Specs

/-! ## Operation Specifications -/

/-- constructor: sets owner and initializes total supply to zero -/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  storageAddrStorageUpdateSpec
    0 1
    (fun _ => initialOwner)
    (fun _ => 0)
    sameStorageMap2Context
    s s'

/-- mint: increases recipient balance and total supply by amount -/
def mint_spec (to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  storageMapAndStorageUpdateSpec
    2 to (fun st => add (st.storageMap 2 to) amount)
    1 (fun st => add (st.storage 1) amount)
    (fun st st' =>
      st'.storageAddr 0 = st.storageAddr 0 ∧
      sameStorageMap2 st st' ∧
      sameContext st st')
    s s'

/-- transfer: sender balance decreases and recipient balance increases by amount -/
def transfer_spec (sender to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s.storageMap 2 sender ≥ amount ∧
  storageMapTransferSpec 2 sender to amount
    (fun st st' =>
      st'.storage 1 = st.storage 1 ∧
      st'.storageAddr 0 = st.storageAddr 0 ∧
      sameStorageMap2 st st' ∧
      sameContext st st')
    s s'

/-- approve: updates the owner-spender allowance mapping entry -/
def approve_spec (ownerAddr spender : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  storageMap2UpdateSpec
    3 ownerAddr spender (fun _ => amount)
    (fun st st' =>
      sameStorage st st' ∧
      sameStorageAddr st st' ∧
      sameStorageMap st st' ∧
      sameContext st st')
    s s'

/-- transferFrom: debits `fromAddr`, credits `to`, and updates allowance for spender -/
def transferFrom_spec (spender fromAddr to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s.storageMap2 3 fromAddr spender ≥ amount ∧
  s.storageMap 2 fromAddr ≥ amount ∧
  storageMapTransferFromSpec 2 3 fromAddr to spender amount
    (fun st st' =>
      sameStorage st st' ∧
      sameStorageAddr st st' ∧
      sameContext st st')
    s s'

/-- balanceOf: returns current balance of `addr` -/
def balanceOf_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 2 addr

/-- allowance: returns current allowance(owner, spender) -/
def allowance_spec (ownerAddr spender : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap2 3 ownerAddr spender

/-- totalSupply: returns the total minted minus burned token count -/
def totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 1

/-- getOwner: returns the current owner address from slot 0 -/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

end Contracts.ERC20.Spec
