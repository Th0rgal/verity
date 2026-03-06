/-
  Formal specifications for SimpleToken operations.
-/

import Verity.Specs.Common
import Verity.Macro
import Verity.EVM.Uint256

namespace Contracts.SimpleToken.Spec

open Verity
open Verity.EVM.Uint256
open Verity.Specs

/-! ## Operation Specifications -/

-- Constructor: sets owner and initializes total supply to 0
#gen_spec_addr_storage constructor_spec for (initialOwner : Address)
  (0, 2, (fun _ => initialOwner), (fun _ => 0), sameMapContext)

-- Mint: increases balance and total supply by amount (owner only)
#gen_spec_map_storage mint_spec for (to : Address) (amount : Uint256)
  (1, to, (fun st => add (st.storageMap 1 to) amount), 2, (fun st => add (st.storage 2) amount), sameStorageAddrSlotContext 0)

/-- Transfer: moves amount from sender to recipient, preserves total supply -/
def transfer_spec (sender to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s.storageMap 1 sender ≥ amount ∧
  storageMapTransferSpec 1 sender to amount
    (fun st st' =>
      sameStorageAddrSlot 0 st st' ∧
      sameStorageAddrContext st st')
    s s'

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

end Contracts.SimpleToken.Spec
