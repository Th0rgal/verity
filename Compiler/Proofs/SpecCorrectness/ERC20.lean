/-
  Compiler.SpecCorrectness.ERC20

  Initial bridge theorem surface for ERC20 scaffolding.
-/

import Verity.Specs.ERC20.Spec
import Verity.Examples.ERC20
import Verity.Proofs.ERC20.Basic
import Verity.Stdlib.Math

namespace Compiler.Proofs.SpecCorrectness

open Verity
open Verity.Specs.ERC20
open Verity.Examples.ERC20

/-- Spec/EDSL agreement for `constructor`. -/
theorem erc20_constructor_spec_correct (s : ContractState) (initialOwner : Address) :
    constructor_spec initialOwner s ((constructor initialOwner).runState s) := by
  simpa using Verity.Proofs.ERC20.constructor_meets_spec s initialOwner

/-- Spec/EDSL agreement for read-only `balanceOf`. -/
theorem erc20_balanceOf_spec_correct (s : ContractState) (addr : Address) :
    balanceOf_spec addr ((balanceOf addr).runValue s) s := by
  simp [balanceOf_spec, balanceOf, getMapping, Contract.runValue, balances]

/-- Spec/EDSL agreement for read-only `allowanceOf`. -/
theorem erc20_allowanceOf_spec_correct (s : ContractState) (ownerAddr spender : Address) :
    allowance_spec ownerAddr spender ((allowanceOf ownerAddr spender).runValue s) s := by
  simp [allowance_spec, allowanceOf, getMapping2, Contract.runValue, allowances]

/-- Spec/EDSL agreement for read-only `getOwner`. -/
theorem erc20_getOwner_spec_correct (s : ContractState) :
    getOwner_spec ((getOwner).runValue s) s := by
  simp [getOwner_spec, getOwner, getStorageAddr, Contract.runValue, owner]

/-- Spec/EDSL agreement for read-only `getTotalSupply`. -/
theorem erc20_totalSupply_spec_correct (s : ContractState) :
    totalSupply_spec ((getTotalSupply).runValue s) s := by
  simpa using Verity.Proofs.ERC20.totalSupply_meets_spec s

/-- Spec/EDSL agreement for `approve` with sender-bound owner. -/
theorem erc20_approve_spec_correct (s : ContractState) (spender : Address) (amount : Uint256) :
    approve_spec s.sender spender amount s ((approve spender amount).runState s) := by
  simpa using Verity.Proofs.ERC20.approve_meets_spec s spender amount

/-- Spec/EDSL agreement for `mint` under owner and no-overflow preconditions. -/
theorem erc20_mint_spec_correct (s : ContractState) (to : Address) (amount : Uint256)
    (h_owner : s.sender = s.storageAddr 0)
    (h_no_bal_overflow : (s.storageMap 2 to : Nat) + (amount : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256)
    (h_no_sup_overflow : (s.storage 1 : Nat) + (amount : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256) :
    mint_spec to amount s ((mint to amount).runState s) := by
  simpa using Verity.Proofs.ERC20.mint_meets_spec_when_owner
    s to amount h_owner h_no_bal_overflow h_no_sup_overflow

/-- Spec/EDSL agreement for `transfer` under balance and overflow preconditions. -/
theorem erc20_transfer_spec_correct (s : ContractState) (to : Address) (amount : Uint256)
    (h_balance : s.storageMap 2 s.sender ≥ amount)
    (h_no_overflow : s.sender ≠ to →
      (s.storageMap 2 to : Nat) + (amount : Nat) ≤ Verity.Stdlib.Math.MAX_UINT256) :
    transfer_spec s.sender to amount s ((transfer to amount).runState s) := by
  simpa using Verity.Proofs.ERC20.transfer_meets_spec_when_sufficient
    s to amount h_balance h_no_overflow

end Compiler.Proofs.SpecCorrectness
