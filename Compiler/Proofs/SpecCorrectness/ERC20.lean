/-
  Compiler.SpecCorrectness.ERC20

  Initial bridge theorem surface for ERC20 scaffolding.
-/

import Verity.Specs.ERC20.Spec
import Verity.Examples.ERC20
import Verity.Proofs.ERC20.Basic

namespace Compiler.Proofs.SpecCorrectness

open Verity
open Verity.Specs.ERC20
open Verity.Examples.ERC20

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

/-- Spec/EDSL agreement for `approve` with sender-bound owner. -/
theorem erc20_approve_spec_correct (s : ContractState) (spender : Address) (amount : Uint256) :
    approve_spec s.sender spender amount s ((approve spender amount).runState s) := by
  simpa using Verity.Proofs.ERC20.approve_meets_spec s spender amount

end Compiler.Proofs.SpecCorrectness
