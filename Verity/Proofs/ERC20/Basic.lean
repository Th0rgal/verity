/-
  Basic proofs for ERC20 foundation scaffold.
-/

import Verity.Specs.ERC20.Spec
import Verity.Examples.ERC20

namespace Verity.Proofs.ERC20

open Verity
open Verity.Specs.ERC20
open Verity.Examples.ERC20

/-- `balanceOf` returns the value stored in balances slot 2 for `addr`. -/
theorem balanceOf_meets_spec (s : ContractState) (addr : Address) :
    balanceOf_spec addr ((balanceOf addr).runValue s) s := by
  simp [balanceOf, balanceOf_spec, getMapping, Contract.runValue, balances]

/-- `allowanceOf` returns the value stored in allowances slot 3 for `(owner, spender)`. -/
theorem allowanceOf_meets_spec (s : ContractState) (ownerAddr spender : Address) :
    allowance_spec ownerAddr spender ((allowanceOf ownerAddr spender).runValue s) s := by
  simp [allowanceOf, allowance_spec, getMapping2, Contract.runValue, allowances]

/-- `getTotalSupply` returns slot 1. -/
theorem totalSupply_meets_spec (s : ContractState) :
    totalSupply_spec ((getTotalSupply).runValue s) s := by
  simp [getTotalSupply, totalSupply_spec, getStorage, Contract.runValue, totalSupply]

end Verity.Proofs.ERC20
