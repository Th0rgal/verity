/-
  Basic proofs for ERC20 foundation scaffold.
-/

import Verity.Specs.ERC20.Spec
import Verity.Examples.ERC20

namespace Verity.Proofs.ERC20

open Verity
open Verity.Specs.ERC20
open Verity.Examples.ERC20

/-- `constructor` sets owner slot 0 and initializes supply slot 1. -/
theorem constructor_meets_spec (s : ContractState) (initialOwner : Address) :
    constructor_spec initialOwner s ((constructor initialOwner).runState s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [constructor, owner, setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]
  · simp [constructor, totalSupply, setStorageAddr, setStorage, Contract.runState, Verity.bind, Bind.bind]
  · intro slot h_neq
    simp [constructor, owner, setStorageAddr, setStorage, Contract.runState, Verity.bind,
      Bind.bind, h_neq]
  · intro slot h_neq
    simp [constructor, owner, totalSupply, setStorageAddr, setStorage, Contract.runState,
      Verity.bind, Bind.bind, h_neq]
  · simp [Specs.sameStorageMap, constructor, owner, totalSupply, setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageMap2, constructor, owner, totalSupply, setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameContext, constructor, owner, totalSupply, setStorageAddr, setStorage,
      Contract.runState, Verity.bind, Bind.bind]

/-- `approve` writes allowance(sender, spender) and leaves other state unchanged. -/
theorem approve_meets_spec (s : ContractState) (spender : Address) (amount : Uint256) :
    approve_spec s.sender spender amount s ((approve spender amount).runState s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [approve, allowances, setMapping2, msgSender, Contract.runState, Verity.bind, Bind.bind]
  · intro o' sp' h_neq
    simp [approve, allowances, setMapping2, msgSender, Contract.runState, Verity.bind, Bind.bind,
      h_neq]
  · intro sp' h_neq
    simp [approve, allowances, setMapping2, msgSender, Contract.runState, Verity.bind, Bind.bind,
      h_neq]
  · simp [Specs.sameStorage, approve, allowances, setMapping2, msgSender,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageAddr, approve, allowances, setMapping2, msgSender,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameStorageMap, approve, allowances, setMapping2, msgSender,
      Contract.runState, Verity.bind, Bind.bind]
  · simp [Specs.sameContext, approve, allowances, setMapping2, msgSender,
      Contract.runState, Verity.bind, Bind.bind]

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

/-- `getOwner` returns owner slot 0. -/
theorem getOwner_meets_spec (s : ContractState) :
    getOwner_spec ((getOwner).runValue s) s := by
  simp [getOwner, getOwner_spec, getStorageAddr, Contract.runValue, owner]

end Verity.Proofs.ERC20
