/-
  Compiler.Proofs.SpecCorrectness.AddressEncoding

  Shared helper lemmas for address encoding and Uint256 arithmetic
  used across SpecCorrectness proofs.
-/

import Compiler.Proofs.SpecInterpreter
import Compiler.Hex
import DumbContracts.Core.Uint256
import DumbContracts.EVM.Uint256

namespace Compiler.Proofs.SpecCorrectness

open Compiler.Hex
open DumbContracts
open DumbContracts.Core.Uint256 (modulus)

/-- addressToNat is always below the 160-bit address modulus. -/
theorem addressToNat_lt_addressModulus (addr : Address) :
    addressToNat addr < addressModulus := by
  unfold addressToNat addressModulus
  split
  · rename_i n _
    exact Nat.mod_lt _ (by decide : 2^160 > 0)
  · rename_i _
    exact Nat.mod_lt _ (by decide : 2^160 > 0)

/-- addressToNat mod 2^160 is identity. -/
theorem addressToNat_mod_address (addr : Address) :
    addressToNat addr % addressModulus = addressToNat addr := by
  exact Nat.mod_eq_of_lt (addressToNat_lt_addressModulus addr)

/-- Value-level view of Uint256.add for proof automation. -/
theorem uint256_add_val (a : DumbContracts.Core.Uint256) (amount : Nat) :
    (DumbContracts.EVM.Uint256.add a (DumbContracts.Core.Uint256.ofNat amount)).val =
      (a.val + amount) % DumbContracts.Core.Uint256.modulus := by
  cases a with
  | mk aval a_lt =>
    let m := DumbContracts.Core.Uint256.modulus
    have h_mod : aval % m = aval := by
      exact Nat.mod_eq_of_lt a_lt
    unfold DumbContracts.EVM.Uint256.add DumbContracts.Core.Uint256.add
    simp [HAdd.hAdd, DumbContracts.Core.Uint256.add, DumbContracts.Core.Uint256.val_ofNat]
    have h_add : (aval + amount) % m = (aval % m + amount % m) % m :=
      Nat.add_mod aval amount m
    have h_add' : (aval + amount) % m = (aval + amount % m) % m := by
      simpa [h_mod] using h_add
    exact h_add'.symm

end Compiler.Proofs.SpecCorrectness
