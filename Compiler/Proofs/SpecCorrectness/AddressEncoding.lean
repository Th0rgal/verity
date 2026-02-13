/-
  Compiler.Proofs.SpecCorrectness.AddressEncoding

  Shared helper lemmas for address encoding and Uint256 arithmetic
  used across SpecCorrectness proofs.
-/

import Compiler.Proofs.Automation
import Compiler.Proofs.SpecInterpreter
import Compiler.Hex
import DumbContracts.Core.Uint256
import DumbContracts.EVM.Uint256

namespace Compiler.Proofs.SpecCorrectness

open Compiler.Hex
open Compiler.Proofs.Automation
open DumbContracts
open DumbContracts.Core.Uint256 (modulus)

/-!
## Shared axioms
-/

-- Re-export the shared injectivity axiom from Automation to keep proofs concise.
theorem addressToNat_injective :
    ∀ (a b : Address), addressToNat a = addressToNat b → a = b :=
  Compiler.Proofs.Automation.addressToNat_injective

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

end Compiler.Proofs.SpecCorrectness
