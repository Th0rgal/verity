/-
  Compiler.SpecCorrectness.ERC20

  Initial bridge theorem surface for ERC20 scaffolding.
-/

import Verity.Specs.ERC20.Spec
import Verity.Examples.ERC20

namespace Compiler.Proofs.SpecCorrectness

open Verity
open Verity.Specs.ERC20
open Verity.Examples.ERC20

/-- Spec/EDSL agreement for read-only `balanceOf`. -/
theorem erc20_balanceOf_spec_correct (s : ContractState) (addr : Address) :
    balanceOf_spec addr ((balanceOf addr).runValue s) s := by
  simp [balanceOf_spec, balanceOf, getMapping, Contract.runValue, balances]

end Compiler.Proofs.SpecCorrectness
