/-
  Verity.AST.SimpleStorage: Unified AST for SimpleStorage

  Storage layout:  slot 0 = storedData (Uint256)
-/

import Verity.Denote
import Verity.Examples.SimpleStorage

namespace Verity.AST.SimpleStorage

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples (storedData store retrieve)

/-- AST for `store(value)`: sstore slot0 value -/
def storeAST : Stmt :=
  .sstore 0 (.var "value") .stop

/-- AST for `retrieve()`: return sload slot0 -/
def retrieveAST : Stmt :=
  .bindUint "x" (.storage 0)
    (.ret (.var "x"))

/-! ## Equivalence Proofs -/

/-- `store` AST denotes to the EDSL `store` function. -/
theorem store_equiv (value : Uint256) :
    denoteUnit (fun s => if s == "value" then value else 0) emptyEnvAddr storeAST
    = store value := by
  rfl

/-- `retrieve` AST denotes to the EDSL `retrieve` function. -/
theorem retrieve_equiv :
    denoteUint emptyEnv emptyEnvAddr retrieveAST
    = retrieve := by
  rfl

end Verity.AST.SimpleStorage
