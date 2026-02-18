/-
  Verity.AST.Counter: Unified AST for Counter

  Storage layout:  slot 0 = count (Uint256)
-/

import Verity.Denote
import Verity.Examples.Counter

namespace Verity.AST.Counter

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples.Counter (count increment decrement getCount)

/-- AST for `increment()`: count ← sload slot0; sstore slot0 (count + 1) -/
def incrementAST : Stmt :=
  .bindUint "current" (.storage 0)
    (.sstore 0 (.add (.var "current") (.lit 1)) .stop)

/-- AST for `decrement()`: count ← sload slot0; sstore slot0 (count - 1) -/
def decrementAST : Stmt :=
  .bindUint "current" (.storage 0)
    (.sstore 0 (.sub (.var "current") (.lit 1)) .stop)

/-- AST for `getCount()`: return sload slot0 -/
def getCountAST : Stmt :=
  .bindUint "x" (.storage 0)
    (.ret (.var "x"))

/-! ## Equivalence Proofs -/

/-- `increment` AST denotes to the EDSL `increment` function. -/
theorem increment_equiv :
    denoteUnit emptyEnv emptyEnvAddr incrementAST = increment := by
  rfl

/-- `decrement` AST denotes to the EDSL `decrement` function. -/
theorem decrement_equiv :
    denoteUnit emptyEnv emptyEnvAddr decrementAST = decrement := by
  rfl

/-- `getCount` AST denotes to the EDSL `getCount` function. -/
theorem getCount_equiv :
    denoteUint emptyEnv emptyEnvAddr getCountAST = getCount := by
  rfl

end Verity.AST.Counter
