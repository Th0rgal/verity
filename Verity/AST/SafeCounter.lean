/-
  Verity.AST.SafeCounter: Unified AST for SafeCounter

  Storage layout:  slot 0 = count (Uint256)

  Like Counter but with overflow/underflow protection via `safeAdd`/`safeSub`.
-/

import Verity.Denote
import Verity.Examples.SafeCounter

namespace Verity.AST.SafeCounter

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples.SafeCounter (count increment decrement getCount)

/-- AST for `increment()`:
    count ← sload slot0
    newCount ← requireSomeUint (safeAdd count 1) "Overflow in increment"
    sstore slot0 newCount -/
def incrementAST : Stmt :=
  .bindUint "current" (.storage 0)
    (.requireSome "newCount" (.safeAdd (.var "current") (.lit 1)) "Overflow in increment"
      (.sstore 0 (.var "newCount") .stop))

/-- AST for `decrement()`:
    count ← sload slot0
    newCount ← requireSomeUint (safeSub count 1) "Underflow in decrement"
    sstore slot0 newCount -/
def decrementAST : Stmt :=
  .bindUint "current" (.storage 0)
    (.requireSome "newCount" (.safeSub (.var "current") (.lit 1)) "Underflow in decrement"
      (.sstore 0 (.var "newCount") .stop))

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

end Verity.AST.SafeCounter
