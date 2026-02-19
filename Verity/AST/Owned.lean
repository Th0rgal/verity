/-
  Verity.AST.Owned: Unified AST for Owned

  Storage layout:  slot 0 = owner (Address)

  `transferOwnership` uses `bind_assoc` and `bind_pure_left` to flatten
  the nested `bind` from `onlyOwner`/`isOwner` helper composition.
-/

import Verity.Denote
import Verity.Examples.Owned

namespace Verity.AST.Owned

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples.Owned (constructor transferOwnership getOwner)

/-- AST for `constructor(initialOwner)`: sstoreAddr slot0 initialOwner -/
def constructorAST : Stmt :=
  .sstoreAddr 0 (.varAddr "initialOwner") .stop

/-- AST for `transferOwnership(newOwner)` (inlined onlyOwner/isOwner):
    sender ← msgSender
    currentOwner ← sloadAddr slot0
    require (sender == currentOwner)
    sstoreAddr slot0 newOwner -/
def transferOwnershipAST : Stmt :=
  .bindAddr "sender" .sender
    (.bindAddr "currentOwner" (.storageAddr 0)
      (.require (.eqAddr (.varAddr "sender") (.varAddr "currentOwner")) "Caller is not the owner"
        (.sstoreAddr 0 (.varAddr "newOwner") .stop)))

/-- AST for `getOwner()`: return sloadAddr slot0 -/
def getOwnerAST : Stmt :=
  .bindAddr "x" (.storageAddr 0)
    (.retAddr (.varAddr "x"))

/-! ## Equivalence Proofs

`constructor` and `getOwner` hold by `rfl`. `transferOwnership` needs
`bind_assoc` + `bind_pure_left` to flatten the EDSL's nested `bind`
from `onlyOwner` → `isOwner` composition. -/

/-- `constructor` AST denotes to the EDSL `constructor` function. -/
theorem constructor_equiv (initialOwner : Address) :
    denoteUnit emptyEnv (fun s => if s == "initialOwner" then initialOwner else 0) constructorAST
    = constructor initialOwner := by
  rfl

/-- `transferOwnership` AST denotes to the EDSL `transferOwnership` function. -/
theorem transferOwnership_equiv (newOwner : Address) :
    denoteUnit emptyEnv (fun s => if s == "newOwner" then newOwner else 0) transferOwnershipAST
    = transferOwnership newOwner := by
  simp only [transferOwnership, Verity.Examples.Owned.onlyOwner,
    Verity.Examples.Owned.isOwner, Verity.Examples.Owned.owner,
    Bind.bind, Pure.pure, Contract.bind_assoc, Contract.bind_pure_left]
  rfl

/-- `getOwner` AST denotes to the EDSL `getOwner` function. -/
theorem getOwner_equiv :
    denoteAddress emptyEnv emptyEnvAddr getOwnerAST
    = getOwner := by
  rfl

end Verity.AST.Owned
