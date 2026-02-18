/-
  Verity.AST.Owned: Unified AST for Owned

  All three Owned functions are migrated. `constructor` and `getOwner`
  use `rfl`. `transferOwnership` uses `bind_assoc` to flatten the
  nested `bind` from `onlyOwner`/`isOwner` helper composition.
-/

import Verity.Denote
import Verity.Examples.Owned

namespace Verity.AST.Owned

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples.Owned (constructor transferOwnership getOwner)

/-- AST for `constructor(initialOwner)`: setStorageAddr 0 initialOwner -/
def constructorAST : Stmt :=
  .sstoreAddr 0 (.varAddr "initialOwner") .stop

/-- AST for `transferOwnership(newOwner)` (inlined `onlyOwner`/`isOwner`):
    let sender ← msgSender
    let currentOwner ← getStorageAddr 0
    require (sender == currentOwner) "Caller is not the owner"
    setStorageAddr 0 newOwner -/
def transferOwnershipAST : Stmt :=
  .bindAddr "sender" .sender
    (.bindAddr "currentOwner" (.storageAddr 0)
      (.require (.eqAddr (.varAddr "sender") (.varAddr "currentOwner")) "Caller is not the owner"
        (.sstoreAddr 0 (.varAddr "newOwner") .stop)))

/-- AST for `getOwner()`: getStorageAddr 0 -/
def getOwnerAST : Stmt :=
  .bindAddr "x" (.storageAddr 0)
    (.retAddr (.varAddr "x"))

/-!
## Equivalence Proofs

`constructor` and `getOwner` hold by `rfl`. `transferOwnership` requires
`bind_assoc` because the EDSL uses helper composition (`onlyOwner` calling
`isOwner`), producing nested `bind (bind m f) g` that the flat AST
denotation flattens into `bind m (fun x => bind (f x) g)`.
-/

theorem constructor_equiv (initialOwner : Address) :
    denoteUnit emptyEnv (fun s => if s == "initialOwner" then initialOwner else "") constructorAST
    = constructor initialOwner := by
  rfl

theorem transferOwnership_equiv (newOwner : Address) :
    denoteUnit emptyEnv (fun s => if s == "newOwner" then newOwner else "") transferOwnershipAST
    = transferOwnership newOwner := by
  simp only [transferOwnership, Verity.Examples.Owned.onlyOwner,
    Verity.Examples.Owned.isOwner, Verity.Examples.Owned.owner,
    Bind.bind, Pure.pure, bind_assoc, bind_pure]
  rfl

theorem getOwner_equiv :
    denoteAddress emptyEnv emptyEnvAddr getOwnerAST
    = getOwner := by
  rfl

end Verity.AST.Owned
