/-
  Verity.AST.OwnedCounter: Unified AST for OwnedCounter

  Storage layout:  slot 0 = owner (Address), slot 1 = count (Uint256)

  Owner-gated functions use `bind_assoc` + `bind_pure_left` to flatten
  the nested `bind` from `onlyOwner`/`isOwner` composition.
-/

import Verity.Denote
import Verity.Examples.OwnedCounter

namespace Verity.AST.OwnedCounter

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples.OwnedCounter
  (constructor increment decrement getCount getOwner transferOwnership)

/-- AST for `constructor(initialOwner)`: sstoreAddr slot0 initialOwner -/
def constructorAST : Stmt :=
  .sstoreAddr 0 (.varAddr "initialOwner") .stop

/-- AST for `increment()` (inlined onlyOwner/isOwner):
    sender ← msgSender
    currentOwner ← sloadAddr slot0
    require (sender == currentOwner)
    current ← sload slot1
    sstore slot1 (current + 1) -/
def incrementAST : Stmt :=
  .bindAddr "sender" .sender
    (.bindAddr "currentOwner" (.storageAddr 0)
      (.require (.eqAddr (.varAddr "sender") (.varAddr "currentOwner")) "Caller is not the owner"
        (.bindUint "current" (.storage 1)
          (.sstore 1 (.add (.var "current") (.lit 1)) .stop))))

/-- AST for `decrement()` (inlined onlyOwner/isOwner):
    sender ← msgSender
    currentOwner ← sloadAddr slot0
    require (sender == currentOwner)
    current ← sload slot1
    sstore slot1 (current - 1) -/
def decrementAST : Stmt :=
  .bindAddr "sender" .sender
    (.bindAddr "currentOwner" (.storageAddr 0)
      (.require (.eqAddr (.varAddr "sender") (.varAddr "currentOwner")) "Caller is not the owner"
        (.bindUint "current" (.storage 1)
          (.sstore 1 (.sub (.var "current") (.lit 1)) .stop))))

/-- AST for `getCount()`: return sload slot1 -/
def getCountAST : Stmt :=
  .bindUint "x" (.storage 1)
    (.ret (.var "x"))

/-- AST for `getOwner()`: return sloadAddr slot0 -/
def getOwnerAST : Stmt :=
  .bindAddr "x" (.storageAddr 0)
    (.retAddr (.varAddr "x"))

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

/-! ## Equivalence Proofs

Standalone functions use `rfl`. Owner-gated functions use `bind_assoc`
+ `bind_pure_left` (via `inline_onlyOwner`) to flatten `onlyOwner`/`isOwner`. -/

/-- `constructor` AST denotes to the EDSL `constructor` function. -/
theorem constructor_equiv (initialOwner : Address) :
    denoteUnit emptyEnv (fun s => if s == "initialOwner" then initialOwner else "") constructorAST
    = constructor initialOwner := by
  rfl

private theorem inline_onlyOwner :
    ∀ (f : Unit → Contract α),
    Verity.bind Verity.Examples.OwnedCounter.onlyOwner f
    = Verity.bind msgSender fun sender =>
        Verity.bind (getStorageAddr ⟨0⟩) fun currentOwner =>
          Verity.bind (Verity.require (sender == currentOwner) "Caller is not the owner") f := by
  intro f
  simp only [Verity.Examples.OwnedCounter.onlyOwner,
    Verity.Examples.OwnedCounter.isOwner,
    Verity.Examples.OwnedCounter.owner,
    Bind.bind, Pure.pure, Contract.bind_assoc, Contract.bind_pure_left]

/-- `increment` AST denotes to the EDSL `increment` function. -/
theorem increment_equiv :
    denoteUnit emptyEnv emptyEnvAddr incrementAST = increment := by
  simp only [increment, Bind.bind, inline_onlyOwner, Verity.Examples.OwnedCounter.count]; rfl

/-- `decrement` AST denotes to the EDSL `decrement` function. -/
theorem decrement_equiv :
    denoteUnit emptyEnv emptyEnvAddr decrementAST = decrement := by
  simp only [decrement, Bind.bind, inline_onlyOwner, Verity.Examples.OwnedCounter.count]; rfl

/-- `getCount` AST denotes to the EDSL `getCount` function. -/
theorem getCount_equiv :
    denoteUint emptyEnv emptyEnvAddr getCountAST = getCount := by
  rfl

/-- `getOwner` AST denotes to the EDSL `getOwner` function. -/
theorem getOwner_equiv :
    denoteAddress emptyEnv emptyEnvAddr getOwnerAST = getOwner := by
  rfl

/-- `transferOwnership` AST denotes to the EDSL `transferOwnership` function. -/
theorem transferOwnership_equiv (newOwner : Address) :
    denoteUnit emptyEnv (fun s => if s == "newOwner" then newOwner else "") transferOwnershipAST
    = transferOwnership newOwner := by
  simp only [transferOwnership, Bind.bind, inline_onlyOwner, Verity.Examples.OwnedCounter.owner]; rfl

end Verity.AST.OwnedCounter
