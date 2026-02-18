/-
  Verity.AST.SimpleToken: Unified AST for SimpleToken

  Storage layout:  slot 0 = owner (Address)
                   slot 1 = balances (Address → Uint256)
                   slot 2 = totalSupply (Uint256)

  Owner-gated `mint` uses `bind_assoc` + `bind_pure_left`. `transfer`
  uses `ite` for the self-transfer short-circuit.
-/

import Verity.Denote
import Verity.Examples.SimpleToken

namespace Verity.AST.SimpleToken

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples.SimpleToken
  (constructor mint transfer balanceOf getTotalSupply getOwner)

/-- AST for `constructor(initialOwner)`:
    sstoreAddr slot0 initialOwner
    sstore slot2 0 -/
def constructorAST : Stmt :=
  .sstoreAddr 0 (.varAddr "initialOwner")
    (.sstore 2 (.lit 0) .stop)

/-- AST for `mint(to, amount)` (inlined onlyOwner/isOwner):
    sender ← msgSender
    currentOwner ← sloadAddr slot0
    require (sender == currentOwner)
    currentBal ← mapping slot1[to]
    newBal ← requireSomeUint (safeAdd currentBal amount)
    currentSupply ← sload slot2
    newSupply ← requireSomeUint (safeAdd currentSupply amount)
    mstore slot1[to] newBal
    sstore slot2 newSupply -/
def mintAST : Stmt :=
  .bindAddr "sender" .sender
    (.bindAddr "currentOwner" (.storageAddr 0)
      (.require (.eqAddr (.varAddr "sender") (.varAddr "currentOwner")) "Caller is not the owner"
        (.bindUint "currentBalance" (.mapping 1 (.varAddr "to"))
          (.requireSome "newBalance" (.safeAdd (.var "currentBalance") (.var "amount")) "Balance overflow"
            (.bindUint "currentSupply" (.storage 2)
              (.requireSome "newSupply" (.safeAdd (.var "currentSupply") (.var "amount")) "Supply overflow"
                (.mstore 1 (.varAddr "to") (.var "newBalance")
                  (.sstore 2 (.var "newSupply") .stop))))))))

/-- AST for `transfer(to, amount)`:
    sender ← msgSender
    senderBal ← mapping slot1[sender]
    require (senderBal >= amount)
    if sender == to then stop
    else
      recipientBal ← mapping slot1[to]
      newRecipientBal ← requireSomeUint (safeAdd recipientBal amount)
      mstore slot1[sender] (senderBal - amount)
      mstore slot1[to] newRecipientBal -/
def transferAST : Stmt :=
  .bindAddr "sender" .sender
    (.bindUint "senderBalance" (.mapping 1 (.varAddr "sender"))
      (.require (.ge (.var "senderBalance") (.var "amount")) "Insufficient balance"
        (.ite (.eqAddr (.varAddr "sender") (.varAddr "to"))
          .stop
          (.bindUint "recipientBalance" (.mapping 1 (.varAddr "to"))
            (.requireSome "newRecipientBalance"
              (.safeAdd (.var "recipientBalance") (.var "amount"))
              "Recipient balance overflow"
              (.mstore 1 (.varAddr "sender") (.sub (.var "senderBalance") (.var "amount"))
                (.mstore 1 (.varAddr "to") (.var "newRecipientBalance") .stop)))))))

/-- AST for `balanceOf(addr)`: return mapping slot1[addr] -/
def balanceOfAST : Stmt :=
  .bindUint "x" (.mapping 1 (.varAddr "addr"))
    (.ret (.var "x"))

/-- AST for `getTotalSupply()`: return sload slot2 -/
def getTotalSupplyAST : Stmt :=
  .bindUint "x" (.storage 2)
    (.ret (.var "x"))

/-- AST for `getOwner()`: return sloadAddr slot0 -/
def getOwnerAST : Stmt :=
  .bindAddr "x" (.storageAddr 0)
    (.retAddr (.varAddr "x"))

/-! ## Equivalence Proofs -/

private theorem inline_onlyOwner :
    ∀ (f : Unit → Contract α),
    Verity.bind Verity.Examples.SimpleToken.onlyOwner f
    = Verity.bind msgSender fun sender =>
        Verity.bind (getStorageAddr ⟨0⟩) fun currentOwner =>
          Verity.bind (Verity.require (sender == currentOwner) "Caller is not the owner") f := by
  intro f
  simp only [Verity.Examples.SimpleToken.onlyOwner,
    Verity.Examples.SimpleToken.isOwner,
    Verity.Examples.SimpleToken.owner,
    Bind.bind, Pure.pure, Contract.bind_assoc, Contract.bind_pure_left]

/-- `constructor` AST denotes to the EDSL `constructor` function. -/
theorem constructor_equiv (initialOwner : Address) :
    denoteUnit emptyEnv (fun s => if s == "initialOwner" then initialOwner else "") constructorAST
    = constructor initialOwner := by
  rfl

/-- `mint` AST denotes to the EDSL `mint` function. -/
theorem mint_equiv (to : Address) (amount : Uint256) :
    denoteUnit
      (fun s => if s == "amount" then amount else 0)
      (fun s => if s == "to" then to else "")
      mintAST
    = mint to amount := by
  simp only [mint, Bind.bind, inline_onlyOwner,
    Verity.Examples.SimpleToken.balances, Verity.Examples.SimpleToken.totalSupply]; rfl

/-- `transfer` AST denotes to the EDSL `transfer` function. -/
theorem transfer_equiv (to : Address) (amount : Uint256) :
    denoteUnit
      (fun s => if s == "amount" then amount else 0)
      (fun s => if s == "to" then to else "")
      transferAST
    = transfer to amount := by
  rfl

/-- `balanceOf` AST denotes to the EDSL `balanceOf` function. -/
theorem balanceOf_equiv (addr : Address) :
    denoteUint emptyEnv (fun s => if s == "addr" then addr else "") balanceOfAST
    = balanceOf addr := by
  rfl

/-- `getTotalSupply` AST denotes to the EDSL `getTotalSupply` function. -/
theorem getTotalSupply_equiv :
    denoteUint emptyEnv emptyEnvAddr getTotalSupplyAST = getTotalSupply := by
  rfl

/-- `getOwner` AST denotes to the EDSL `getOwner` function. -/
theorem getOwner_equiv :
    denoteAddress emptyEnv emptyEnvAddr getOwnerAST = getOwner := by
  rfl

end Verity.AST.SimpleToken
