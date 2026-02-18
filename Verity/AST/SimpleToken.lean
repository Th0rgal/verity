/-
  Verity.AST.SimpleToken: Unified AST for SimpleToken

  The most complex contract: ownership + balances mapping + total supply +
  safeAdd overflow protection + if/then/else transfer logic. Demonstrates
  `bind_assoc` for owner-gated mint and `ite` for self-transfer.
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
    setStorageAddr 0 initialOwner
    setStorage 2 0 -/
def constructorAST : Stmt :=
  .sstoreAddr 0 (.varAddr "initialOwner")
    (.sstore 2 (.lit 0) .stop)

/-- AST for `mint(to, amount)` (inlined onlyOwner/isOwner):
    let sender ← msgSender
    let currentOwner ← getStorageAddr 0
    require (sender == currentOwner) "Caller is not the owner"
    let currentBalance ← getMapping 1 to
    let newBalance ← requireSomeUint (safeAdd currentBalance amount) "Balance overflow"
    let currentSupply ← getStorage 2
    let newSupply ← requireSomeUint (safeAdd currentSupply amount) "Supply overflow"
    setMapping 1 to newBalance
    setStorage 2 newSupply -/
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
    let sender ← msgSender
    let senderBalance ← getMapping 1 sender
    require (senderBalance >= amount) "Insufficient balance"
    if sender == to then stop
    else
      let recipientBalance ← getMapping 1 to
      let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance amount) "Recipient balance overflow"
      setMapping 1 sender (sub senderBalance amount)
      setMapping 1 to newRecipientBalance -/
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

/-- AST for `balanceOf(addr)`: getMapping 1 addr -/
def balanceOfAST : Stmt :=
  .bindUint "x" (.mapping 1 (.varAddr "addr"))
    (.ret (.var "x"))

/-- AST for `getTotalSupply()`: getStorage 2 -/
def getTotalSupplyAST : Stmt :=
  .bindUint "x" (.storage 2)
    (.ret (.var "x"))

/-- AST for `getOwner()`: getStorageAddr 0 -/
def getOwnerAST : Stmt :=
  .bindAddr "x" (.storageAddr 0)
    (.retAddr (.varAddr "x"))

/-!
## Equivalence Proofs
-/

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
    Bind.bind, Pure.pure, bind_assoc, bind_pure]

theorem constructor_equiv (initialOwner : Address) :
    denoteUnit emptyEnv (fun s => if s == "initialOwner" then initialOwner else "") constructorAST
    = constructor initialOwner := by
  rfl

theorem mint_equiv (to : Address) (amount : Uint256) :
    denoteUnit
      (fun s => if s == "amount" then amount else 0)
      (fun s => if s == "to" then to else "")
      mintAST
    = mint to amount := by
  simp only [mint, Bind.bind, inline_onlyOwner,
    Verity.Examples.SimpleToken.balances, Verity.Examples.SimpleToken.totalSupply]; rfl

theorem transfer_equiv (to : Address) (amount : Uint256) :
    denoteUnit
      (fun s => if s == "amount" then amount else 0)
      (fun s => if s == "to" then to else "")
      transferAST
    = transfer to amount := by
  rfl

theorem balanceOf_equiv (addr : Address) :
    denoteUint emptyEnv (fun s => if s == "addr" then addr else "") balanceOfAST
    = balanceOf addr := by
  rfl

theorem getTotalSupply_equiv :
    denoteUint emptyEnv emptyEnvAddr getTotalSupplyAST = getTotalSupply := by
  rfl

theorem getOwner_equiv :
    denoteAddress emptyEnv emptyEnvAddr getOwnerAST = getOwner := by
  rfl

end Verity.AST.SimpleToken
