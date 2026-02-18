/-
  Verity.AST.Ledger: Unified AST for Ledger

  Demonstrates mappings (Address → Uint256), `msgSender`, `require`,
  and `if/then/else` through the unified AST with `rfl` equivalence proofs.
-/

import Verity.Denote
import Verity.Examples.Ledger

namespace Verity.AST.Ledger

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples.Ledger (deposit withdraw transfer getBalance)

/-- AST for `deposit(amount)`:
    let sender ← msgSender
    let currentBalance ← getMapping ⟨0⟩ sender
    setMapping ⟨0⟩ sender (add currentBalance amount) -/
def depositAST : Stmt :=
  .bindAddr "sender" .sender
    (.bindUint "currentBalance" (.mapping 0 (.varAddr "sender"))
      (.mstore 0 (.varAddr "sender") (.add (.var "currentBalance") (.var "amount")) .stop))

/-- AST for `withdraw(amount)`:
    let sender ← msgSender
    let currentBalance ← getMapping ⟨0⟩ sender
    require (currentBalance >= amount) "Insufficient balance"
    setMapping ⟨0⟩ sender (sub currentBalance amount) -/
def withdrawAST : Stmt :=
  .bindAddr "sender" .sender
    (.bindUint "currentBalance" (.mapping 0 (.varAddr "sender"))
      (.require (.ge (.var "currentBalance") (.var "amount")) "Insufficient balance"
        (.mstore 0 (.varAddr "sender") (.sub (.var "currentBalance") (.var "amount")) .stop)))

/-- AST for `getBalance(addr)`:
    getMapping ⟨0⟩ addr -/
def getBalanceAST : Stmt :=
  .bindUint "x" (.mapping 0 (.varAddr "addr"))
    (.ret (.var "x"))

/-- AST for `transfer(to, amount)`:
    let sender ← msgSender
    let senderBalance ← getMapping ⟨0⟩ sender
    require (senderBalance >= amount) "Insufficient balance"
    if sender == to then pure ()
    else
      let recipientBalance ← getMapping ⟨0⟩ to
      let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance amount) "Recipient balance overflow"
      setMapping ⟨0⟩ sender (sub senderBalance amount)
      setMapping ⟨0⟩ to newRecipientBalance -/
def transferAST : Stmt :=
  .bindAddr "sender" .sender
    (.bindUint "senderBalance" (.mapping 0 (.varAddr "sender"))
      (.require (.ge (.var "senderBalance") (.var "amount")) "Insufficient balance"
        (.ite (.eqAddr (.varAddr "sender") (.varAddr "to"))
          .stop
          (.bindUint "recipientBalance" (.mapping 0 (.varAddr "to"))
            (.requireSome "newRecipientBalance"
              (.safeAdd (.var "recipientBalance") (.var "amount"))
              "Recipient balance overflow"
              (.mstore 0 (.varAddr "sender") (.sub (.var "senderBalance") (.var "amount"))
                (.mstore 0 (.varAddr "to") (.var "newRecipientBalance") .stop)))))))

/-!
## Equivalence Proofs
-/

theorem deposit_equiv (amount : Uint256) :
    denoteUnit (fun s => if s == "amount" then amount else 0) emptyEnvAddr depositAST
    = deposit amount := by
  rfl

theorem withdraw_equiv (amount : Uint256) :
    denoteUnit (fun s => if s == "amount" then amount else 0) emptyEnvAddr withdrawAST
    = withdraw amount := by
  rfl

theorem getBalance_equiv (addr : Address) :
    denoteUint emptyEnv (fun s => if s == "addr" then addr else "") getBalanceAST
    = getBalance addr := by
  rfl

theorem transfer_equiv (to : Address) (amount : Uint256) :
    denoteUnit
      (fun s => if s == "amount" then amount else 0)
      (fun s => if s == "to" then to else "")
      transferAST
    = transfer to amount := by
  rfl

end Verity.AST.Ledger
