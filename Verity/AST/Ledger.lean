/-
  Verity.AST.Ledger: Unified AST for Ledger

  Storage layout:  slot 0 = balances (Address → Uint256)
-/

import Verity.Denote
import Verity.Examples.Ledger

namespace Verity.AST.Ledger

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples.Ledger (deposit withdraw transfer getBalance)

/-- AST for `deposit(amount)`:
    sender ← msgSender
    bal ← mapping slot0[sender]
    mstore slot0[sender] (bal + amount) -/
def depositAST : Stmt :=
  .bindAddr "sender" .sender
    (.bindUint "currentBalance" (.mapping 0 (.varAddr "sender"))
      (.mstore 0 (.varAddr "sender") (.add (.var "currentBalance") (.var "amount")) .stop))

/-- AST for `withdraw(amount)`:
    sender ← msgSender
    bal ← mapping slot0[sender]
    require (bal >= amount)
    mstore slot0[sender] (bal - amount) -/
def withdrawAST : Stmt :=
  .bindAddr "sender" .sender
    (.bindUint "currentBalance" (.mapping 0 (.varAddr "sender"))
      (.require (.ge (.var "currentBalance") (.var "amount")) "Insufficient balance"
        (.mstore 0 (.varAddr "sender") (.sub (.var "currentBalance") (.var "amount")) .stop)))

/-- AST for `getBalance(addr)`: return mapping slot0[addr] -/
def getBalanceAST : Stmt :=
  .bindUint "x" (.mapping 0 (.varAddr "addr"))
    (.ret (.var "x"))

/-- AST for `transfer(to, amount)`:
    sender ← msgSender
    senderBal ← mapping slot0[sender]
    require (senderBal >= amount)
    if sender == to then stop
    else
      recipientBal ← mapping slot0[to]
      newRecipientBal ← requireSomeUint (safeAdd recipientBal amount) "..."
      mstore slot0[sender] (senderBal - amount)
      mstore slot0[to] newRecipientBal -/
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

/-! ## Equivalence Proofs -/

/-- `deposit` AST denotes to the EDSL `deposit` function. -/
theorem deposit_equiv (amount : Uint256) :
    denoteUnit (fun s => if s == "amount" then amount else 0) emptyEnvAddr depositAST
    = deposit amount := by
  rfl

/-- `withdraw` AST denotes to the EDSL `withdraw` function. -/
theorem withdraw_equiv (amount : Uint256) :
    denoteUnit (fun s => if s == "amount" then amount else 0) emptyEnvAddr withdrawAST
    = withdraw amount := by
  rfl

/-- `getBalance` AST denotes to the EDSL `getBalance` function. -/
theorem getBalance_equiv (addr : Address) :
    denoteUint emptyEnv (fun s => if s == "addr" then addr else 0) getBalanceAST
    = getBalance addr := by
  rfl

/-- `transfer` AST denotes to the EDSL `transfer` function. -/
theorem transfer_equiv (to : Address) (amount : Uint256) :
    denoteUnit
      (fun s => if s == "amount" then amount else 0)
      (fun s => if s == "to" then to else 0)
      transferAST
    = transfer to amount := by
  rfl

end Verity.AST.Ledger
