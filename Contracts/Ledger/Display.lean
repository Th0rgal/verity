/-
  Contracts.Ledger.Display: Intent specification for the Ledger contract.

  Defines `Contracts.Ledger.intentSpec` — the provable intent DSL mapping
  for the Ledger contract's user-facing state-changing functions:
    - deposit(amount)
    - withdraw(amount)
    - transfer(to, amount)

  This constant is auto-discovered by the compiler when `--circom-output`
  is passed, enabling Circom circuit generation for each binding.

  See `Contracts/ERC20/Display.lean` for the ERC-20 version.
-/
import Verity.Intent.DSL

namespace Contracts.Ledger

open Verity.Intent
open Verity.Intent.DSL
open Compiler.CompilationModel (ParamType)

/-- MAX_UINT256 = 2^256 - 1.
    Used in circuits as two 128-bit limbs: both equal to 2^128 - 1. -/
private def maxUint256 : Int := (2 ^ 256 : Nat) - 1

/-- Intent specification for the Ledger contract.

    Covers three functions:
    - `deposit`: unconditional — always shows amount
    - `withdraw`: unconditional — always shows amount
    - `transfer`: conditional on amount == MAX_UINT256

    Read-only function (`getBalance`) is not covered. -/
intent_spec "Ledger" where
  const MAX_UINT256 := maxUint256

  predicate isMaxUint(v : uint256) :=
    v == MAX_UINT256

  intent depositIntent(amount : uint256) where
    emit "Deposit {amount} tokens" [amount : tokenAmount 18]

  intent withdrawIntent(amount : uint256) where
    emit "Withdraw {amount} tokens" [amount : tokenAmount 18]

  intent transferIntent(to : address, amount : uint256) where
    if isMaxUint(amount)
    then { emit "Send all tokens to {to}" [to : address] }
    else { emit "Send {amount} tokens to {to}" [amount : tokenAmount 18, to : address] }

  bind "deposit" => depositIntent
  bind "withdraw" => withdrawIntent
  bind "transfer" => transferIntent

end Contracts.Ledger
