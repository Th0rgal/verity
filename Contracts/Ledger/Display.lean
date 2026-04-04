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
import Verity.Intent.Types

namespace Contracts.Ledger

open Verity.Intent
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
def intentSpec : IntentSpec := {
  contractName := "Ledger"

  constants := [
    { name := "MAX_UINT256", value := .intLit maxUint256 }
  ]

  fns := [
    -- Predicate: isMaxUint(v: uint256) → Bool := v == MAX_UINT256
    { name := "isMaxUint"
      params := [("v", .uint256)]
      returnKind := .bool
      expr := some (.eq (.param "v") (.param "MAX_UINT256"))
    },

    -- Intent: deposit(amount: uint256)
    -- Single template — no conditional needed for deposit
    { name := "depositIntent"
      params := [("amount", .uint256)]
      returnKind := .void
      body := [
        .emit { text := "Deposit {amount} tokens",
                holes := [{ param := "amount",
                            format := .tokenAmount 18 }] }
      ]
    },

    -- Intent: withdraw(amount: uint256)
    -- Single template — no conditional needed for withdraw
    { name := "withdrawIntent"
      params := [("amount", .uint256)]
      returnKind := .void
      body := [
        .emit { text := "Withdraw {amount} tokens",
                holes := [{ param := "amount",
                            format := .tokenAmount 18 }] }
      ]
    },

    -- Intent: transfer(to: address, amount: uint256)
    -- Conditional: "Send all tokens" vs "Send {amount} tokens"
    { name := "transferIntent"
      params := [("to", .address), ("amount", .uint256)]
      returnKind := .void
      body := [
        .ite (.call "isMaxUint" [.param "amount"])
          [.emit { text := "Send all tokens to {to}",
                   holes := [{ param := "to", format := .address }] }]
          [.emit { text := "Send {amount} tokens to {to}",
                   holes := [{ param := "amount",
                               format := .tokenAmount 18 },
                             { param := "to", format := .address }] }]
      ]
    }
  ]

  bindings := [
    { functionName := "deposit",  intentFn := "depositIntent" },
    { functionName := "withdraw", intentFn := "withdrawIntent" },
    { functionName := "transfer", intentFn := "transferIntent" }
  ]
}

end Contracts.Ledger
