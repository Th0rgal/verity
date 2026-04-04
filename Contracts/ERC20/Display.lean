/-
  Contracts.ERC20.Display: Intent specification for the ERC-20 contract.

  Defines `Contracts.ERC20.intentSpec` — the provable intent DSL mapping
  for the ERC-20 contract's user-facing state-changing functions:
    - transfer(to, amount)
    - approve(spender, amount)
    - transferFrom(fromAddr, to, amount)

  This constant is auto-discovered by the compiler when `--circom-output`
  is passed, enabling Circom circuit generation for each binding.

  See `Verity/Intent/Example.lean` for the standalone version with
  evaluator smoke tests and circuit cross-validation.
-/
import Verity.Intent.Types

namespace Contracts.ERC20

open Verity.Intent
open Compiler.CompilationModel (ParamType)

/-- MAX_UINT256 = 2^256 - 1.
    Used in circuits as two 128-bit limbs: both equal to 2^128 - 1. -/
private def maxUint256 : Int := (2 ^ 256 : Nat) - 1

/-- Intent specification for the ERC-20 contract.

    Covers three functions:
    - `transfer`: conditional on amount == MAX_UINT256
    - `approve`: conditional on amount == MAX_UINT256
    - `transferFrom`: conditional on amount == MAX_UINT256

    Read-only functions (`balanceOf`, `allowanceOf`, `totalSupply`, `owner`)
    and owner-only functions (`mint`) are not covered — they either have no
    calldata display value or are privileged operations. -/
def intentSpec : IntentSpec := {
  contractName := "ERC20"

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

    -- Intent: transfer(to: address, amount: uint256)
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
    },

    -- Intent: approve(spender: address, amount: uint256)
    { name := "approveIntent"
      params := [("spender", .address), ("amount", .uint256)]
      returnKind := .void
      body := [
        .ite (.call "isMaxUint" [.param "amount"])
          [.emit { text := "Approve {spender} to spend unlimited tokens",
                   holes := [{ param := "spender", format := .address }] }]
          [.emit { text := "Approve {spender} to spend {amount} tokens",
                   holes := [{ param := "spender", format := .address },
                             { param := "amount",
                               format := .tokenAmount 18 }] }]
      ]
    },

    -- Intent: transferFrom(fromAddr: address, to: address, amount: uint256)
    { name := "transferFromIntent"
      params := [("fromAddr", .address), ("to", .address), ("amount", .uint256)]
      returnKind := .void
      body := [
        .ite (.call "isMaxUint" [.param "amount"])
          [.emit { text := "Transfer all tokens from {fromAddr} to {to}",
                   holes := [{ param := "fromAddr", format := .address },
                             { param := "to", format := .address }] }]
          [.emit { text := "Transfer {amount} tokens from {fromAddr} to {to}",
                   holes := [{ param := "amount",
                               format := .tokenAmount 18 },
                             { param := "fromAddr", format := .address },
                             { param := "to", format := .address }] }]
      ]
    }
  ]

  bindings := [
    { functionName := "transfer",     intentFn := "transferIntent" },
    { functionName := "approve",      intentFn := "approveIntent" },
    { functionName := "transferFrom", intentFn := "transferFromIntent" }
  ]
}

end Contracts.ERC20
