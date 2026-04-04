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
import Verity.Intent.DSL

namespace Contracts.ERC20

open Verity.Intent
open Verity.Intent.DSL
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
intent_spec "ERC20" where
  const MAX_UINT256 := maxUint256

  predicate isMaxUint(v : uint256) :=
    v == MAX_UINT256

  intent transferIntent(to : address, amount : uint256) where
    if isMaxUint(amount)
    then { emit "Send all tokens to {to}" [to : address] }
    else { emit "Send {amount} tokens to {to}" [amount : tokenAmount 18, to : address] }

  intent approveIntent(spender : address, amount : uint256) where
    if isMaxUint(amount)
    then { emit "Approve {spender} to spend unlimited tokens" [spender : address] }
    else { emit "Approve {spender} to spend {amount} tokens" [spender : address, amount : tokenAmount 18] }

  intent transferFromIntent(fromAddr : address, to : address, amount : uint256) where
    if isMaxUint(amount)
    then { emit "Transfer all tokens from {fromAddr} to {to}" [fromAddr : address, to : address] }
    else { emit "Transfer {amount} tokens from {fromAddr} to {to}" [amount : tokenAmount 18, fromAddr : address, to : address] }

  bind "transfer" => transferIntent
  bind "approve" => approveIntent
  bind "transferFrom" => transferFromIntent

end Contracts.ERC20
