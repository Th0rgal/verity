/-
  Contracts.ERC20.Display: Intent specification for the ERC-20 contract.

  Defines `Contracts.ERC20.intentSpec` — the provable intent DSL mapping
  for the ERC-20 contract's user-facing state-changing functions:
    - transfer(to, amount)
    - approve(spender, amount)
    - transferFrom(fromAddr, to, amount)

  This constant is auto-discovered by the compiler when `--circom-output`
  or `--erc7730-output` is passed, enabling circuit and clear-signing
  JSON generation for each binding.

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

  intent transfer(to : address, amount : uint256) where
    when isMaxUint(amount) =>
      emit "Send all tokens to {to:address}"
    otherwise =>
      emit "Send {amount:tokenAmount 18} tokens to {to:address}"

  intent approve(spender : address, amount : uint256) where
    when isMaxUint(amount) =>
      emit "Approve {spender:address} to spend unlimited tokens"
    otherwise =>
      emit "Approve {spender:address} to spend {amount:tokenAmount 18} tokens"

  intent transferFrom(fromAddr : address, to : address, amount : uint256) where
    when isMaxUint(amount) =>
      emit "Transfer all tokens from {fromAddr:address} to {to:address}"
    otherwise =>
      emit "Transfer {amount:tokenAmount 18} tokens from {fromAddr:address} to {to:address}"

end Contracts.ERC20
