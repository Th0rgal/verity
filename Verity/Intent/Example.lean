/-
  Verity.Intent.Example: Example IntentSpec for an ERC-20 contract.

  Demonstrates the provable intent DSL by defining:
    - A `isMaxUint` predicate helper
    - A `transfer` intent (2 params: address + uint256, conditional)
    - An `approve` intent (2 params: address + uint256, conditional)
    - A `transferFrom` intent (3 params: address + address + uint256, conditional)

  These examples can be used to:
    1. Test the reference evaluator
    2. Generate Circom circuits
    3. Validate the end-to-end pipeline
-/
import Verity.Intent.Types
import Verity.Intent.Eval
import Verity.Intent.Validate
import Compiler.CompilationModel.Types

namespace Verity.Intent.Example

open Verity.Intent
open Compiler.CompilationModel (ParamType)

/-! ## Constants -/

/-- MAX_UINT256 = 2^256 - 1.
    In circuits, we check this as two 128-bit limbs both equal to 2^128 - 1. -/
def maxUint256 : Int :=
  (2 ^ 256 : Nat) - 1

/-! ## ERC-20 Transfer Intent -/

/-- Example: ERC-20 IntentSpec with transfer, approve, and transferFrom. -/
def erc20IntentSpec : IntentSpec := {
  contractName := "ERC20"

  constants := [
    { name := "MAX_UINT256", value := .intLit maxUint256 }
  ]

  fns := [
    -- Predicate: isMaxUint(v: uint256) -> Bool := v == MAX_UINT256
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
          -- then: "Send all tokens to {to}"
          [.emit { text := "Send all tokens to {to}",
                   holes := [{ param := "to", format := .address }] }]
          -- else: "Send {amount} tokens to {to}"
          [.emit { text := "Send {amount} tokens to {to}",
                   holes := [{ param := "amount",
                               format := .tokenAmount 18 (some "TOKEN") },
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
                               format := .tokenAmount 18 (some "TOKEN") }] }]
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
                               format := .tokenAmount 18 (some "TOKEN") },
                             { param := "fromAddr", format := .address },
                             { param := "to", format := .address }] }]
      ]
    }
  ]

  bindings := [
    { functionName := "transfer",     intentFn := "transferIntent" },
    { functionName := "approve",      intentFn := "approveIntent"  },
    { functionName := "transferFrom", intentFn := "transferFromIntent" }
  ]
}

/-! ## Helper to get a binding safely -/

def getBinding (spec : IntentSpec) (idx : Nat) : Option IntentBinding :=
  spec.bindings[idx]?

/-! ## Evaluator Smoke Tests

Run `#eval` to verify the evaluator produces the expected output.
-/

-- Test: transfer with a specific amount should emit "Send {amount} tokens to {to}".
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 0 with
  | some binding =>
    let params : List (String × Value) := [
      ("to", .addr "0xdead"),
      ("amount", .int 1000)
    ]
    let result := evalIntent spec binding params
    match result with
    | some templates =>
      IO.println s!"Transfer (amount=1000): {templates.length} template(s)"
      for t in templates do
        IO.println s!"  text: \"{t.text}\""
        IO.println s!"  holes: {t.holes.length}"
    | none => IO.println "ERROR: evaluation failed"
  | none => IO.println "ERROR: binding not found"

-- Test: transfer with MAX_UINT256 should emit "Send all tokens to {to}".
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 0 with
  | some binding =>
    let params : List (String × Value) := [
      ("to", .addr "0xdead"),
      ("amount", .int maxUint256)
    ]
    let result := evalIntent spec binding params
    match result with
    | some templates =>
      IO.println s!"Transfer (amount=MAX): {templates.length} template(s)"
      for t in templates do
        IO.println s!"  text: \"{t.text}\""
    | none => IO.println "ERROR: evaluation failed"
  | none => IO.println "ERROR: binding not found"

-- Test: approve with a specific amount.
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 1 with
  | some binding =>
    let params : List (String × Value) := [
      ("spender", .addr "0xbeef"),
      ("amount", .int 500)
    ]
    let result := evalIntent spec binding params
    match result with
    | some templates =>
      IO.println s!"Approve (amount=500): {templates.length} template(s)"
      for t in templates do
        IO.println s!"  text: \"{t.text}\""
    | none => IO.println "ERROR: evaluation failed"
  | none => IO.println "ERROR: binding not found"

-- Test: transferFrom with a specific amount (3-parameter function).
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 2 with
  | some binding =>
    let params : List (String × Value) := [
      ("fromAddr", .addr "0xcafe"),
      ("to", .addr "0xdead"),
      ("amount", .int 2000)
    ]
    let result := evalIntent spec binding params
    match result with
    | some templates =>
      IO.println s!"TransferFrom (amount=2000): {templates.length} template(s)"
      for t in templates do
        IO.println s!"  text: \"{t.text}\""
        IO.println s!"  holes: {t.holes.length}"
    | none => IO.println "ERROR: evaluation failed"
  | none => IO.println "ERROR: binding not found"

-- Test: transferFrom with MAX_UINT256 should emit "Transfer all tokens from {fromAddr} to {to}".
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 2 with
  | some binding =>
    let params : List (String × Value) := [
      ("fromAddr", .addr "0xcafe"),
      ("to", .addr "0xdead"),
      ("amount", .int maxUint256)
    ]
    let result := evalIntent spec binding params
    match result with
    | some templates =>
      IO.println s!"TransferFrom (amount=MAX): {templates.length} template(s)"
      for t in templates do
        IO.println s!"  text: \"{t.text}\""
    | none => IO.println "ERROR: evaluation failed"
  | none => IO.println "ERROR: binding not found"

/-! ## Validation Smoke Tests

Build a mock CompilationModel matching the ERC-20 intent spec and verify validation.
-/

open Compiler.CompilationModel (CompilationModel FunctionSpec Param)

/-- Mock ERC-20 CompilationModel with transfer, approve, and transferFrom. -/
private def mockErc20Model : CompilationModel := {
  name := "ERC20"
  fields := []
  constructor := none
  functions := [
    { name := "transfer"
      params := [⟨"to", .address⟩, ⟨"amount", .uint256⟩]
      returnType := none
      body := [] },
    { name := "approve"
      params := [⟨"spender", .address⟩, ⟨"amount", .uint256⟩]
      returnType := none
      body := [] },
    { name := "transferFrom"
      params := [⟨"fromAddr", .address⟩, ⟨"to", .address⟩, ⟨"amount", .uint256⟩]
      returnType := none
      body := [] }
  ]
}

-- Test: valid intent spec passes validation.
#eval do
  let errors := Validate.validate erc20IntentSpec mockErc20Model
  if errors.isEmpty then
    IO.println "✓ ERC-20 intent spec validates against mock CompilationModel"
  else
    for e in errors do
      IO.println s!"✗ {e}"
    throw (IO.userError "validation failed")

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

-- Test: mismatched contract name is caught.
#eval do
  let badSpec := { erc20IntentSpec with contractName := "BadName" }
  let errors := Validate.validate badSpec mockErc20Model
  match errors.find? (fun e => hasSubstr e "Contract name mismatch") with
  | some _ => IO.println "✓ Mismatched contract name detected"
  | none => throw (IO.userError "expected contract name mismatch error")

-- Test: binding to missing ABI function is caught.
#eval do
  let badSpec := { erc20IntentSpec with
    bindings := [{ functionName := "nonexistent", intentFn := "transferIntent" }] }
  let errors := Validate.validate badSpec mockErc20Model
  match errors.find? (fun e => hasSubstr e "no matching function") with
  | some _ => IO.println "✓ Missing ABI function detected"
  | none => throw (IO.userError "expected missing function error")

-- Test: binding to missing intent function is caught.
#eval do
  let badSpec := { erc20IntentSpec with
    bindings := [{ functionName := "transfer", intentFn := "missingFn" }] }
  let errors := Validate.validate badSpec mockErc20Model
  match errors.find? (fun e => hasSubstr e "intent function 'missingFn' not found") with
  | some _ => IO.println "✓ Missing intent function detected"
  | none => throw (IO.userError "expected missing intent function error")

-- Test: param type mismatch is caught.
#eval do
  let badModel : CompilationModel := { mockErc20Model with
    functions := [
      { name := "transfer"
        params := [⟨"to", .bool⟩, ⟨"amount", .uint256⟩]  -- wrong type for 'to'
        returnType := none
        body := [] },
      { name := "approve"
        params := [⟨"spender", .address⟩, ⟨"amount", .uint256⟩]
        returnType := none
        body := [] }
    ] }
  let errors := Validate.validate erc20IntentSpec badModel
  match errors.find? (fun e => hasSubstr e "type mismatch") with
  | some _ => IO.println "✓ Param type mismatch detected"
  | none => throw (IO.userError "expected type mismatch error")

-- Test: undefined constant reference is caught.
#eval do
  let badSpec : IntentSpec := { erc20IntentSpec with
    constants := []  -- remove MAX_UINT256 constant
  }
  let errors := Validate.validate badSpec mockErc20Model
  match errors.find? (fun e => hasSubstr e "undefined name 'MAX_UINT256'") with
  | some _ => IO.println "✓ Undefined constant reference detected"
  | none => throw (IO.userError "expected undefined name error")

-- Test: Poseidon arity overflow is caught (too many params for circomlib).
#eval do
  -- Create a spec with 8 uint256 params = 16 signals + 1 selector = 17 > Poseidon max of 16
  let manyParamFn : FnDecl := {
    name := "bigIntent"
    params := (List.range 8).map (fun i => (s!"p{i}", ParamType.uint256))
    returnKind := .void
    body := [.emit { text := "test", holes := [] }]
  }
  let bigSpec : IntentSpec := {
    contractName := "ERC20"
    fns := [manyParamFn]
    bindings := [{ functionName := "transfer", intentFn := "bigIntent" }]
  }
  let errors := Validate.validate bigSpec mockErc20Model
  match errors.find? (fun e => hasSubstr e "Poseidon") with
  | some _ => IO.println "✓ Poseidon arity overflow detected"
  | none => throw (IO.userError "expected Poseidon arity error")

/-! ## Circuit Output Cross-Validation Tests

Verify that `evalIntentCircuitOutput` computes the same `(templateId, holeValues)`
that the Circom circuit commits to. These values must match what the JavaScript
test (`test_circom_e2e.sh`) hard-codes as Poseidon inputs.
-/

private def max128 : Nat := (2 ^ 128) - 1

-- Test: transfer(to=0xdead, amount=1000) → templateIdx=1 (else branch), holes=[1000, 0, 57005]
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 0 with
  | some binding =>
    let params : List (String × Value) := [
      ("to", .addr "0xdead"),
      ("amount", .int 1000)
    ]
    match evalIntentCircuitOutput spec binding params with
    | some co =>
      unless co.templateIdx == 1 do
        throw (IO.userError s!"expected templateIdx=1, got {co.templateIdx}")
      unless co.holeValues == [1000, 0, 57005] do
        throw (IO.userError s!"expected holeValues=[1000, 0, 57005], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: transfer(1000) → templateIdx={co.templateIdx}, holes={repr co.holeValues}"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

-- Test: transfer(to=0xdead, amount=MAX) → templateIdx=0 (then branch), holes=[max128, max128, 57005]
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 0 with
  | some binding =>
    let params : List (String × Value) := [
      ("to", .addr "0xdead"),
      ("amount", .int maxUint256)
    ]
    match evalIntentCircuitOutput spec binding params with
    | some co =>
      unless co.templateIdx == 0 do
        throw (IO.userError s!"expected templateIdx=0, got {co.templateIdx}")
      unless co.holeValues == [max128, max128, 57005] do
        throw (IO.userError s!"expected holeValues=[max128, max128, 57005], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: transfer(MAX) → templateIdx={co.templateIdx}, holes match"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

-- Test: approve(spender=0xbeef, amount=500) → templateIdx=1 (else branch), holes=[48879, 500, 0]
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 1 with
  | some binding =>
    let params : List (String × Value) := [
      ("spender", .addr "0xbeef"),
      ("amount", .int 500)
    ]
    match evalIntentCircuitOutput spec binding params with
    | some co =>
      unless co.templateIdx == 1 do
        throw (IO.userError s!"expected templateIdx=1, got {co.templateIdx}")
      unless co.holeValues == [48879, 500, 0] do
        throw (IO.userError s!"expected holeValues=[48879, 500, 0], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: approve(500) → templateIdx={co.templateIdx}, holes={repr co.holeValues}"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

-- Test: transferFrom(fromAddr=0xcafe, to=0xdead, amount=2000)
--   → templateIdx=1 (else branch), holes=[2000, 0, 51966, 57005]
--   Hole order: dedup of [fromAddr, to] ++ [amount, fromAddr, to] = [amount, fromAddr, to]
--   Values: amount_lo=2000, amount_hi=0, fromAddr=0xcafe=51966, to=0xdead=57005
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 2 with
  | some binding =>
    let params : List (String × Value) := [
      ("fromAddr", .addr "0xcafe"),
      ("to", .addr "0xdead"),
      ("amount", .int 2000)
    ]
    match evalIntentCircuitOutput spec binding params with
    | some co =>
      unless co.templateIdx == 1 do
        throw (IO.userError s!"expected templateIdx=1, got {co.templateIdx}")
      unless co.holeValues == [2000, 0, 51966, 57005] do
        throw (IO.userError s!"expected holeValues=[2000, 0, 51966, 57005], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: transferFrom(2000) → templateIdx={co.templateIdx}, holes={repr co.holeValues}"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

-- Test: transferFrom(fromAddr=0xcafe, to=0xdead, amount=MAX)
--   → templateIdx=0 (then branch), holes=[max128, max128, 51966, 57005]
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 2 with
  | some binding =>
    let params : List (String × Value) := [
      ("fromAddr", .addr "0xcafe"),
      ("to", .addr "0xdead"),
      ("amount", .int maxUint256)
    ]
    match evalIntentCircuitOutput spec binding params with
    | some co =>
      unless co.templateIdx == 0 do
        throw (IO.userError s!"expected templateIdx=0, got {co.templateIdx}")
      unless co.holeValues == [max128, max128, 51966, 57005] do
        throw (IO.userError s!"expected holeValues=[max128, max128, 51966, 57005], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: transferFrom(MAX) → templateIdx={co.templateIdx}, holes match"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

end Verity.Intent.Example
