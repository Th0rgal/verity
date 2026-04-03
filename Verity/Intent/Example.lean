/-
  Verity.Intent.Example: Example IntentSpec for an ERC-20 transfer function.

  Demonstrates the provable intent DSL by defining:
    - A `isMaxUint` predicate helper
    - A `transfer` intent that emits different templates based on whether
      the amount equals MAX_UINT256 ("all tokens" vs specific amount)
    - An `approve` intent (simpler, unconditional)

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

/-- Example: ERC-20 IntentSpec with transfer and approve. -/
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
    }
  ]

  bindings := [
    { functionName := "transfer", intentFn := "transferIntent" },
    { functionName := "approve",  intentFn := "approveIntent"  }
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

/-! ## Validation Smoke Tests

Build a mock CompilationModel matching the ERC-20 intent spec and verify validation.
-/

open Compiler.CompilationModel (CompilationModel FunctionSpec Param)

/-- Mock ERC-20 CompilationModel with transfer and approve functions. -/
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

end Verity.Intent.Example
