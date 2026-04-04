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
import Verity.Intent.DSL
import Compiler.CompilationModel.Types
import Contracts.ERC721.Display
import Contracts.Ledger.Display

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
    { name := "transfer"
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
    { name := "approve"
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
    { name := "transferFrom"
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
    { functionName := "transfer",     intentFn := "transfer" },
    { functionName := "approve",      intentFn := "approve"  },
    { functionName := "transferFrom", intentFn := "transferFrom" }
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
  let parts := haystack.splitOn needle
  parts.length > 1

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
    bindings := [{ functionName := "nonexistent", intentFn := "transfer" }] }
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

-- Test: transfer(to=0xdead, amount=1000) → templateIdx=1 (else branch), holes=[57005, 1000, 0]
-- Hole order: dedup first-occurrence of [to] ++ [amount, to] = [to, amount] → [to, amount_lo, amount_hi]
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
      unless co.holeValues == [57005, 1000, 0] do
        throw (IO.userError s!"expected holeValues=[57005, 1000, 0], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: transfer(1000) → templateIdx={co.templateIdx}, holes={repr co.holeValues}"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

-- Test: transfer(to=0xdead, amount=MAX) → templateIdx=0 (then branch), holes=[57005, max128, max128]
-- Hole order: [to, amount_lo, amount_hi]
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
      unless co.holeValues == [57005, max128, max128] do
        throw (IO.userError s!"expected holeValues=[57005, max128, max128], got {repr co.holeValues}")
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
--   → templateIdx=1 (else branch), holes=[51966, 57005, 2000, 0]
--   Hole order: dedup first-occurrence of [fromAddr, to] ++ [amount, fromAddr, to] = [fromAddr, to, amount]
--   Values: fromAddr=0xcafe=51966, to=0xdead=57005, amount_lo=2000, amount_hi=0
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
      unless co.holeValues == [51966, 57005, 2000, 0] do
        throw (IO.userError s!"expected holeValues=[51966, 57005, 2000, 0], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: transferFrom(2000) → templateIdx={co.templateIdx}, holes={repr co.holeValues}"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

-- Test: transferFrom(fromAddr=0xcafe, to=0xdead, amount=MAX)
--   → templateIdx=0 (then branch), holes=[51966, 57005, max128, max128]
--   Hole order: [fromAddr, to, amount_lo, amount_hi]
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
      unless co.holeValues == [51966, 57005, max128, max128] do
        throw (IO.userError s!"expected holeValues=[51966, 57005, max128, max128], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: transferFrom(MAX) → templateIdx={co.templateIdx}, holes match"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

/-! ## Bool Parameter Example

A minimal IntentSpec that exercises the `bool` type (Phase 1).
Models `setApprovalForAll(operator: address, approved: bool)` from ERC-721.
-/

/-- Example: IntentSpec with a bool parameter. -/
def boolIntentSpec : IntentSpec := {
  contractName := "ERC721"

  fns := [
    -- Intent: setApprovalForAll(operator: address, approved: bool)
    { name := "setApprovalForAllIntent"
      params := [("operator", .address), ("approved", .bool)]
      returnKind := .void
      body := [
        .ite (.param "approved")
          [.emit { text := "Approve {operator} to manage all your NFTs",
                   holes := [{ param := "operator", format := .address }] }]
          [.emit { text := "Revoke {operator} from managing your NFTs",
                   holes := [{ param := "operator", format := .address }] }]
      ]
    }
  ]

  bindings := [
    { functionName := "setApprovalForAll", intentFn := "setApprovalForAllIntent" }
  ]
}

-- Test: setApprovalForAll(operator=0xbeef, approved=true)
-- → "Approve {operator} to manage all your NFTs"
#eval do
  let spec := boolIntentSpec
  match getBinding spec 0 with
  | some binding =>
    let params : List (String × Value) := [
      ("operator", .addr "0xbeef"),
      ("approved", .bool true)
    ]
    match evalIntent spec binding params with
    | some [t] =>
      unless t.text == "Approve {operator} to manage all your NFTs" do
        throw (IO.userError s!"wrong text: {t.text}")
      IO.println s!"✓ setApprovalForAll(approved=true): \"{t.text}\""
    | some ts => throw (IO.userError s!"expected 1 template, got {ts.length}")
    | none => throw (IO.userError "evaluation failed")
  | none => throw (IO.userError "binding not found")

-- Test: setApprovalForAll(operator=0xbeef, approved=false)
-- → "Revoke {operator} from managing your NFTs"
#eval do
  let spec := boolIntentSpec
  match getBinding spec 0 with
  | some binding =>
    let params : List (String × Value) := [
      ("operator", .addr "0xbeef"),
      ("approved", .bool false)
    ]
    match evalIntent spec binding params with
    | some [t] =>
      unless t.text == "Revoke {operator} from managing your NFTs" do
        throw (IO.userError s!"wrong text: {t.text}")
      IO.println s!"✓ setApprovalForAll(approved=false): \"{t.text}\""
    | some ts => throw (IO.userError s!"expected 1 template, got {ts.length}")
    | none => throw (IO.userError "evaluation failed")
  | none => throw (IO.userError "binding not found")

-- Test: circuit output for setApprovalForAll(operator=0xbeef, approved=true)
-- → templateIdx=0 (then branch), holes=[48879] (operator only)
#eval do
  let spec := boolIntentSpec
  match getBinding spec 0 with
  | some binding =>
    let params : List (String × Value) := [
      ("operator", .addr "0xbeef"),
      ("approved", .bool true)
    ]
    match evalIntentCircuitOutput spec binding params with
    | some co =>
      unless co.templateIdx == 0 do
        throw (IO.userError s!"expected templateIdx=0, got {co.templateIdx}")
      unless co.holeValues == [48879] do
        throw (IO.userError s!"expected holeValues=[48879], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: setApprovalForAll(true) → templateIdx={co.templateIdx}, holes={repr co.holeValues}"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

-- Test: circuit output for setApprovalForAll(operator=0xbeef, approved=false)
-- → templateIdx=1 (else branch), holes=[48879] (operator only)
#eval do
  let spec := boolIntentSpec
  match getBinding spec 0 with
  | some binding =>
    let params : List (String × Value) := [
      ("operator", .addr "0xbeef"),
      ("approved", .bool false)
    ]
    match evalIntentCircuitOutput spec binding params with
    | some co =>
      unless co.templateIdx == 1 do
        throw (IO.userError s!"expected templateIdx=1, got {co.templateIdx}")
      unless co.holeValues == [48879] do
        throw (IO.userError s!"expected holeValues=[48879], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: setApprovalForAll(false) → templateIdx={co.templateIdx}, holes={repr co.holeValues}"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

/-! ## ERC-721 Approve / TransferFrom Tests (Production IntentSpec)

Tests for the two remaining ERC-721 bindings using the production
`Contracts.ERC721.intentSpec` (binding 0 = approve, binding 2 = transferFrom).
Both are unconditional (single-template) functions.
-/

-- Test: ERC-721 approve(approved=0xbeef, tokenId=42)
-- → "Approve {approved} to transfer token #{tokenId}"
#eval do
  let spec := Contracts.ERC721.intentSpec
  match getBinding spec 0 with
  | some binding =>
    let params : List (String × Value) := [
      ("approved", .addr "0xbeef"),
      ("tokenId", .int 42)
    ]
    match evalIntent spec binding params with
    | some [t] =>
      unless t.text == "Approve {approved} to transfer token #{tokenId}" do
        throw (IO.userError s!"wrong text: {t.text}")
      unless t.holes.length == 2 do
        throw (IO.userError s!"expected 2 holes, got {t.holes.length}")
      IO.println s!"✓ ERC-721 approve(tokenId=42): \"{t.text}\""
    | some ts => throw (IO.userError s!"expected 1 template, got {ts.length}")
    | none => throw (IO.userError "evaluation failed")
  | none => throw (IO.userError "binding not found")

-- Test: ERC-721 transferFrom(fromAddr=0xcafe, to=0xdead, tokenId=99)
-- → "Transfer token #{tokenId} from {fromAddr} to {to}"
#eval do
  let spec := Contracts.ERC721.intentSpec
  match getBinding spec 2 with
  | some binding =>
    let params : List (String × Value) := [
      ("fromAddr", .addr "0xcafe"),
      ("to", .addr "0xdead"),
      ("tokenId", .int 99)
    ]
    match evalIntent spec binding params with
    | some [t] =>
      unless t.text == "Transfer token #{tokenId} from {fromAddr} to {to}" do
        throw (IO.userError s!"wrong text: {t.text}")
      unless t.holes.length == 3 do
        throw (IO.userError s!"expected 3 holes, got {t.holes.length}")
      IO.println s!"✓ ERC-721 transferFrom(tokenId=99): \"{t.text}\""
    | some ts => throw (IO.userError s!"expected 1 template, got {ts.length}")
    | none => throw (IO.userError "evaluation failed")
  | none => throw (IO.userError "binding not found")

-- Test: circuit output for ERC-721 approve(approved=0xbeef, tokenId=42)
-- → templateIdx=0 (unconditional), holes=[48879, 42, 0]
-- Hole order: approved (address → Nat), tokenId (uint256 → lo, hi)
#eval do
  let spec := Contracts.ERC721.intentSpec
  match getBinding spec 0 with
  | some binding =>
    let params : List (String × Value) := [
      ("approved", .addr "0xbeef"),
      ("tokenId", .int 42)
    ]
    match evalIntentCircuitOutput spec binding params with
    | some co =>
      unless co.templateIdx == 0 do
        throw (IO.userError s!"expected templateIdx=0, got {co.templateIdx}")
      unless co.holeValues == [48879, 42, 0] do
        throw (IO.userError s!"expected holeValues=[48879, 42, 0], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: ERC-721 approve(42) → templateIdx={co.templateIdx}, holes={repr co.holeValues}"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

-- Test: circuit output for ERC-721 transferFrom(fromAddr=0xcafe, to=0xdead, tokenId=99)
-- → templateIdx=0 (unconditional), holes=[99, 0, 51966, 57005]
-- Hole order: tokenId (uint256 → lo, hi), fromAddr (address → Nat), to (address → Nat)
#eval do
  let spec := Contracts.ERC721.intentSpec
  match getBinding spec 2 with
  | some binding =>
    let params : List (String × Value) := [
      ("fromAddr", .addr "0xcafe"),
      ("to", .addr "0xdead"),
      ("tokenId", .int 99)
    ]
    match evalIntentCircuitOutput spec binding params with
    | some co =>
      unless co.templateIdx == 0 do
        throw (IO.userError s!"expected templateIdx=0, got {co.templateIdx}")
      unless co.holeValues == [99, 0, 51966, 57005] do
        throw (IO.userError s!"expected holeValues=[99, 0, 51966, 57005], got {repr co.holeValues}")
      IO.println s!"✓ Circuit output: ERC-721 transferFrom(99) → templateIdx={co.templateIdx}, holes={repr co.holeValues}"
    | none => throw (IO.userError "evalIntentCircuitOutput returned none")
  | none => throw (IO.userError "binding not found")

/-! ## Validation Tests for Ledger and ERC-721 Production IntentSpecs

Validate the production intentSpecs against mock CompilationModels matching their ABIs.
-/

/-- Mock Ledger CompilationModel: deposit, withdraw, transfer. -/
private def mockLedgerModel : CompilationModel := {
  name := "Ledger"
  fields := []
  constructor := none
  functions := [
    { name := "deposit"
      params := [⟨"amount", .uint256⟩]
      returnType := none
      body := [] },
    { name := "withdraw"
      params := [⟨"amount", .uint256⟩]
      returnType := none
      body := [] },
    { name := "transfer"
      params := [⟨"to", .address⟩, ⟨"amount", .uint256⟩]
      returnType := none
      body := [] }
  ]
}

-- Test: Ledger intentSpec validates against its CompilationModel.
#eval do
  let errors := Validate.validate Contracts.Ledger.intentSpec mockLedgerModel
  if errors.isEmpty then
    IO.println "✓ Ledger intentSpec validates against mock CompilationModel"
  else
    for e in errors do
      IO.println s!"✗ {e}"
    throw (IO.userError "Ledger validation failed")

/-- Mock ERC-721 CompilationModel: approve, setApprovalForAll, transferFrom. -/
private def mockErc721Model : CompilationModel := {
  name := "ERC721"
  fields := []
  constructor := none
  functions := [
    { name := "approve"
      params := [⟨"approved", .address⟩, ⟨"tokenId", .uint256⟩]
      returnType := none
      body := [] },
    { name := "setApprovalForAll"
      params := [⟨"operator", .address⟩, ⟨"approved", .bool⟩]
      returnType := none
      body := [] },
    { name := "transferFrom"
      params := [⟨"fromAddr", .address⟩, ⟨"to", .address⟩, ⟨"tokenId", .uint256⟩]
      returnType := none
      body := [] }
  ]
}

-- Test: ERC-721 intentSpec validates against its CompilationModel.
#eval do
  let errors := Validate.validate Contracts.ERC721.intentSpec mockErc721Model
  if errors.isEmpty then
    IO.println "✓ ERC-721 intentSpec validates against mock CompilationModel"
  else
    for e in errors do
      IO.println s!"✗ {e}"
    throw (IO.userError "ERC-721 validation failed")

/-! ## Phase 2: forEach + enum Smoke Tests -/

/-- A mock multicall-like intent spec that uses forEach to iterate over actions. -/
private def forEachIntentSpec : IntentSpec := {
  contractName := "Multicall"
  fns := [
    { name := "multicallIntent"
      params := [("targets", .address)]  -- simplified: single param for the test
      returnKind := .void
      body := [
        .forEach "target" (.param "targets")
          [.emit { text := "Call {target}",
                   holes := [{ param := "target", format := .address }] }]
      ]
    }
  ]
  bindings := [
    { functionName := "multicall", intentFn := "multicallIntent" }
  ]
}

-- Test: forEach evaluator emits one template per list element.
#eval do
  let spec := forEachIntentSpec
  match spec.bindings with
  | binding :: _ =>
    let params : List (String × Value) := [
      ("targets", .list [.addr "0xdead", .addr "0xbeef", .addr "0xcafe"])
    ]
    match evalIntent spec binding params with
    | some templates =>
      unless templates.length == 3 do
        throw (IO.userError s!"expected 3 templates, got {templates.length}")
      match templates with
      | t0 :: _ :: t2 :: _ =>
        unless t0.text == "Call {target}" do
          throw (IO.userError s!"wrong text: {t0.text}")
        match t0.holes with
        | h :: _ =>
          match h.value with
          | .addr a => unless a == "0xdead" do
              throw (IO.userError s!"expected 0xdead, got {a}")
          | _ => throw (IO.userError "expected addr value")
        | _ => throw (IO.userError "missing holes")
        match t2.holes with
        | h :: _ =>
          match h.value with
          | .addr a => unless a == "0xcafe" do
              throw (IO.userError s!"expected 0xcafe, got {a}")
          | _ => throw (IO.userError "expected addr value")
        | _ => throw (IO.userError "missing holes")
      | _ => throw (IO.userError "expected 3 templates")
      IO.println s!"✓ forEach multicall: emitted {templates.length} templates correctly"
    | none => throw (IO.userError "forEach eval returned none")
  | [] => throw (IO.userError "no bindings")

/-- A mock intent spec that uses enum format. -/
private def enumIntentSpec' : IntentSpec := {
  contractName := "Lending"
  enums := [
    { name := "RateMode", values := [(1, "Stable"), (2, "Variable")] }
  ]
  fns := [
    { name := "borrowIntent"
      params := [("amount", .uint256), ("rateMode", .bool)]
      returnKind := .void
      body := [
        .emit { text := "Borrow {amount} at {rateMode} rate",
                holes := [{ param := "amount", format := .tokenAmount 18 },
                          { param := "rateMode", format := .enum "RateMode" }] }
      ]
    }
  ]
  bindings := [
    { functionName := "borrow", intentFn := "borrowIntent" }
  ]
}

-- Test: enum format evaluator runs without error.
#eval do
  let spec := enumIntentSpec'
  match spec.bindings with
  | binding :: _ =>
    let params : List (String × Value) := [
      ("amount", .int 5000),
      ("rateMode", .int 1)
    ]
    match evalIntent spec binding params with
    | some templates =>
      unless templates.length == 1 do
        throw (IO.userError s!"expected 1 template, got {templates.length}")
      match templates with
      | t :: _ =>
        unless t.text == "Borrow {amount} at {rateMode} rate" do
          throw (IO.userError s!"wrong text: {t.text}")
      | _ => throw (IO.userError "expected 1 template")
      IO.println "✓ Enum format: borrow intent evaluates correctly"
    | none => throw (IO.userError "enum eval returned none")
  | [] => throw (IO.userError "no bindings")

-- Test: index and length expressions.
#eval do
  let env : Env := [("arr", .list [.int 10, .int 20, .int 30])]
  let idxExpr := Expr.index (.param "arr") (.intLit 1)
  match evalExpr [] [] env 100 idxExpr with
  | some (.int 20) => pure ()
  | some v => throw (IO.userError s!"expected int 20, got {repr v}")
  | none => throw (IO.userError "index eval returned none")
  let lenExpr := Expr.length (.param "arr")
  match evalExpr [] [] env 100 lenExpr with
  | some (.int 3) => pure ()
  | some v => throw (IO.userError s!"expected int 3, got {repr v}")
  | none => throw (IO.userError "length eval returned none")
  IO.println "✓ index/length: arr[1]=20, arr.length=3"

/-! ## DSL Macro Equivalence Tests

Verify that the `intent_spec` DSL macro generates IntentSpecs identical
to the hand-written ones. This tests the macro end-to-end.
-/

open Verity.Intent.DSL

-- Define an ERC-20 spec using the DSL macro (generates `dslErc20.intentSpec`)
namespace dslErc20

private def maxUint256 : Int := (2 ^ 256 : Nat) - 1

intent_spec "ERC20" where
  const MAX_UINT256 := maxUint256

  predicate isMaxUint(v : uint256) :=
    v == MAX_UINT256

  intent transfer(to : address, amount : uint256) where
    when isMaxUint(amount) =>
      emit "Send all tokens to {to:address}"
    otherwise =>
      emit "Send {amount:tokenAmount 18 \"TOKEN\"} tokens to {to:address}"

  intent approve(spender : address, amount : uint256) where
    when isMaxUint(amount) =>
      emit "Approve {spender:address} to spend unlimited tokens"
    otherwise =>
      emit "Approve {spender:address} to spend {amount:tokenAmount 18 \"TOKEN\"} tokens"

  intent transferFrom(fromAddr : address, to : address, amount : uint256) where
    when isMaxUint(amount) =>
      emit "Transfer all tokens from {fromAddr:address} to {to:address}"
    otherwise =>
      emit "Transfer {amount:tokenAmount 18 \"TOKEN\"} tokens from {fromAddr:address} to {to:address}"

end dslErc20

-- Test: DSL-generated spec matches hand-written spec field by field
#eval do
  let dsl := dslErc20.intentSpec
  let hw := erc20IntentSpec
  unless dsl.contractName == hw.contractName do
    throw (IO.userError s!"contractName mismatch: {dsl.contractName} vs {hw.contractName}")
  unless dsl.fns.length == hw.fns.length do
    throw (IO.userError s!"fns count mismatch: {dsl.fns.length} vs {hw.fns.length}")
  unless dsl.bindings.length == hw.bindings.length do
    throw (IO.userError s!"bindings count mismatch: {dsl.bindings.length} vs {hw.bindings.length}")
  unless dsl.constants.length == hw.constants.length do
    throw (IO.userError s!"constants count mismatch: {dsl.constants.length} vs {hw.constants.length}")
  -- Verify binding names match
  for (db, hb) in dsl.bindings.zip hw.bindings do
    unless db.functionName == hb.functionName do
      throw (IO.userError s!"binding functionName mismatch: {db.functionName} vs {hb.functionName}")
    unless db.intentFn == hb.intentFn do
      throw (IO.userError s!"binding intentFn mismatch: {db.intentFn} vs {hb.intentFn}")
  -- Verify function names and params match
  for (df, hf) in dsl.fns.zip hw.fns do
    unless df.name == hf.name do
      throw (IO.userError s!"fn name mismatch: {df.name} vs {hf.name}")
    unless df.params.length == hf.params.length do
      throw (IO.userError s!"fn {df.name} params count mismatch")
    unless df.returnKind == hf.returnKind do
      throw (IO.userError s!"fn {df.name} returnKind mismatch")
  IO.println "✓ DSL-generated ERC-20 spec matches hand-written spec"

-- Test: DSL-generated spec works with the evaluator
#eval do
  let spec := dslErc20.intentSpec
  match spec.bindings[0]? with
  | some binding =>
    let params : List (String × Value) := [
      ("to", .addr "0xdead"),
      ("amount", .int 1000)
    ]
    match evalIntent spec binding params with
    | some [t] =>
      unless t.text == "Send {amount} tokens to {to}" do
        throw (IO.userError s!"wrong text: {t.text}")
      IO.println s!"✓ DSL spec evaluator: transfer(1000) = \"{t.text}\""
    | some ts => throw (IO.userError s!"expected 1 template, got {ts.length}")
    | none => throw (IO.userError "evaluation failed")
  | none => throw (IO.userError "binding not found")

-- Test: DSL-generated spec works with the validator
#eval do
  let errors := Validate.validate dslErc20.intentSpec mockErc20Model
  if errors.isEmpty then
    IO.println "✓ DSL-generated ERC-20 spec validates against mock CompilationModel"
  else
    for e in errors do
      IO.println s!"✗ {e}"
    throw (IO.userError "DSL spec validation failed")

end Verity.Intent.Example
