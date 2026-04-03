/-
  Compiler.CircomTest: Regression tests for the Circom circuit generator.

  Uses the ERC-20 example IntentSpec to generate Circom circuits and verify
  key structural properties at build time. These tests catch regressions
  in the circuit generator without requiring external tools (circom, snarkjs).

  IMPORTANT: The full Circom output is printed with header markers, because
  `scripts/test_circom_e2e.sh` parses this output to extract `.circom` files
  for external compilation and witness verification. The headers are:
    === Generated Circom for ERC20.transfer ===
    === Generated Circom for ERC20.approve ===
  No other text may appear between a header and the next header (or EOF).
  All assertion messages are printed BEFORE the first header.
-/
import Compiler.Circom
import Verity.Intent.Example

namespace Compiler.CircomTest

open Verity.Intent
open Verity.Intent.Example

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Verify structural properties of the transfer Circom circuit. -/
private def assertTransferStructure (circom : String) : IO Unit := do
  unless hasSubstr circom "template TransferIntent()" do
    throw (IO.userError "missing template TransferIntent()")
  unless hasSubstr circom "selector === 0xa9059cbb" do
    throw (IO.userError "missing selector check")
  unless hasSubstr circom "signal input selector" do
    throw (IO.userError "missing selector input")
  unless hasSubstr circom "signal input calldataCommitment" do
    throw (IO.userError "missing calldataCommitment input")
  unless hasSubstr circom "signal input outputCommitment" do
    throw (IO.userError "missing outputCommitment input")
  unless hasSubstr circom "signal input to" do
    throw (IO.userError "missing 'to' input")
  unless hasSubstr circom "signal input amount_lo" do
    throw (IO.userError "missing 'amount_lo' input")
  unless hasSubstr circom "signal input amount_hi" do
    throw (IO.userError "missing 'amount_hi' input")
  unless hasSubstr circom "component cdHash = Poseidon(4)" do
    throw (IO.userError "missing calldata Poseidon(4)")
  unless hasSubstr circom "component outHash = Poseidon(4)" do
    throw (IO.userError "missing output Poseidon(4)")
  unless hasSubstr circom "IsEqual()" do
    throw (IO.userError "missing IsEqual for uint256 comparison")
  unless hasSubstr circom "signal templateId" do
    throw (IO.userError "missing templateId signal")
  unless hasSubstr circom "component main {public [selector, calldataCommitment, outputCommitment]}" do
    throw (IO.userError "missing main component declaration")

/-- Verify structural properties of the approve Circom circuit. -/
private def assertApproveStructure (circom : String) : IO Unit := do
  unless hasSubstr circom "template ApproveIntent()" do
    throw (IO.userError "missing template ApproveIntent()")
  unless hasSubstr circom "selector === 0x095ea7b3" do
    throw (IO.userError "missing selector check")
  unless hasSubstr circom "signal input spender" do
    throw (IO.userError "missing 'spender' input")
  unless hasSubstr circom "signal input amount_lo" do
    throw (IO.userError "missing 'amount_lo' input")
  unless hasSubstr circom "component cdHash = Poseidon(4)" do
    throw (IO.userError "missing calldata Poseidon(4)")
  unless hasSubstr circom "component outHash = Poseidon(4)" do
    throw (IO.userError "missing output Poseidon(4)")
  unless hasSubstr circom "component main" do
    throw (IO.userError "missing main component")

-- Single #eval block: run all assertions, then print structured output.
-- All assertion/status messages come before headers so the E2E script's
-- awk extraction gets clean circom source between headers (and to EOF).
#eval do
  let spec := erc20IntentSpec

  -- Generate transfer circuit
  let transferBinding ← match getBinding spec 0 with
    | some b => pure b
    | none => throw (IO.userError "transfer binding not found")
  let transferCircom ← match Compiler.Circom.emitCircom spec transferBinding "0xa9059cbb" with
    | some c => pure c
    | none => throw (IO.userError "Circom generation failed for transfer")
  assertTransferStructure transferCircom

  -- Generate approve circuit
  let approveBinding ← match getBinding spec 1 with
    | some b => pure b
    | none => throw (IO.userError "approve binding not found")
  let approveCircom ← match Compiler.Circom.emitCircom spec approveBinding "0x095ea7b3" with
    | some c => pure c
    | none => throw (IO.userError "Circom generation failed for approve")
  assertApproveStructure approveCircom

  -- Verify emitCircom returns none for invalid bindings
  let badBinding : IntentBinding := { functionName := "fake", intentFn := "nonexistent" }
  match Compiler.Circom.emitCircom spec badBinding "0x00000000" with
  | some _ => throw (IO.userError "expected none for invalid binding")
  | none => pure ()

  -- All assertions passed. Print status messages first, then headers+circom.
  IO.println "✓ TransferIntent: all structural checks pass"
  IO.println "✓ ApproveIntent: all structural checks pass"
  IO.println "✓ Invalid binding correctly returns none"
  IO.println "=== Generated Circom for ERC20.transfer ==="
  IO.println transferCircom
  IO.println "=== Generated Circom for ERC20.approve ==="
  IO.println approveCircom

end Compiler.CircomTest
