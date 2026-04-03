/-
  Compiler.CircomTest: Regression tests for the Circom circuit generator.

  Uses the ERC-20 example IntentSpec to generate Circom circuits and verify
  key structural properties at build time. These tests catch regressions
  in the circuit generator without requiring external tools (circom, snarkjs).
-/
import Compiler.Circom
import Verity.Intent.Example

namespace Compiler.CircomTest

open Verity.Intent
open Verity.Intent.Example

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

-- Transfer intent: generate and verify structural properties.
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 0 with
  | some binding =>
    match Compiler.Circom.emitCircom spec binding "0xa9059cbb" with
    | some circom =>
      -- Template name
      unless hasSubstr circom "template TransferIntent()" do
        throw (IO.userError "missing template TransferIntent()")
      -- Selector check
      unless hasSubstr circom "selector === 0xa9059cbb" do
        throw (IO.userError "missing selector check")
      -- Public inputs
      unless hasSubstr circom "signal input selector" do
        throw (IO.userError "missing selector input")
      unless hasSubstr circom "signal input calldataCommitment" do
        throw (IO.userError "missing calldataCommitment input")
      unless hasSubstr circom "signal input outputCommitment" do
        throw (IO.userError "missing outputCommitment input")
      -- Private param inputs (uint256 split into lo/hi)
      unless hasSubstr circom "signal input to" do
        throw (IO.userError "missing 'to' input")
      unless hasSubstr circom "signal input amount_lo" do
        throw (IO.userError "missing 'amount_lo' input")
      unless hasSubstr circom "signal input amount_hi" do
        throw (IO.userError "missing 'amount_hi' input")
      -- Calldata commitment uses Poseidon(4): selector + to + amount_lo + amount_hi
      unless hasSubstr circom "component cdHash = Poseidon(4)" do
        throw (IO.userError "missing calldata Poseidon(4)")
      -- Output commitment uses Poseidon(4): templateId + amount_lo + amount_hi + to
      unless hasSubstr circom "component outHash = Poseidon(4)" do
        throw (IO.userError "missing output Poseidon(4)")
      -- IsEqual for uint256 comparison (isMaxUint)
      unless hasSubstr circom "IsEqual()" do
        throw (IO.userError "missing IsEqual for uint256 comparison")
      -- Template selection with two paths
      unless hasSubstr circom "signal templateId" do
        throw (IO.userError "missing templateId signal")
      -- Main component with public inputs
      unless hasSubstr circom "component main {public [selector, calldataCommitment, outputCommitment]}" do
        throw (IO.userError "missing main component declaration")
      IO.println "✓ TransferIntent: all structural checks pass"
    | none =>
      throw (IO.userError "Circom generation failed for transfer")
  | none => throw (IO.userError "binding not found")

-- Approve intent: generate and verify structural properties.
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 1 with
  | some binding =>
    match Compiler.Circom.emitCircom spec binding "0x095ea7b3" with
    | some circom =>
      -- Template name
      unless hasSubstr circom "template ApproveIntent()" do
        throw (IO.userError "missing template ApproveIntent()")
      -- Selector check
      unless hasSubstr circom "selector === 0x095ea7b3" do
        throw (IO.userError "missing selector check")
      -- Private param inputs
      unless hasSubstr circom "signal input spender" do
        throw (IO.userError "missing 'spender' input")
      unless hasSubstr circom "signal input amount_lo" do
        throw (IO.userError "missing 'amount_lo' input")
      -- Calldata commitment
      unless hasSubstr circom "component cdHash = Poseidon(4)" do
        throw (IO.userError "missing calldata Poseidon(4)")
      -- Output commitment
      unless hasSubstr circom "component outHash = Poseidon(4)" do
        throw (IO.userError "missing output Poseidon(4)")
      -- Main component
      unless hasSubstr circom "component main" do
        throw (IO.userError "missing main component")
      IO.println "✓ ApproveIntent: all structural checks pass"
    | none =>
      throw (IO.userError "Circom generation failed for approve")
  | none => throw (IO.userError "binding not found")

-- Verify emitCircom returns none for invalid bindings.
#eval do
  let spec := erc20IntentSpec
  let badBinding : IntentBinding := { functionName := "fake", intentFn := "nonexistent" }
  match Compiler.Circom.emitCircom spec badBinding "0x00000000" with
  | some _ => throw (IO.userError "expected none for invalid binding")
  | none => IO.println "✓ Invalid binding correctly returns none"

end Compiler.CircomTest
