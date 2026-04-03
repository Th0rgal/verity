/-
  Compiler.CircomTest: Smoke tests for the Circom circuit generator.

  Uses the ERC-20 example IntentSpec to generate and print Circom circuits.
  These #eval blocks run at build time and verify the generator produces output.
-/
import Compiler.Circom
import Verity.Intent.Example

namespace Compiler.CircomTest

open Verity.Intent
open Verity.Intent.Example

-- Generate and print the Circom output for the transfer intent.
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 0 with
  | some binding =>
    match Compiler.Circom.emitCircom spec binding "0xa9059cbb" with
    | some circom =>
      IO.println "=== Generated Circom for ERC20.transfer ==="
      IO.println circom
    | none =>
      IO.println "ERROR: Circom generation failed for transfer"
  | none => IO.println "ERROR: binding not found"

-- Generate and print the Circom output for the approve intent.
#eval do
  let spec := erc20IntentSpec
  match getBinding spec 1 with
  | some binding =>
    match Compiler.Circom.emitCircom spec binding "0x095ea7b3" with
    | some circom =>
      IO.println "=== Generated Circom for ERC20.approve ==="
      IO.println circom
    | none =>
      IO.println "ERROR: Circom generation failed for approve"
  | none => IO.println "ERROR: binding not found"

end Compiler.CircomTest
