import Std
import Compiler.ContractSpec
import Compiler.Hex

namespace Compiler.Selector

open Compiler.ContractSpec
open Compiler.Hex

private def functionSignature (fn : FunctionSpec) : String :=
  let params := fn.params.map (fun p => paramTypeToSolidityString p.ty)
  let paramStr := String.intercalate "," params
  s!"{fn.name}({paramStr})"

private def parseSelectorLine (line : String) : Option Nat :=
  let trimmed := line.trim
  parseHexNat? trimmed

private def runKeccak (sigs : List String) : IO (List Nat) := do
  if sigs.isEmpty then
    return []
  let args := #["scripts/keccak256.py"] ++ sigs.toArray
  let result ← IO.Process.output { cmd := "python3", args := args }
  if result.exitCode != 0 then
    throw (IO.userError s!"keccak256.py failed: {result.stderr}")
  let lines := result.stdout.trim.splitOn "\n"
  if lines.length != sigs.length then
    throw (IO.userError s!"keccak256.py returned {lines.length} lines for {sigs.length} signatures: {result.stdout}")
  let selectors := lines.filterMap parseSelectorLine
  if selectors.length != sigs.length then
    throw (IO.userError s!"Failed to parse selector output: {result.stdout}")
  return selectors

/-- Compute Solidity-compatible selectors for external functions in a spec.
    Internal functions and special entrypoints (fallback/receive) are excluded
    since they are not dispatched via selector. This filter must match the one
    in `ContractSpec.compile` to avoid a selector count mismatch. -/
def computeSelectors (spec : ContractSpec) : IO (List Nat) := do
  let externalFns := spec.functions.filter (fun fn =>
    !fn.isInternal && !["fallback", "receive"].contains fn.name)
  let sigs := externalFns.map functionSignature
  runKeccak sigs

end Compiler.Selector
