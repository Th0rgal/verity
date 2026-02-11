import Std
import Compiler.ContractSpec
import Compiler.Hex

namespace Compiler.Selector

open Compiler.ContractSpec
open Compiler.Hex

private def paramTypeToSol : ParamType -> String
  | ParamType.uint256 => "uint256"
  | ParamType.address => "address"

private def functionSignature (fn : FunctionSpec) : String :=
  let params := fn.params.map (fun p => paramTypeToSol p.ty)
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
  let selectors := lines.map parseSelectorLine
  if selectors.any (·.isNone) then
    throw (IO.userError s!"Failed to parse selector output: {result.stdout}")
  return selectors.map Option.get!

/-- Compute Solidity-compatible selectors for all functions in a spec. -/
def computeSelectors (spec : ContractSpec) : IO (List Nat) := do
  let sigs := spec.functions.map functionSignature
  runKeccak sigs

end Compiler.Selector
