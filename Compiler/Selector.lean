import Std
import Compiler.ContractSpec

namespace Compiler.Selector

open Compiler.ContractSpec

private def paramTypeToSol : ParamType -> String
  | ParamType.uint256 => "uint256"
  | ParamType.address => "address"

private def functionSignature (fn : FunctionSpec) : String :=
  let params := fn.params.map (fun p => paramTypeToSol p.ty)
  let paramStr := String.intercalate "," params
  s!"{fn.name}({paramStr})"

private def parseHexChar? (c : Char) : Option Nat :=
  if c >= '0' && c <= '9' then
    some (c.toNat - '0'.toNat)
  else if c >= 'a' && c <= 'f' then
    some (10 + (c.toNat - 'a'.toNat))
  else if c >= 'A' && c <= 'F' then
    some (10 + (c.toNat - 'A'.toNat))
  else
    none

private def hexToNat? (s : String) : Option Nat :=
  s.foldl (fun acc c =>
    match acc, parseHexChar? c with
    | some n, some v => some (n * 16 + v)
    | _, _ => none
  ) (some 0)

private def parseSelectorLine (line : String) : Option Nat :=
  let trimmed := line.trim
  let hex := if trimmed.startsWith "0x" then trimmed.drop 2 else trimmed
  hexToNat? hex

private def runKeccak (sigs : List String) : IO (List Nat) := do
  if sigs.isEmpty then
    return []
  let args := #["scripts/keccak256.py"] ++ sigs.toArray
  let result ← IO.Process.output { cmd := "python3", args := args }
  if result.exitCode != 0 then
    throw (IO.userError s!"keccak256.py failed: {result.stderr}")
  let lines := result.stdout.trim.splitOn "\n"
  let selectors := lines.map parseSelectorLine
  if selectors.any (·.isNone) then
    throw (IO.userError s!"Failed to parse selector output: {result.stdout}")
  return selectors.map Option.get!

/-- Compute Solidity-compatible selectors for all functions in a spec. -/
def computeSelectors (spec : ContractSpec) : IO (List Nat) := do
  let sigs := spec.functions.map functionSignature
  runKeccak sigs

end Compiler.Selector
