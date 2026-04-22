import Std
import Compiler.CompilationModel
import Compiler.Hex
import Compiler.Selectors

namespace Compiler.Selector

open Compiler.CompilationModel
open Compiler.Hex

private def externalFunctions (spec : CompilationModel) : List FunctionSpec :=
  spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)

def runKeccak (sigs : List String) : IO (List Nat) := do
  pure <| sigs.map Compiler.keccak256_first_4_bytes

/-- Compute Solidity-compatible selectors for external functions in a spec.
    Internal functions and special entrypoints (fallback/receive) are excluded
    since they are not dispatched via selector. Uses `isInteropEntrypointName`
    so this filter stays in sync with `CompilationModel.compile`. -/
def computeSelectors (spec : CompilationModel) : IO (List Nat) := do
  let externalFns := externalFunctions spec
  let sigs := externalFns.map functionSignature
  runKeccak sigs

/-- Validate that caller-provided selectors exactly match canonical Solidity
    selectors for each external function in declaration order. -/
def validateSelectors (spec : CompilationModel) (selectors : List Nat) : IO (Except String Unit) := do
  let externalFns := externalFunctions spec
  let expected ← computeSelectors spec
  if selectors.length != expected.length then
    return .error s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {expected.length} external functions"
  match ((externalFns.zip selectors).zip expected).find? (fun ((_, provided), canonical) => provided != canonical) with
  | some ((fn, provided), canonical) =>
      return .error s!"Selector mismatch in {spec.name} for function '{fn.name}': expected {natToHex canonical}, got {natToHex provided}"
  | none =>
      return .ok ()

/-- Checked compilation boundary for caller-supplied selector lists.
    Validates selectors against canonical Solidity signatures before invoking
    the core pure compiler. -/
def compileChecked (spec : CompilationModel) (selectors : List Nat) : IO (Except String IRContract) := do
  match ← validateSelectors spec selectors with
  | .error err => return .error err
  | .ok () => return Compiler.CompilationModel.compile spec selectors

end Compiler.Selector
