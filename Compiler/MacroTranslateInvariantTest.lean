import Compiler.ABI
import Compiler.Selector
import Contracts.MacroContracts.Core
import Contracts.MacroContracts.Tokens
import Contracts.MacroContracts.Smoke

namespace Compiler.MacroTranslateInvariantTest

open Compiler
open Compiler.CompilationModel

private def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
        if (c :: cs).take n.length == n then true
        else go cs
    go h

private def countOccurrences (haystack needle : String) : Nat :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then 0
  else
    let rec go : List Char → Nat
      | [] => 0
      | c :: cs =>
        if (c :: cs).take n.length == n then
          1 + go cs
        else
          go cs
    go h

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"✗ {label}")
  IO.println s!"✓ {label}"

private def allDistinct [DecidableEq α] (xs : List α) : Bool :=
  xs.length == xs.eraseDups.length

private def externalFunctions (spec : CompilationModel) : List FunctionSpec :=
  spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)

private def canonicalFieldSlots (spec : CompilationModel) : List Nat :=
  let indexed := List.zip (List.range spec.fields.length) spec.fields
  indexed.map (fun (idx, field) => field.slot.getD idx)

private def writeSlots (spec : CompilationModel) : List Nat :=
  let indexed := List.zip (List.range spec.fields.length) spec.fields
  indexed.flatMap (fun (idx, field) => field.slot.getD idx :: field.aliasSlots)

private def macroSpecs : List CompilationModel :=
  [ Contracts.MacroContracts.SimpleStorage.spec
  , Contracts.MacroContracts.Counter.spec
  , Contracts.MacroContracts.Owned.spec
  , Contracts.MacroContracts.Ledger.spec
  , Contracts.MacroContracts.SafeCounter.spec
  , Contracts.MacroContracts.OwnedCounter.spec
  , Contracts.MacroContracts.SimpleToken.spec
  , Contracts.MacroContracts.ERC20.spec
  , Contracts.MacroContracts.ERC721.spec
  , Contracts.MacroContracts.UintMapSmoke.spec
  , Contracts.MacroContracts.Bytes32Smoke.spec
  , Contracts.MacroContracts.MappingWordSmoke.spec
  , Contracts.MacroContracts.StorageWordsSmoke.spec
  , Contracts.MacroContracts.TupleSmoke.spec
  , Contracts.MacroContracts.Uint8Smoke.spec
  ]

private def checkSpec (spec : CompilationModel) : IO Unit := do
  let extFns := externalFunctions spec
  let fnNames := extFns.map (·.name)
  expectTrue s!"{spec.name}: external function names are unique" (allDistinct fnNames)

  let fieldNames := spec.fields.map (·.name)
  expectTrue s!"{spec.name}: field names are unique" (allDistinct fieldNames)

  let slots := canonicalFieldSlots spec
  expectTrue s!"{spec.name}: canonical storage slots are unique" (allDistinct slots)

  let writes := writeSlots spec
  expectTrue s!"{spec.name}: write slots are unique (canonical + alias)" (allDistinct writes)

  let selectors ← Selector.computeSelectors spec
  expectTrue s!"{spec.name}: selector count matches external function count"
    (selectors.length == extFns.length)

  let compileResult ← Selector.compileChecked spec selectors
  match compileResult with
  | .ok _ =>
      IO.println s!"✓ {spec.name}: compileChecked succeeds with canonical selectors"
  | .error err =>
      throw (IO.userError s!"✗ {spec.name}: compileChecked failed: {err}")

  let abi := ABI.emitContractABIJson spec
  let abiFunctionCount := countOccurrences abi "\"type\": \"function\""
  expectTrue s!"{spec.name}: ABI function count matches external function count"
    (abiFunctionCount == extFns.length)

  -- Sanity-check ABI output contains each external function name.
  let allNamesPresent :=
    fnNames.all (fun fnName => contains abi s!"\"name\": \"{fnName}\"")
  expectTrue s!"{spec.name}: ABI contains every external function name" allNamesPresent

#eval! do
  for spec in macroSpecs do
    checkSpec spec

end Compiler.MacroTranslateInvariantTest
