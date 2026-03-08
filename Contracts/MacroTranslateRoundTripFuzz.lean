import Compiler.Selector
import Compiler.Hex
import Compiler.Proofs.YulGeneration.Equivalence
import Contracts
import Contracts.Smoke

namespace Compiler.MacroTranslateRoundTripFuzz

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"round-trip fuzz failed: {label}")

private def externalFunctions (spec : CompilationModel) : List FunctionSpec :=
  spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)

private def canonicalFieldSlots (spec : CompilationModel) : List Nat :=
  let indexed := List.zip (List.range spec.fields.length) spec.fields
  indexed.map (fun (idx, field) => field.slot.getD idx)

private def writeSlots (spec : CompilationModel) : List Nat :=
  let indexed := List.zip (List.range spec.fields.length) spec.fields
  indexed.flatMap (fun (idx, field) => field.slot.getD idx :: field.aliasSlots)

private def macroSpecs : List CompilationModel :=
  [ Contracts.SimpleStorage.spec
  , Contracts.Counter.spec
  , Contracts.Owned.spec
  , Contracts.Ledger.spec
  , Contracts.SafeCounter.spec
  , Contracts.OwnedCounter.spec
  , Contracts.SimpleToken.spec
  , Contracts.Vault.spec
  , Contracts.ERC20.spec
  , Contracts.ERC721.spec
  , Contracts.Smoke.UintMapSmoke.spec
  , Contracts.Smoke.Bytes32Smoke.spec
  , Contracts.Smoke.MappingWordSmoke.spec
  , Contracts.Smoke.StorageWordsSmoke.spec
  , Contracts.Smoke.CustomErrorSmoke.spec
  , Contracts.Smoke.StatelessSmoke.spec
  , Contracts.Smoke.ConstantSmoke.spec
  , Contracts.Smoke.TupleSmoke.spec
  , Contracts.Smoke.Uint8Smoke.spec
  , Contracts.Smoke.AddressHelpersSmoke.spec
  , Contracts.Smoke.ZeroAddressShadowSmoke.spec
  , Contracts.Smoke.StructMappingSmoke.spec
  ]

private structure FuzzRng where
  seed : Nat

private def fuzzMask64 : Nat := 2^64 - 1

private def fuzzNext (rng : FuzzRng) : FuzzRng × Nat :=
  let s := (rng.seed + 0x9e3779b97f4a7c15) &&& fuzzMask64
  let z := s
  let z := ((z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9) &&& fuzzMask64
  let z := ((z ^^^ (z >>> 27)) * 0x94d049bb133111eb) &&& fuzzMask64
  let z := z ^^^ (z >>> 31)
  ({ seed := s }, z)

private def fuzzEdgeValues : List Nat :=
  [0, 1, 2, 255, 256, 2^16 - 1, 2^128 - 1, 2^255, 2^256 - 1]

private def fuzzWord (rng : FuzzRng) : FuzzRng × Nat :=
  let (rng, n) := fuzzNext rng
  match fuzzEdgeValues[n % 16]? with
  | some v => (rng, v)
  | none =>
      let (rng, hi) := fuzzNext rng
      let (rng, lo) := fuzzNext rng
      (rng, ((hi &&& fuzzMask64) <<< 64) + (lo &&& fuzzMask64))

private def fuzzValueForType (ty : ParamType) (rng : FuzzRng) : FuzzRng × Nat :=
  let (rng, raw) := fuzzWord rng
  match ty with
  | .uint8 => (rng, raw % 256)
  | .address => (rng, raw % (2^160))
  | .bool => (rng, raw % 2)
  | _ => (rng, raw)

private def fuzzArgsForParams : List Param → FuzzRng → FuzzRng × List Nat
  | [], rng => (rng, [])
  | p :: rest, rng =>
      let (rng, arg) := fuzzValueForType p.ty rng
      let (rng, restArgs) := fuzzArgsForParams rest rng
      (rng, arg :: restArgs)

private def fuzzStorageEntries : List Nat → FuzzRng → FuzzRng × List (Nat × Nat)
  | [], rng => (rng, [])
  | slotIdx :: rest, rng =>
      let (rng, value) := fuzzWord rng
      let (rng, tail) := fuzzStorageEntries rest rng
      (rng, (slotIdx, value) :: tail)

private def storageOfEntries (entries : List (Nat × Nat)) : Nat → Nat :=
  fun slotIdx =>
    match entries.find? (fun entry => entry.1 == slotIdx) with
    | some (_, value) => value
    | none => 0

private def mappingKeySamples (sender : Nat) (args : List Nat) : List Nat :=
  (args ++ [0, 1, sender, 2^160 - 1, 2^256 - 1]).eraseDups

private def storageSlotSamples (spec : CompilationModel) : List Nat :=
  (canonicalFieldSlots spec ++ writeSlots spec ++ [0, 1, 2, 3, 4, 31, 32, 255]).eraseDups

private def mappingBaseSamples (spec : CompilationModel) : List Nat :=
  (writeSlots spec ++ canonicalFieldSlots spec ++ [0, 1, 2, 3]).eraseDups

private def sampledResultsMatch
    (slots : List Nat)
    (bases : List Nat)
    (keys : List Nat)
    (ir : IRResult)
    (yul : YulResult) : Bool :=
  ir.success == yul.success &&
  ir.returnValue == yul.returnValue &&
  ir.events == yul.events &&
  slots.all (fun slotIdx => ir.finalStorage slotIdx == yul.finalStorage slotIdx) &&
  bases.all (fun base => keys.all (fun key => ir.finalMappings base key == yul.finalMappings base key))

private def roundTripTrialsPerFunction : Nat := 1
private def roundTripFuelBudget : Nat := 512
private def roundTripInitialSeed : Nat := 0xC0DEC0DE

private def runRoundTripTrials
    (spec : CompilationModel)
    (irFn : IRFunction)
    (fn : FunctionSpec)
    (selector : Nat)
    (slots : List Nat)
    (bases : List Nat) :
    Nat → FuzzRng → IO FuzzRng
  | 0, rng => pure rng
  | trial + 1, rng => do
      let (rng, senderRaw) := fuzzWord rng
      let sender := senderRaw % (2^160)
      let (rng, args) := fuzzArgsForParams fn.params rng
      let (rng, storageEntries) := fuzzStorageEntries slots rng
      let initialState : IRState :=
        { vars := []
          «storage» := storageOfEntries storageEntries
          memory := fun _ => 0
          calldata := args
          returnValue := none
          sender := sender
          selector := selector
          events := [] }
      let irResult := execIRFunctionFuel roundTripFuelBudget irFn args initialState
      let stateWithParams := irFn.params.zip args |>.foldl
        (fun s (p, v) => s.setVar p.name v)
        initialState
      let yulState := yulStateOfIR selector stateWithParams
      let yulRollback := yulStateOfIR selector initialState
      let yulExec := execYulStmtsFuel roundTripFuelBudget yulState irFn.body
      let yulResult := yulResultOfExecWithRollback yulRollback yulExec
      let keys := mappingKeySamples sender args
      expectTrue
        s!"{spec.name}.{fn.name}: trial {trial + 1}"
        (sampledResultsMatch slots bases keys irResult yulResult)
      runRoundTripTrials spec irFn fn selector slots bases trial rng

private def checkRoundTripSpec (spec : CompilationModel) (rng : FuzzRng) : IO FuzzRng := do
  let extFns := externalFunctions spec
  let selectors ← Selector.computeSelectors spec
  let compileResult ← Selector.compileChecked spec selectors
  let ir ←
    match compileResult with
    | .ok ir =>
        pure ir
    | .error err =>
        throw (IO.userError s!"{spec.name}: compileChecked failed in round-trip fuzz harness: {err}")

  expectTrue
    s!"{spec.name}: function/selector alignment"
    (extFns.length == selectors.length)

  let slots := (storageSlotSamples spec).take 16
  let bases := (mappingBaseSamples spec).take 12
  let fnSelectors := List.zip extFns selectors
  let mut rng := rng
  for (fn, selector) in fnSelectors do
    let irFn ←
      match ir.functions.find? (fun f => f.selector == selector) with
      | some found =>
          pure found
      | none =>
          throw (IO.userError s!"{spec.name}.{fn.name}: missing compiled IR function for selector {Compiler.Hex.natToHex selector}")
    rng ← runRoundTripTrials spec irFn fn selector slots bases roundTripTrialsPerFunction rng
  IO.println s!"✓ {spec.name}: randomized IR/Yul function round-trip checks passed"
  pure rng

def main : IO Unit := do
  let mut rng : FuzzRng := { seed := roundTripInitialSeed }
  for spec in macroSpecs do
    rng ← checkRoundTripSpec spec rng
  IO.println "✓ macro round-trip fuzz harness passed"

end Compiler.MacroTranslateRoundTripFuzz

def main : IO Unit := Compiler.MacroTranslateRoundTripFuzz.main
