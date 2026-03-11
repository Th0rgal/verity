/- 
  Compiler.CompilationModel.Dispatch: Contract assembly and entrypoint wiring

  This module builds IR functions, constructor code, and whole contracts from
  the lower-level statement/expression compilation helpers.
-/
import Compiler.CompilationModel.Compile
import Compiler.CompilationModel.ParamLoading

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

private def pickFreshInternalRetName (usedNames : List String) (idx : Nat) : String :=
  pickFreshName s!"__ret{idx}" usedNames

private def freshInternalRetNames (returns : List ParamType) (usedNames : List String) : List String :=
  let (_, namesRev) := returns.zipIdx.foldl
    (fun (acc : List String × List String) (_retTy, idx) =>
      let (used, names) := acc
      let fresh := pickFreshInternalRetName used idx
      (fresh :: used, fresh :: names))
    (usedNames, [])
  namesRev.reverse

-- Compile internal function to a Yul function definition (#181)
def compileInternalFunction (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (spec : FunctionSpec) :
    Except String YulStmt := do
  validateFunctionSpec spec
  let returns ← functionReturns spec
  let paramNames := spec.params.map (·.name)
  let usedNames := paramNames ++ collectStmtListBindNames spec.body
  let retNames := freshInternalRetNames returns usedNames
  let bodyStmts ← compileStmtList fields events errors .calldata retNames true
    (paramNames ++ retNames) spec.body
  pure (YulStmt.funcDef (internalFunctionYulName spec.name) paramNames retNames bodyStmts)

-- Compile function spec to IR function
def compileFunctionSpec (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) :
    Except String IRFunction := do
  validateFunctionSpec spec
  let returns ← functionReturns spec
  let paramLoads := genParamLoads spec.params
  let bodyStmts ← compileStmtList fields events errors .calldata [] false
    (spec.params.map (·.name)) spec.body
  let allStmts := paramLoads ++ bodyStmts
  let retType := match returns with
    | [single] => single.toIRType
    | _ => IRType.unit
  return {
    name := spec.name
    selector := selector
    params := spec.params.map Param.toIRParam
    ret := retType
    payable := spec.isPayable
    body := allStmts
  }

private def compileSpecialEntrypoint (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (spec : FunctionSpec) :
    Except String IREntrypoint := do
  let bodyChunks ← compileStmtList fields events errors .calldata [] false [] spec.body
  pure {
    payable := spec.isPayable
    body := bodyChunks
  }

def pickUniqueFunctionByName (name : String) (funcs : List FunctionSpec) :
    Except String (Option FunctionSpec) :=
  match funcs.filter (·.name == name) with
  | [] => pure none
  | [single] => pure (some single)
  | _ => throw s!"Compilation error: multiple '{name}' entrypoints are not allowed ({issue586Ref})"

-- Check if contract uses mappings
def usesMapping (fields : List Field) : Bool :=
  fields.any fun f => isMapping fields f.name

-- Compile deploy code (constructor)
-- Note: Don't append datacopy/return here - Codegen.deployCode does that
def compileConstructor (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (ctor : Option ConstructorSpec) :
    Except String (List YulStmt) := do
  match ctor with
  | none => return []
  | some spec =>
    let argLoads := genConstructorArgLoads spec.params
    let bodyChunks ← compileStmtList fields events errors .memory [] false [] spec.body
    return argLoads ++ bodyChunks

-- Main compilation function
-- NOTE: this is the pure core compiler and does *not* verify canonical
-- selector/signature correspondence (it only checks count/duplicates).
-- Use `Compiler.Selector.compileChecked` on caller-provided selector lists.
-- WARNING: Order matters! If selector list is reordered but function list isn't,
-- functions will be mapped to wrong selectors with no runtime error.
def validateCompileInputs (spec : CompilationModel) (selectors : List Nat) : Except String Unit := do
  validateIdentifierShapes spec
  match firstInvalidSlotAliasRange spec.slotAliasRanges with
  | some (idx, range) =>
      throw s!"Compilation error: slotAliasRanges[{idx}] has invalid source interval {range.sourceStart}..{range.sourceEnd} in {spec.name} ({issue623Ref}). slotAliasRanges require sourceStart <= sourceEnd."
  | none =>
      pure ()
  match firstSlotAliasSourceOverlap spec.slotAliasRanges with
  | some (idxA, a, idxB, b) =>
      throw s!"Compilation error: slotAliasRanges[{idxA}]={a.sourceStart}..{a.sourceEnd} and slotAliasRanges[{idxB}]={b.sourceStart}..{b.sourceEnd} overlap in source slots in {spec.name} ({issue623Ref}). Ensure slotAliasRanges source intervals are disjoint."
  | none =>
      pure ()
  let fields := applySlotAliasRanges spec.fields spec.slotAliasRanges
  let externalFns := spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)
  match firstInternalDynamicParam spec.functions with
  | some (fnName, paramName, ty) =>
      throw s!"Compilation error: internal function '{fnName}' parameter '{paramName}' has dynamic type {repr ty}, which is currently unsupported ({issue753Ref}). Internal dynamic ABI lowering is not implemented yet."
  | none =>
      pure ()
  match firstDuplicateFunctionParamName spec.functions with
  | some (fnName, dup) =>
      throw s!"Compilation error: duplicate parameter name '{dup}' in function '{fnName}'"
  | none =>
      pure ()
  match firstDuplicateConstructorParamName spec.constructor with
  | some dup =>
      throw s!"Compilation error: duplicate parameter name '{dup}' in constructor"
  | none =>
      pure ()
  for fn in spec.functions do
    validateFunctionSpec fn
    validateInteropFunctionSpec fn
    validateSpecialEntrypointSpec fn
    validateEventArgShapesInFunction fn spec.events
    validateCustomErrorArgShapesInFunction fn spec.errors
    validateInternalCallShapesInFunction spec.functions fn
    validateExternalCallTargetsInFunction spec.externals fn
  validateConstructorSpec spec.constructor
  validateInteropConstructorSpec spec.constructor
  validateExternalCallTargetsInConstructor spec.externals spec.constructor
  match spec.constructor with
  | none => pure ()
  | some ctor => do
      ctor.body.forM (validateEventArgShapesInStmt "constructor" ctor.params spec.events)
      ctor.body.forM (validateCustomErrorArgShapesInStmt "constructor" ctor.params spec.errors)
      ctor.body.forM (validateInternalCallShapesInStmt spec.functions "constructor")
  for ext in spec.externals do
    let _ ← externalFunctionReturns ext
    validateInteropExternalSpec ext
  match firstDuplicateName (spec.functions.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate function name '{dup}' in {spec.name}"
  | none =>
      pure ()
  match firstDuplicateName (spec.errors.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate custom error declaration '{dup}'"
  | none =>
      pure ()
  match firstDuplicateName (spec.fields.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate field name '{dup}' in {spec.name}"
  | none =>
      pure ()
  match firstInvalidPackedBits spec.fields with
  | some (fieldName, packed) =>
      throw s!"Compilation error: field '{fieldName}' has invalid packedBits offset={packed.offset} width={packed.width} in {spec.name} ({issue623Ref}). Require 0 < width <= 256, offset < 256, and offset + width <= 256."
  | none =>
      pure ()
  match firstMappingPackedBits spec.fields with
  | some fieldName =>
      throw s!"Compilation error: field '{fieldName}' is a mapping and cannot declare packedBits in {spec.name} ({issue623Ref}). Packed subfields are only supported for value-word fields."
  | none =>
      pure ()
  match firstUnsupportedStorageArrayElemType spec.fields with
  | some (fieldName, elemType) =>
      throw s!"Compilation error: field '{fieldName}' uses unsupported storage dynamic array element type {repr elemType} in {spec.name} ({issue1571Ref}). This incremental lowering currently supports only one-storage-word elements (uint256, address, bytes32)."
  | none =>
      pure ()
  firstInvalidStructField spec.fields
  match firstFieldWriteSlotConflict fields with
  | some (slot, existingField, conflictingField) =>
      throw s!"Compilation error: storage slot {slot} has overlapping write ranges for '{existingField}' and '{conflictingField}' in {spec.name} ({issue623Ref}). Ensure full-slot writes are unique and packed bit ranges are disjoint per slot."
  | none =>
      pure ()
  match firstInvalidReservedRange spec.reservedSlotRanges with
  | some (idx, range) =>
      throw s!"Compilation error: reservedSlotRanges[{idx}] has invalid interval {range.start}..{range.end_} in {spec.name} ({issue623Ref}). Reserved slot range start must be <= end."
  | none =>
      pure ()
  match firstReservedRangeOverlap spec.reservedSlotRanges with
  | some (idxA, a, idxB, b) =>
      throw s!"Compilation error: reserved slot ranges reservedSlotRanges[{idxA}]={a.start}..{a.end_} and reservedSlotRanges[{idxB}]={b.start}..{b.end_} overlap in {spec.name} ({issue623Ref}). Ensure reserved ranges are disjoint."
  | none =>
      pure ()
  match firstReservedSlotWriteConflict fields spec.reservedSlotRanges with
  | some (slot, ownerName, rangeIdx, range) =>
      throw s!"Compilation error: field write slot {slot} ('{ownerName}') overlaps reservedSlotRanges[{rangeIdx}]={range.start}..{range.end_} in {spec.name} ({issue623Ref}). Adjust field slot/aliasSlots or reservedSlotRanges."
  | none =>
      pure ()
  match firstDuplicateName (spec.events.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate event name '{dup}' in {spec.name}"
  | none =>
      pure ()
  for eventDef in spec.events do
    validateEventDef eventDef
  match firstDuplicateEventParamName spec.events with
  | some (evName, dup) =>
      throw s!"Compilation error: duplicate parameter name '{dup}' in event '{evName}'"
  | none =>
      pure ()
  match firstDuplicateName (spec.externals.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate external declaration '{dup}' in {spec.name}"
  | none =>
      pure ()
  let mappingHelpersRequired := usesMapping fields
  let arrayHelpersRequired := contractUsesArrayElement spec
  let dynamicBytesEqHelpersRequired := contractUsesDynamicBytesEq spec
  match firstReservedExternalCollision
      spec mappingHelpersRequired arrayHelpersRequired dynamicBytesEqHelpersRequired with
  | some name =>
      if name.startsWith internalFunctionPrefix then
        throw s!"Compilation error: external declaration '{name}' uses reserved prefix '{internalFunctionPrefix}' ({issue756Ref})."
      else
        throw s!"Compilation error: external declaration '{name}' collides with compiler-generated/reserved symbol '{name}' ({issue756Ref}). Rename the external wrapper."
  | none =>
      pure ()
  for err in spec.errors do
    validateErrorDef err
  if externalFns.length != selectors.length then
    throw s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {externalFns.length} external functions"
  match firstDuplicateSelector selectors with
  | some dup =>
      let names := selectorNames spec selectors dup
      let nameStr := if names.isEmpty then "<unknown>" else String.intercalate ", " names
      throw s!"Selector collision in {spec.name}: {dup} assigned to {nameStr}"
  | none => pure ()

def compileValidatedCore (spec : CompilationModel) (selectors : List Nat) : Except String IRContract := do
  let fields := applySlotAliasRanges spec.fields spec.slotAliasRanges
  let externalFns := spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)
  let internalFns := spec.functions.filter (·.isInternal)
  let mappingHelpersRequired := usesMapping fields
  let arrayHelpersRequired := contractUsesArrayElement spec
  let dynamicBytesEqHelpersRequired := contractUsesDynamicBytesEq spec
  let fallbackSpec ← pickUniqueFunctionByName "fallback" spec.functions
  let receiveSpec ← pickUniqueFunctionByName "receive" spec.functions
  let functions ← (externalFns.zip selectors).mapM fun (fnSpec, sel) =>
    compileFunctionSpec fields spec.events spec.errors sel fnSpec
  let internalFuncDefs ← internalFns.mapM (compileInternalFunction fields spec.events spec.errors)
  let arrayElementHelpers :=
    if arrayHelpersRequired then
      [checkedArrayElementCalldataHelper, checkedArrayElementMemoryHelper]
    else
      []
  let dynamicBytesEqHelpers :=
    if dynamicBytesEqHelpersRequired then
      [dynamicBytesEqCalldataHelper, dynamicBytesEqMemoryHelper]
    else
      []
  let fallbackEntrypoint ← fallbackSpec.mapM (compileSpecialEntrypoint fields spec.events spec.errors)
  let receiveEntrypoint ← receiveSpec.mapM (compileSpecialEntrypoint fields spec.events spec.errors)
  return {
    name := spec.name
    deploy := (← compileConstructor fields spec.events spec.errors spec.constructor)
    constructorPayable := spec.constructor.map (·.isPayable) |>.getD false
    functions := functions
    fallbackEntrypoint := fallbackEntrypoint
    receiveEntrypoint := receiveEntrypoint
    usesMapping := mappingHelpersRequired
    internalFunctions := arrayElementHelpers ++ dynamicBytesEqHelpers ++ internalFuncDefs
  }

def compile (spec : CompilationModel) (selectors : List Nat) : Except String IRContract := do
  validateCompileInputs spec selectors
  compileValidatedCore spec selectors

end Compiler.CompilationModel
