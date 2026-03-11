import Compiler.Proofs.IRGeneration.SupportedFragment
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.SelectorInteropHelpers
import Compiler.TypedIRCompilerCorrectness

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

/-- ABI parameter types admitted by the first whole-contract Layer 2 fragment.
Only single-head-word scalars are included for the initial generic theorem. -/
def SupportedExternalParamType : ParamType → Prop
  | .uint256 | .uint8 | .address | .bytes32 => True
  | _ => False

/-- Return profiles admitted by the first whole-contract Layer 2 fragment.
The initial theorem only targets zero-return or single-head-word-return entrypoints. -/
def SupportedExternalReturnProfile : List ParamType → Prop
  | [] => True
  | [ty] => SupportedExternalParamType ty
  | _ => False

/-- Selector-dispatched entrypoints in the same order used by `CompilationModel.compile`. -/
def selectorDispatchedFunctions (spec : CompilationModel) : List FunctionSpec :=
  spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)

/-- Parameter-profile interface for selector-dispatched entrypoints covered by the
current whole-contract theorem. -/
structure SupportedParamProfile (params : List Param) : Prop where
  namesNodup : (params.map (·.name)).Nodup
  supported : ∀ param ∈ params, SupportedExternalParamType param.ty

/-- Return-profile interface for selector-dispatched entrypoints covered by the
current whole-contract theorem. -/
structure SupportedReturnProfile (fn : FunctionSpec) : Prop where
  resolved :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns

/-- Expression forms intentionally outside the first generic whole-contract theorem.
These are contract-surface features that would otherwise keep proof burden in
client-side bridge theorems instead of compiler-structure lemmas. -/
def exprTouchesUnsupportedContractSurface : Expr → Bool
  | .literal _ | .param _ | .caller | .contractAddress
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .localVar _ => false
  | .storage _ | .storageAddr _ => true
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b =>
      exprTouchesUnsupportedContractSurface a || exprTouchesUnsupportedContractSurface b
  | .bitNot a | .logicalNot a => exprTouchesUnsupportedContractSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedContractSurface cond ||
        exprTouchesUnsupportedContractSurface thenVal ||
        exprTouchesUnsupportedContractSurface elseVal
  | .mapping _ _ | .mappingWord _ _ _ | .mappingPackedWord _ _ _ _
  | .mapping2 _ _ _ | .mapping2Word _ _ _ _ | .mappingUint _ _
  | .structMember _ _ _ | .structMember2 _ _ _ _
  | .constructorArg _ | .blobbasefee | .mload _ | .tload _ | .keccak256 _ _
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _
  | .calldatasize | .calldataload _ | .returndataSize | .extcodesize _
  | .returndataOptionalBoolAt _ | .externalCall _ _ | .internalCall _ _
  | .arrayLength _ | .arrayElement _ _ | .storageArrayLength _ | .storageArrayElement _ _
  | .mulDivDown _ _ _ | .mulDivUp _ _ _ | .shl _ _
  | .shr _ _ | .sdiv _ _ | .smod _ _ | .sar _ _ | .signextend _ _ | .sgt _ _ | .slt _ _ => true

mutual
  /-- Statement forms intentionally outside the first generic whole-contract theorem. -/
  def stmtTouchesUnsupportedContractSurface : Stmt → Bool
    | .letVar _ value | .assignVar _ value | .setStorage _ value =>
        exprTouchesUnsupportedContractSurface value
    | .setStorageAddr _ _ => true
    | .require cond _ | .return cond =>
        exprTouchesUnsupportedContractSurface cond
    | .mstore _ _ | .tstore _ _ => true
    | .stop => false
    | .ite _ _ _ => true
    | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
    | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
    | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
    | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _
    | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
    | .returnBytes _ | .returnStorageWords _ | .calldatacopy _ _ _
    | .returndataCopy _ _ _ | .revertReturndata | .forEach _ _ _
    | .emit _ _ | .internalCall _ _ | .internalCallAssign _ _ _
    | .rawLog _ _ _ | .externalCallBind _ _ _ | .ecm _ _ => true

  /-- List-level scan for unsupported whole-contract features. -/
  def stmtListTouchesUnsupportedContractSurface : List Stmt → Bool
    | [] => false
    | stmt :: rest =>
        stmtTouchesUnsupportedContractSurface stmt ||
          stmtListTouchesUnsupportedContractSurface rest
end

/-- Body-level interface for the initial theorem boundary. This keeps the current
syntactic exclusion scan local to the body-support witness instead of baking it
directly into the top-level `SupportedSpec` inventory. -/
structure SupportedBodyInterface (fields : List Field) (fn : FunctionSpec) : Prop where
  stmtList : SupportedStmtList fields fn.body
  surfaceClosed : stmtListTouchesUnsupportedContractSurface fn.body = false
  noLocalObligations : fn.localObligations = []

/-- Supported external function for the first whole-contract Layer 2 theorem.
This lifts the raw `SupportedStmtList` witness to the function boundary and
makes the whole-contract scope auditable without proof-internal inspection. -/
structure SupportedFunction (fields : List Field) (fn : FunctionSpec) : Prop where
  nonInternal : fn.isInternal = false
  nonSpecialEntrypoint : isInteropEntrypointName fn.name = false
  params : SupportedParamProfile fn.params
  returns : SupportedReturnProfile fn
  body : SupportedBodyInterface fields fn

/-- Whole-contract invariants that should remain global preconditions for the
current generic theorem, independent of feature-local proof interfaces. -/
structure SupportedSpecInvariants (spec : CompilationModel) (selectors : List Nat) : Prop where
  normalizedFields :
    applySlotAliasRanges spec.fields spec.slotAliasRanges = spec.fields
  noPackedFields :
    ∀ field ∈ spec.fields, field.packedBits = none
  selectorCount : selectors.length = (selectorDispatchedFunctions spec).length
  selectorsDistinct : firstDuplicateSelector selectors = none

/-- Whole-contract surfaces intentionally still outside the initial theorem,
kept separate from global normalization/dispatch invariants so future widening
can replace these by dedicated proof interfaces feature-by-feature. -/
structure SupportedSpecSurface (spec : CompilationModel) : Prop where
  noConstructor : spec.constructor = none
  noEvents : spec.events = []
  noErrors : spec.errors = []
  noExternals : spec.externals = []
  noFallback :
    ∀ fn ∈ spec.functions, fn.name != "fallback"
  noReceive :
    ∀ fn ∈ spec.functions, fn.name != "receive"

/-- Whole-contract support witness for the first generic Layer 2 theorem.
The initial scope is deliberately narrow: selector-dispatched external entrypoints only,
no constructor, no fallback/receive, no foreign/linking surface, and every function body
must already live inside the explicit supported statement fragment. -/
structure SupportedSpec (spec : CompilationModel) (selectors : List Nat) : Prop where
  invariants : SupportedSpecInvariants spec selectors
  surface : SupportedSpecSurface spec
  functions :
    ∀ fn, fn ∈ spec.functions → SupportedFunction spec.fields fn

theorem SupportedFunction.paramNamesNodup
    {fields : List Field} {fn : FunctionSpec}
    (hSupported : SupportedFunction fields fn) :
    (fn.params.map (·.name)).Nodup :=
  hSupported.params.namesNodup

theorem SupportedFunction.paramsSupported
    {fields : List Field} {fn : FunctionSpec}
    (hSupported : SupportedFunction fields fn) :
    ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
  hSupported.params.supported

theorem SupportedFunction.returnsSupported
    {fields : List Field} {fn : FunctionSpec}
    (hSupported : SupportedFunction fields fn) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  hSupported.returns.resolved

theorem SupportedSpec.normalizedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    applySlotAliasRanges spec.fields spec.slotAliasRanges = spec.fields :=
  hSupported.invariants.normalizedFields

theorem SupportedSpec.noPackedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ field ∈ spec.fields, field.packedBits = none :=
  hSupported.invariants.noPackedFields

theorem SupportedSpec.selectorCount
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    selectors.length = (selectorDispatchedFunctions spec).length :=
  hSupported.invariants.selectorCount

theorem SupportedSpec.selectorsDistinct
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    firstDuplicateSelector selectors = none :=
  hSupported.invariants.selectorsDistinct

theorem SupportedSpec.noConstructor
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.constructor = none :=
  hSupported.surface.noConstructor

theorem SupportedSpec.noEvents
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.events = [] :=
  hSupported.surface.noEvents

theorem SupportedSpec.noErrors
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.errors = [] :=
  hSupported.surface.noErrors

theorem SupportedSpec.noExternals
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.externals = [] :=
  hSupported.surface.noExternals

theorem SupportedSpec.noFallback
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn ∈ spec.functions, fn.name != "fallback" :=
  hSupported.surface.noFallback

theorem SupportedSpec.noReceive
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn ∈ spec.functions, fn.name != "receive" :=
  hSupported.surface.noReceive

theorem SupportedSpec.supportedFunctionOfSelectorDispatched
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedFunction spec.fields fn := by
  have hfiltered : fn ∈ spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name) := by
    simpa [selectorDispatchedFunctions] using hfn
  have hmem : fn ∈ spec.functions := (List.mem_filter.mp hfiltered).1
  exact hSupported.functions fn hmem

theorem SupportedSpec.selectorFunctionParamsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).paramsSupported

theorem SupportedSpec.selectorFunctionParamNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    (fn.params.map (·.name)).Nodup :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).paramNamesNodup

theorem SupportedSpec.selectorFunctionBodySupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedStmtList spec.fields fn.body :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).body.stmtList

theorem SupportedSpec.selectorFunctionReturnsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).returnsSupported

@[simp] theorem stmtListTouchesUnsupportedContractSurface_nil :
    stmtListTouchesUnsupportedContractSurface [] = false := rfl

@[simp] theorem exprTouchesUnsupportedContractSurface_storage
    (field : String) :
    exprTouchesUnsupportedContractSurface (.storage field) = true := rfl

@[simp] theorem exprTouchesUnsupportedContractSurface_storageAddr
    (field : String) :
    exprTouchesUnsupportedContractSurface (.storageAddr field) = true := rfl

@[simp] theorem stmtTouchesUnsupportedContractSurface_storageArrayPush
    (field : String) (value : Expr) :
    stmtTouchesUnsupportedContractSurface (.storageArrayPush field value) = true := rfl

@[simp] theorem stmtTouchesUnsupportedContractSurface_mstore
    (offset value : Expr) :
    stmtTouchesUnsupportedContractSurface (.mstore offset value) = true := rfl

@[simp] theorem stmtTouchesUnsupportedContractSurface_setStorageAddr
    (field : String) (value : Expr) :
    stmtTouchesUnsupportedContractSurface (.setStorageAddr field value) = true := rfl

@[simp] theorem stmtTouchesUnsupportedContractSurface_ite
    (cond : Expr) (thenBranch elseBranch : List Stmt) :
    stmtTouchesUnsupportedContractSurface (.ite cond thenBranch elseBranch) = true := rfl

@[simp] theorem stmtTouchesUnsupportedContractSurface_tstore
    (offset value : Expr) :
    stmtTouchesUnsupportedContractSurface (.tstore offset value) = true := rfl

@[simp] theorem stmtTouchesUnsupportedContractSurface_storageArrayPop
    (field : String) :
    stmtTouchesUnsupportedContractSurface (.storageArrayPop field) = true := rfl

@[simp] theorem stmtTouchesUnsupportedContractSurface_setStorageArrayElement
    (field : String) (index value : Expr) :
    stmtTouchesUnsupportedContractSurface (.setStorageArrayElement field index value) = true := rfl

@[simp] theorem selectorDispatchedFunctions_nil :
    selectorDispatchedFunctions
      { name := "Empty", fields := [], reservedSlotRanges := [], slotAliasRanges := [],
        constructor := none, functions := [], events := [], errors := [], externals := [] } = [] := rfl

def counterSupportedSpecModel : CompilationModel :=
  { name := "Counter"
    fields := []
    constructor := none
    functions :=
      [ { name := "getCount"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.literal 42)] } ] }

private theorem counter_noPackedFields :
    ∀ field ∈ counterSupportedSpecModel.fields, field.packedBits = none := by
  intro field hfield
  simp [counterSupportedSpecModel] at hfield

private theorem counter_noFallback :
    ∀ fn ∈ counterSupportedSpecModel.functions, fn.name != "fallback" := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  rcases hfn with rfl <;> decide

private theorem counter_noReceive :
    ∀ fn ∈ counterSupportedSpecModel.functions, fn.name != "receive" := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  rcases hfn with rfl <;> decide

private theorem counter_supported_function :
    ∀ fn, fn ∈ counterSupportedSpecModel.functions →
      SupportedFunction counterSupportedSpecModel.fields fn := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  rcases hfn with rfl
  refine
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      params :=
        { namesNodup := by decide
          supported := by intro param hparam; cases hparam }
      returns := { resolved := ⟨[.uint256], rfl, trivial⟩ }
      body :=
        { stmtList := by
            refine ⟨[Verity.Core.Free.SupportedStmtFragment.requireClausesThenReturnLiteral [] 42], ?_⟩
            simp [Verity.Core.Free.supportedStmtFragmentsToStmts,
              Verity.Core.Free.SupportedStmtFragment.toStmts,
              Verity.Core.Free.RequireFamilyClausesTailProgram.toStmts,
              Verity.Core.Free.RequireFamilyClausesTail.toStmts]
          surfaceClosed := by decide
          noLocalObligations := rfl } }

theorem counter_supported_spec : SupportedSpec counterSupportedSpecModel
    [0xa87d942c] := by
  refine
    { invariants :=
        { normalizedFields := by
            rfl
          noPackedFields := counter_noPackedFields
          selectorCount := by
            decide
          selectorsDistinct := by
            decide }
      surface :=
        { noConstructor := rfl
          noEvents := rfl
          noErrors := rfl
          noExternals := rfl
          noFallback := counter_noFallback
          noReceive := counter_noReceive }
      functions := counter_supported_function }

def simpleStorageSupportedSpecModel : CompilationModel :=
  { name := "SimpleStorage"
    fields := []
    constructor := none
    functions :=
      [ { name := "retrieve"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.literal 11)] } ] }

theorem simpleStorage_supported_spec : SupportedSpec simpleStorageSupportedSpecModel
    [0x2e64cec1] := by
  refine
    { invariants :=
        { normalizedFields := by
            rfl
          noPackedFields := by
            intro field hfield
            simp [simpleStorageSupportedSpecModel] at hfield
          selectorCount := by
            decide
          selectorsDistinct := by
            decide }
      surface :=
        { noConstructor := rfl
          noEvents := rfl
          noErrors := rfl
          noExternals := rfl
          noFallback := by
            intro fn hfn
            simp [simpleStorageSupportedSpecModel] at hfn
            rcases hfn with rfl <;> decide
          noReceive := by
            intro fn hfn
            simp [simpleStorageSupportedSpecModel] at hfn
            rcases hfn with rfl <;> decide }
      functions := ?_ }
  intro fn hfn
  simp [simpleStorageSupportedSpecModel] at hfn
  rcases hfn with rfl
  refine
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      params :=
        { namesNodup := by decide
          supported := by intro param hparam; cases hparam }
      returns := { resolved := ⟨[.uint256], rfl, trivial⟩ }
      body :=
        { stmtList := by
            refine ⟨[Verity.Core.Free.SupportedStmtFragment.requireClausesThenReturnLiteral [] 11], ?_⟩
            simp [Verity.Core.Free.supportedStmtFragmentsToStmts,
              Verity.Core.Free.SupportedStmtFragment.toStmts,
              Verity.Core.Free.RequireFamilyClausesTailProgram.toStmts,
              Verity.Core.Free.RequireFamilyClausesTail.toStmts]
          surfaceClosed := by decide
          noLocalObligations := rfl } }

end Compiler.Proofs.IRGeneration
