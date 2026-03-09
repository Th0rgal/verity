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

/-- Expression forms intentionally outside the first generic whole-contract theorem.
These are contract-surface features that would otherwise keep proof burden in
client-side bridge theorems instead of compiler-structure lemmas. -/
def exprTouchesUnsupportedContractSurface : Expr → Bool
  | .literal _ | .param _ | .storage _ | .storageAddr _ | .caller | .contractAddress
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .localVar _ => false
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .lt a b | .le a b
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
  | .arrayLength _ | .arrayElement _ _ | .mulDivDown _ _ _ | .mulDivUp _ _ _ | .shl _ _
  | .shr _ _ => true

mutual
  /-- Statement forms intentionally outside the first generic whole-contract theorem. -/
  def stmtTouchesUnsupportedContractSurface : Stmt → Bool
    | .letVar _ value | .assignVar _ value | .setStorage _ value | .setStorageAddr _ value =>
        exprTouchesUnsupportedContractSurface value
    | .require cond _ | .return cond =>
        exprTouchesUnsupportedContractSurface cond
    | .mstore offset value | .tstore offset value =>
        exprTouchesUnsupportedContractSurface offset ||
          exprTouchesUnsupportedContractSurface value
    | .stop => false
    | .ite cond thenBranch elseBranch =>
        exprTouchesUnsupportedContractSurface cond ||
          stmtListTouchesUnsupportedContractSurface thenBranch ||
          stmtListTouchesUnsupportedContractSurface elseBranch
    | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
    | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
    | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
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

/-- Supported external function for the first whole-contract Layer 2 theorem.
This lifts the raw `SupportedStmtList` witness to the function boundary and
makes the whole-contract scope auditable without proof-internal inspection. -/
structure SupportedFunction (fields : List Field) (fn : FunctionSpec) : Prop where
  nonInternal : fn.isInternal = false
  nonSpecialEntrypoint : isInteropEntrypointName fn.name = false
  params : ∀ param ∈ fn.params, SupportedExternalParamType param.ty
  returns :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns
  body : SupportedStmtList fields fn.body
  bodySurface : stmtListTouchesUnsupportedContractSurface fn.body = false
  noLocalObligations : fn.localObligations = []

/-- Whole-contract support witness for the first generic Layer 2 theorem.
The initial scope is deliberately narrow: selector-dispatched external entrypoints only,
no constructor, no fallback/receive, no foreign/linking surface, and every function body
must already live inside the explicit supported statement fragment. -/
structure SupportedSpec (spec : CompilationModel) (selectors : List Nat) : Prop where
  normalizedFields :
    applySlotAliasRanges spec.fields spec.slotAliasRanges = spec.fields
  noPackedFields :
    ∀ field ∈ spec.fields, field.packedBits = none
  noConstructor : spec.constructor = none
  noEvents : spec.events = []
  noErrors : spec.errors = []
  noExternals : spec.externals = []
  noFallback :
    ∀ fn ∈ spec.functions, fn.name != "fallback"
  noReceive :
    ∀ fn ∈ spec.functions, fn.name != "receive"
  selectorCount : selectors.length = (selectorDispatchedFunctions spec).length
  selectorsDistinct : firstDuplicateSelector selectors = none
  functions :
    ∀ fn, fn ∈ spec.functions → SupportedFunction spec.fields fn

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
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params

theorem SupportedSpec.selectorFunctionBodySupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedStmtList spec.fields fn.body :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).body

theorem SupportedSpec.selectorFunctionReturnsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).returns

@[simp] theorem stmtListTouchesUnsupportedContractSurface_nil :
    stmtListTouchesUnsupportedContractSurface [] = false := rfl

@[simp] theorem selectorDispatchedFunctions_nil :
    selectorDispatchedFunctions
      { name := "Empty", fields := [], reservedSlotRanges := [], slotAliasRanges := [],
        constructor := none, functions := [], events := [], errors := [], externals := [] } = [] := rfl

def counterSupportedSpecModel : CompilationModel :=
  { name := "Counter"
    fields := Verity.Core.Free.counterFields
    constructor := none
    functions :=
      [ { name := "increment"
          params := []
          returnType := none
          body :=
            [ Stmt.letVar "current" (Expr.storage "count")
            , Stmt.setStorage "count" (Expr.add (Expr.localVar "current") (Expr.literal 1))
            , Stmt.stop ] }
      , { name := "decrement"
          params := []
          returnType := none
          body :=
            [ Stmt.letVar "current" (Expr.storage "count")
            , Stmt.setStorage "count" (Expr.sub (Expr.localVar "current") (Expr.literal 1))
            , Stmt.stop ] }
      , { name := "getCount"
          params := []
          returnType := some .uint256
          body :=
            [ Stmt.letVar "current" (Expr.storage "count")
            , Stmt.return (Expr.localVar "current") ] } ] }

private theorem counter_noPackedFields :
    ∀ field ∈ counterSupportedSpecModel.fields, field.packedBits = none := by
  intro field hfield
  simp [counterSupportedSpecModel, Verity.Core.Free.counterFields] at hfield
  cases hfield
  rfl

private theorem counter_noFallback :
    ∀ fn ∈ counterSupportedSpecModel.functions, fn.name != "fallback" := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  rcases hfn with rfl | rfl | rfl <;> decide

private theorem counter_noReceive :
    ∀ fn ∈ counterSupportedSpecModel.functions, fn.name != "receive" := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  rcases hfn with rfl | rfl | rfl <;> decide

private theorem counter_supported_function :
    ∀ fn, fn ∈ counterSupportedSpecModel.functions →
      SupportedFunction counterSupportedSpecModel.fields fn := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  rcases hfn with rfl | rfl | rfl
  · refine
      { nonInternal := rfl
        nonSpecialEntrypoint := rfl
        params := by intro param hparam; cases hparam
        returns := ⟨[], rfl, trivial⟩
        body := Verity.Core.Free.counter_increment_supported
        bodySurface := by decide
        noLocalObligations := rfl }
  · refine
      { nonInternal := rfl
        nonSpecialEntrypoint := rfl
        params := by intro param hparam; cases hparam
        returns := ⟨[], rfl, trivial⟩
        body := Verity.Core.Free.counter_decrement_supported
        bodySurface := by decide
        noLocalObligations := rfl }
  · refine
      { nonInternal := rfl
        nonSpecialEntrypoint := rfl
        params := by intro param hparam; cases hparam
        returns := ⟨[.uint256], rfl, trivial⟩
        body := Verity.Core.Free.counter_getCount_supported
        bodySurface := by decide
        noLocalObligations := rfl }

theorem counter_supported_spec : SupportedSpec counterSupportedSpecModel
    [0xd09de08a, 0x2baeceb7, 0xa87d942c] := by
  refine
    { normalizedFields := by
        rfl
      noPackedFields := counter_noPackedFields
      noConstructor := rfl
      noEvents := rfl
      noErrors := rfl
      noExternals := rfl
      noFallback := counter_noFallback
      noReceive := counter_noReceive
      selectorCount := by
        decide
      selectorsDistinct := by
        decide
      functions := counter_supported_function }

def simpleStorageSupportedSpecModel : CompilationModel :=
  { name := "SimpleStorage"
    fields := Verity.Core.Free.simpleStorageFields
    constructor := none
    functions :=
      [ { name := "retrieve"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.storage "storedData")] } ] }

theorem simpleStorage_supported_spec : SupportedSpec simpleStorageSupportedSpecModel
    [0x2e64cec1] := by
  refine
    { normalizedFields := by
        rfl
      noPackedFields := by
        intro field hfield
        simp [simpleStorageSupportedSpecModel, Verity.Core.Free.simpleStorageFields] at hfield
        cases hfield
        rfl
      noConstructor := rfl
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
        rcases hfn with rfl <;> decide
      selectorCount := by
        decide
      selectorsDistinct := by
        decide
      functions := ?_ }
  intro fn hfn
  simp [simpleStorageSupportedSpecModel] at hfn
  rcases hfn with rfl
  refine
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      params := by intro param hparam; cases hparam
      returns := ⟨[.uint256], rfl, trivial⟩
      body := Verity.Core.Free.simpleStorage_retrieve_supported
      bodySurface := by decide
      noLocalObligations := rfl }

end Compiler.Proofs.IRGeneration
