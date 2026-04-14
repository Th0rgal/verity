import Compiler.Proofs.IRGeneration.Contract
import Compiler.Proofs.MappingSlot

namespace Compiler.Proofs.IRGeneration.ContractFeatureTest

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration

private def literalMappingWriteFunction : FunctionSpec :=
  { name := "setFive"
    params := [{ name := "value", ty := .uint256 }]
    returnType := none
    body := [Stmt.setMapping "balances" (.literal 5) (.param "value"), .stop] }

private def literalMappingWriteSpec : CompilationModel :=
  { name := "LiteralMappingWrite"
    fields := [{ name := "balances", ty := .mappingTyped (.simple .uint256), slot := some 7 }]
    constructor := none
    functions := [literalMappingWriteFunction] }

private def literalMappingWriteSelector : Nat := 0x11111111

private theorem literalMappingWrite_noPackedFields :
    ∀ field ∈ literalMappingWriteSpec.fields, field.packedBits = none := by
  intro field hfield
  simp [literalMappingWriteSpec] at hfield
  rcases hfield with rfl
  rfl

private theorem literalMappingWrite_noFallback :
    ∀ fn ∈ literalMappingWriteSpec.functions, fn.name != "fallback" := by
  intro fn hfn
  simp [literalMappingWriteSpec] at hfn
  rcases hfn with rfl
  decide

private theorem literalMappingWrite_noReceive :
    ∀ fn ∈ literalMappingWriteSpec.functions, fn.name != "receive" := by
  intro fn hfn
  simp [literalMappingWriteSpec] at hfn
  rcases hfn with rfl
  decide

private def literalMappingWrite_supported_function :
    ∀ fn, fn ∈ literalMappingWriteSpec.functions →
      SupportedFunctionExceptMappingWrites literalMappingWriteSpec fn := by
  intro fn hfn
  simp [literalMappingWriteSpec] at hfn
  rcases hfn with rfl
  exact
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      params :=
        { namesNodup := by decide
          supported := by
            intro param hparam
            rcases (by simpa [literalMappingWriteFunction] using hparam : param = { name := "value", ty := .uint256 }) with rfl
            trivial }
      returns := { resolved := ⟨[], rfl, trivial⟩ }
      body :=
        { stmtList :=
            .append
              (.setMappingSingle
                (.literal 5)
                (by simp [FunctionBody.exprBoundNamesInScope, FunctionBody.exprBoundNames])
                (.param "value")
                (by
                  intro name hname
                  simp [FunctionBody.exprBoundNames, literalMappingWriteFunction] at hname ⊢
                  aesop)
                rfl)
              (.terminalCore (.stop .nil))
          core := { surfaceClosed := by decide }
          state := { surfaceClosed := by decide }
          calls :=
            { helpers :=
                { helperRank := 0
                  callNamesNodup := helperCallNames_nodup _
                  summaryOf := by
                    intro calleeName hmem
                    exfalso
                    simpa [literalMappingWriteFunction, helperCallNames,
                      stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
                      exprInternalHelperCallNames] using hmem
                  calleeRanksDecrease := by
                    intro calleeName hmem
                    exfalso
                    simpa [literalMappingWriteFunction, helperCallNames,
                      stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
                      exprInternalHelperCallNames] using hmem
                  exprCallsPreserveWorld := by
                    intro calleeName hmem
                    exfalso
                    simpa [literalMappingWriteFunction, exprHelperCallNames,
                      stmtListExprHelperCallNames, stmtExprHelperCallNames,
                      exprInternalHelperCallNames] using hmem }
              foreign := by decide
              lowLevel := by decide }
          effects := { surfaceClosed := by decide }
          noLocalObligations := rfl } }

private def literalMappingWrite_supported_spec :
    SupportedSpecExceptMappingWrites literalMappingWriteSpec [literalMappingWriteSelector] :=
  { invariants :=
      { normalizedFields := rfl
        noPackedFields := literalMappingWrite_noPackedFields
        selectorCount := by decide
        selectorsDistinct := by decide
        functionNamesNodup := by decide }
    surface :=
      { noConstructor := rfl
        noEvents := rfl
        noErrors := rfl
        noExternals := rfl
        noFallback := literalMappingWrite_noFallback
        noReceive := literalMappingWrite_noReceive }
    functions := literalMappingWrite_supported_function }

private theorem literalMappingWrite_noConflict :
    firstFieldWriteSlotConflict literalMappingWriteSpec.fields = none := by
  native_decide

private def literalMappingWriteTx : IRTransaction :=
  { sender := 9
    functionSelector := literalMappingWriteSelector
    args := [23] }

private def constructorOnlyCtor : ConstructorSpec :=
  { params := [{ name := "initialOwner", ty := .address }]
    body := [Stmt.setStorageAddr "owner" (.param "initialOwner"), .stop] }

private def constructorBodyFunction : FunctionSpec :=
  constructorAsFunctionSpec constructorOnlyCtor

private def constructorOnlyOwnerField : Field :=
  { name := "owner", ty := .address }

private def constructorOnlySpec : CompilationModel :=
  { name := "ConstructorOnly"
    fields := [constructorOnlyOwnerField]
    constructor := some constructorOnlyCtor
    functions := [] }

private theorem constructorOnly_owner_resolved :
    findFieldWithResolvedSlot constructorOnlySpec.fields "owner" =
      some ({ name := "owner", ty := FieldType.address }, 0) := by
  rfl

private def constructorOnlySupported :
    SupportedConstructor constructorOnlySpec constructorOnlyCtor :=
  { params :=
      { namesNodup := by decide
        supported := by
          intro param hparam
          simp [constructorOnlyCtor] at hparam
          rcases hparam with rfl
          trivial }
    body :=
      { stmtList :=
          .append
            (.setStorageAddrSingleSlot
              (fieldName := "owner")
              (slot := 0)
              (.param "initialOwner")
              (by
                intro name hname
                simpa [FunctionBody.exprBoundNamesInScope, FunctionBody.exprBoundNames,
                  constructorAsFunctionSpec, constructorOnlyCtor] using hname)
              (by
                simpa [constructorOnlySpec, constructorOnlyOwnerField] using
                  (findFieldWithResolvedSlot_cons constructorOnlyOwnerField [] "owner")))
            (.terminalCore (.stop .nil))
        core := { surfaceClosed := by decide }
        state := { surfaceClosed := by decide }
        calls :=
          { helpers :=
              { helperRank := 0
                callNamesNodup := helperCallNames_nodup _
                summaryOf := by
                  intro calleeName hmem
                  exfalso
                  simpa [helperCallNames, constructorAsFunctionSpec, constructorOnlyCtor,
                    stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
                    exprInternalHelperCallNames] using hmem
                calleeRanksDecrease := by
                  intro calleeName hmem
                  exfalso
                  simpa [helperCallNames, constructorAsFunctionSpec, constructorOnlyCtor,
                    stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
                    exprInternalHelperCallNames] using hmem
                exprCallsPreserveWorld := by
                  intro calleeName hmem
                  exfalso
                  simpa [exprHelperCallNames, constructorAsFunctionSpec, constructorOnlyCtor,
                    stmtListExprHelperCallNames, stmtExprHelperCallNames,
                    exprInternalHelperCallNames] using hmem }
            foreign := by decide
            lowLevel := by decide }
        effects := { surfaceClosed := by decide }
        noLocalObligations := rfl } }

private def constructorOnlyTx : IRTransaction :=
  { sender := 7
    functionSelector := 0
    args := [11] }

private theorem literalMappingWrite_txNormalized :
    Function.TxContextNormalized literalMappingWriteTx := by
  simp [Function.TxContextNormalized, literalMappingWriteTx, Compiler.Constants.addressModulus,
    Compiler.Constants.evmModulus]

private theorem literalMappingWrite_calldataFits :
    Function.TxCalldataSizeFitsEvm literalMappingWriteTx := by
  simp [Function.TxCalldataSizeFitsEvm, literalMappingWriteTx, Compiler.Constants.evmModulus]

private theorem constructorOnly_txNormalized :
    Function.TxContextNormalized constructorOnlyTx := by
  simp [Function.TxContextNormalized, constructorOnlyTx, Compiler.Constants.addressModulus,
    Compiler.Constants.evmModulus]

private theorem constructorOnly_calldataFits :
    Function.TxCalldataSizeFitsEvm constructorOnlyTx := by
  simp [Function.TxCalldataSizeFitsEvm, constructorOnlyTx, Compiler.Constants.evmModulus]

private theorem constructorOnly_noConflict :
    firstFieldWriteSlotConflict constructorOnlySpec.fields = none := by
  native_decide

example
    (ir : IRContract)
    (hcompile : CompilationModel.compile literalMappingWriteSpec [literalMappingWriteSelector] = Except.ok ir)
    (hbodySafety :
      ∀ stmt ∈ literalMappingWriteFunction.body,
        StmtMappingWriteSlotSafe literalMappingWriteSpec.fields stmt) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsExceptMappingWrites
        literalMappingWriteSpec
        [literalMappingWriteSelector]
        literalMappingWrite_supported_spec
        literalMappingWriteTx
        Verity.defaultState)
      (interpretIR
        ir
        literalMappingWriteTx
        (FunctionBody.initialIRStateForTx
          literalMappingWriteSpec
          literalMappingWriteTx
          Verity.defaultState)) := by
  exact Contract.compile_preserves_semantics_except_mapping_writes_stmtSafety
    (model := literalMappingWriteSpec)
    (selectors := [literalMappingWriteSelector])
    (hSupported := literalMappingWrite_supported_spec)
    (ir := ir)
    (tx := literalMappingWriteTx)
    (initialWorld := Verity.defaultState)
    (hnoConflict := literalMappingWrite_noConflict)
    (hsafety := by
      intro fn hfn
      simp [selectorDispatchedFunctions, literalMappingWriteSpec, literalMappingWriteFunction] at hfn
      rcases hfn with ⟨rfl, _, _⟩
      exact hbodySafety)
    (htxNormalized := literalMappingWrite_txNormalized)
    (hcalldataSizeFits := literalMappingWrite_calldataFits)
    (hcompile := hcompile)

example
    (ir : IRContract)
    (hcompile : CompilationModel.compile literalMappingWriteSpec [literalMappingWriteSelector] = Except.ok ir)
    (hbodySafety :
      ∀ stmt ∈ literalMappingWriteFunction.body,
        StmtMappingWriteSlotSafe literalMappingWriteSpec.fields stmt) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsExceptMappingWrites
        literalMappingWriteSpec
        [literalMappingWriteSelector]
        literalMappingWrite_supported_spec
        literalMappingWriteTx
        Verity.defaultState)
      (interpretIRWithInternals
        ir
        0
        literalMappingWriteTx
        (FunctionBody.initialIRStateForTx
          literalMappingWriteSpec
          literalMappingWriteTx
          Verity.defaultState)) := by
  exact Contract.compile_preserves_semantics_except_mapping_writes_and_helper_ir_supported
    (model := literalMappingWriteSpec)
    (selectors := [literalMappingWriteSelector])
    (hSupported := literalMappingWrite_supported_spec)
    (ir := ir)
    (tx := literalMappingWriteTx)
    (initialWorld := Verity.defaultState)
    (hnoConflict := literalMappingWrite_noConflict)
    (hsafety := by
      intro fn hfn
      simp [selectorDispatchedFunctions, literalMappingWriteSpec, literalMappingWriteFunction] at hfn
      rcases hfn with ⟨rfl, _, _⟩
      exact hbodySafety)
    (htxNormalized := literalMappingWrite_txNormalized)
    (hcalldataSizeFits := literalMappingWrite_calldataFits)
    (hcompile := hcompile)

example :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretConstructorWithHelpers
        constructorOnlySpec
        0
        constructorOnlyCtor
        constructorOnlyTx
        Verity.defaultState)
      (Function.execResultToIRResult
        (FunctionBody.initialIRStateForTx constructorOnlySpec constructorOnlyTx Verity.defaultState)
        (execIRStmts
          (sizeOf
            (match compileStmtList
                constructorOnlySpec.fields [] [] .calldata [] false
                ["initialOwner"]
                [Stmt.setStorageAddr "owner" (.param "initialOwner"), .stop] with
             | .ok body => body
             | .error _ => []) + 1)
          (ParamLoading.applyBindingsToIRState
            (FunctionBody.initialIRStateForTx constructorOnlySpec constructorOnlyTx Verity.defaultState)
            [("initialOwner", Compiler.Constants.addressMask &&& 11)])
          (match compileStmtList
              constructorOnlySpec.fields [] [] .calldata [] false
              ["initialOwner"]
              [Stmt.setStorageAddr "owner" (.param "initialOwner"), .stop] with
           | .ok body => body
           | .error _ => []))) := by
  have hbodyCompile :
      compileStmtList constructorOnlySpec.fields constructorOnlySpec.events constructorOnlySpec.errors
        .calldata [] false (constructorOnlyCtor.params.map (·.name)) constructorOnlyCtor.body =
      Except.ok
        (match compileStmtList constructorOnlySpec.fields [] [] .calldata [] false
            (constructorOnlyCtor.params.map (·.name)) constructorOnlyCtor.body with
         | .ok body => body
         | .error _ => []) := by
    rfl
  have hbind :
      SourceSemantics.bindSupportedParams
        [{ name := "initialOwner", ty := .address }]
        constructorOnlyTx.args =
      some [("initialOwner", Compiler.Constants.addressMask &&& 11)] := by
    native_decide
  simpa [constructorOnlySpec, constructorOnlyTx, constructorOnlySupported, Function.execResultToIRResult] using
    Function.supported_constructor_body_correct_with_body_interface
      (model := constructorOnlySpec)
      (ctor := constructorOnlyCtor)
      (helperFuel := 0)
      (hnormalized := rfl)
      (hnoEvents := rfl)
      (hnoErrors := rfl)
      (hSupported := constructorOnlySupported)
      (hnoConflict := constructorOnly_noConflict)
      (hsafety := by
        intro stmt hmem
        simp [constructorOnlyCtor] at hmem
        rcases hmem with rfl | rfl
        · simp [StmtMappingWriteSlotSafe]
        · simp [StmtMappingWriteSlotSafe])
      (tx := constructorOnlyTx)
      (initialWorld := Verity.defaultState)
      (bindings := [("initialOwner", Compiler.Constants.addressMask &&& 11)])
      (bodyStmts := match compileStmtList constructorOnlySpec.fields [] [] .calldata [] false
          (constructorOnlyCtor.params.map (·.name)) constructorOnlyCtor.body with
        | .ok body => body
        | .error _ => [])
      (hbodyCompile := hbodyCompile)
      (hbind := hbind)
      (htxNormalized := constructorOnly_txNormalized)
      (hcalldataSizeFits := constructorOnly_calldataFits)

end Compiler.Proofs.IRGeneration.ContractFeatureTest
