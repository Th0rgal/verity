import Compiler.Proofs.IRGeneration.Contract
import Compiler.Proofs.MappingSlot

namespace Compiler.Proofs.IRGeneration.ContractFeatureTest

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration
open Compiler.Yul

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
        noLocalObligations := rfl }
    rawCalldataSurfaceClosed := by decide }

private def constructorOnlyTx : IRTransaction :=
  { sender := 7
    functionSelector := 0
    args := [11] }

private def constructorArgCtor : ConstructorSpec :=
  { params := [{ name := "initialValue", ty := .uint256 }]
    body := [Stmt.setStorage "value" (.constructorArg 0), .stop] }

private def constructorArgSpec : CompilationModel :=
  { name := "ConstructorArg"
    fields := [{ name := "value", ty := .uint256 }]
    constructor := some constructorArgCtor
    functions := [] }

private def constructorArgTx : IRTransaction :=
  { sender := 5
    functionSelector := 0
    args := [13] }

private def constructorArgTrailingTx : IRTransaction :=
  { sender := 5
    functionSelector := 0
    args := [13, 99] }

private def constructorCalldataCtor : ConstructorSpec :=
  { params := [{ name := "initialValue", ty := .uint256 }]
    body := [Stmt.setStorage "value" .calldatasize, .stop] }

private def constructorCalldataSpec : CompilationModel :=
  { name := "ConstructorCalldata"
    fields := [{ name := "value", ty := .uint256 }]
    constructor := some constructorCalldataCtor
    functions := [] }

private def constructorCalldataTx : IRTransaction :=
  { sender := 6
    functionSelector := 0
    args := [21] }

private def constructorHelperArgCtor : ConstructorSpec :=
  { params := [{ name := "initialValue", ty := .uint256 }]
    body :=
      [Stmt.internalCallAssign ["tmp"] "identity" [.constructorArg 0],
        Stmt.setStorage "value" (.localVar "tmp"),
        .stop] }

private def constructorHelperArgTx : IRTransaction :=
  { sender := 8
    functionSelector := 0
    args := [17] }

private def identityInternalHelper : FunctionSpec :=
  { name := "identity"
    params := [{ name := "x", ty := .uint256 }]
    returnType := some .uint256
    isInternal := true
    body := [Stmt.return (.param "x")] }

private def constructorHelperArgSpec : CompilationModel :=
  { name := "ConstructorHelperArg"
    fields := [{ name := "value", ty := .uint256 }]
    constructor := some constructorHelperArgCtor
    functions := [identityInternalHelper] }

private def constSevenInternalHelper : FunctionSpec :=
  { name := "constSeven"
    params := []
    returnType := some .uint256
    isInternal := true
    body := [Stmt.return (.literal 7)] }

private def helperFuelAlignSpec : CompilationModel :=
  { name := "HelperFuelAlign"
    fields := []
    constructor := none
    functions := [constSevenInternalHelper] }

private def helperCallerFunction : FunctionSpec :=
  { name := "callConstSeven"
    params := []
    returnType := some .uint256
    body :=
      [Stmt.internalCallAssign ["result"] "constSeven" []
      , Stmt.return (.param "result")] }

private def helperCallerTx : IRTransaction :=
  { sender := 4
    functionSelector := 0
    args := [] }

private def helperCallSpec : CompilationModel :=
  { name := "HelperCall"
    fields := []
    constructor := none
    functions := [constSevenInternalHelper, helperCallerFunction] }

private def helperFuelAlignRuntime : SourceSemantics.RuntimeState :=
  { world := Verity.defaultState
    bindings := []
    selector := 0 }

private def stopOnlyFunction : FunctionSpec :=
  { name := "stopOnly"
    params := []
    returnType := none
    body := [Stmt.stop] }

private def stopOnlySpec : CompilationModel :=
  { name := "StopOnly"
    fields := []
    constructor := none
    functions := [stopOnlyFunction] }

private def stopOnlyTx : IRTransaction :=
  { sender := 3
    functionSelector := 0
    args := [] }

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

private theorem constructorArg_txNormalized :
    Function.TxContextNormalized constructorArgTx := by
  simp [Function.TxContextNormalized, constructorArgTx, Compiler.Constants.addressModulus,
    Compiler.Constants.evmModulus]

private theorem constructorArg_calldataFits :
    Function.TxCalldataSizeFitsEvm constructorArgTx := by
  simp [Function.TxCalldataSizeFitsEvm, constructorArgTx, Compiler.Constants.evmModulus]

private theorem stopOnly_txNormalized :
    Function.TxContextNormalized stopOnlyTx := by
  simp [Function.TxContextNormalized, stopOnlyTx, Compiler.Constants.addressModulus,
    Compiler.Constants.evmModulus]

private theorem stopOnly_calldataFits :
    Function.TxCalldataSizeFitsEvm stopOnlyTx := by
  simp [Function.TxCalldataSizeFitsEvm, stopOnlyTx, Compiler.Constants.evmModulus]

private theorem constructorOnly_noConflict :
    firstFieldWriteSlotConflict constructorOnlySpec.fields = none := by
  native_decide

private theorem constructorOnly_compileConstructor :
    ∃ bodyStmts,
      compileConstructor
          constructorOnlySpec.fields
          constructorOnlySpec.events
          constructorOnlySpec.errors
          constructorOnlySpec.constructor =
        Except.ok (genConstructorArgLoads constructorOnlyCtor.params ++ bodyStmts) ∧
      compileStmtList
          constructorOnlySpec.fields
          constructorOnlySpec.events
          constructorOnlySpec.errors
          .memory
          []
          false
          []
          constructorOnlyCtor.body =
        Except.ok bodyStmts := by
  rcases Function.compileConstructor_ok_components
      constructorOnlySpec.fields
      constructorOnlySpec.events
      constructorOnlySpec.errors
      constructorOnlyCtor
      (genConstructorArgLoads constructorOnlyCtor.params ++
        match compileStmtList
            constructorOnlySpec.fields
            constructorOnlySpec.events
            constructorOnlySpec.errors
            .memory
            []
            false
            []
            constructorOnlyCtor.body with
         | .ok body => body
         | .error _ => [])
      (by rfl) with ⟨bodyStmts, hbodyCompile, hdeploy⟩
  refine ⟨bodyStmts, ?_, hbodyCompile⟩
  exact Function.compileConstructor_some_ok_of_body
    constructorOnlySpec.fields
    constructorOnlySpec.events
    constructorOnlySpec.errors
    constructorOnlyCtor
    bodyStmts
    hbodyCompile

example :
    ∃ bodyStmts,
      compileConstructor
          constructorOnlySpec.fields
          constructorOnlySpec.events
          constructorOnlySpec.errors
          constructorOnlySpec.constructor =
        Except.ok (genConstructorArgLoads constructorOnlyCtor.params ++ bodyStmts) := by
  rcases constructorOnly_compileConstructor with ⟨bodyStmts, hdeploy, _⟩
  exact ⟨bodyStmts, hdeploy⟩

example :
    ∀ returns retNames bodyStmts,
      validateFunctionSpec identityInternalHelper = Except.ok () →
      functionReturns identityInternalHelper = Except.ok returns →
      retNames =
        freshInternalRetNames returns
          (identityInternalHelper.params.map (·.name) ++
            collectStmtListBindNames identityInternalHelper.body) →
      compileStmtList [] [] [] .calldata retNames true
        (identityInternalHelper.params.map (·.name) ++ retNames)
        identityInternalHelper.body = Except.ok bodyStmts →
      compileInternalFunction [] [] [] identityInternalHelper =
        Except.ok
          (YulStmt.funcDef
            (internalFunctionYulName identityInternalHelper.name)
            (identityInternalHelper.params.map (·.name))
            retNames
            bodyStmts) := by
  intro returns retNames bodyStmts hvalidate hreturns hretNames hbody
  exact compileInternalFunction_some_ok_of_components
    [] [] [] identityInternalHelper returns retNames bodyStmts
    hvalidate hreturns hretNames hbody

example :
    (SourceSemantics.interpretInternalFunctionFuel
      helperFuelAlignSpec
      0
      constSevenInternalHelper
      Verity.defaultState
      []).returnValue = some 7 := by
  native_decide

example :
    (SourceSemantics.interpretFunctionWithHelpers
      helperCallSpec
      1
      helperCallerFunction
      helperCallerTx
      Verity.defaultState).returnValue = some 7 := by
  native_decide

example :
    (SourceSemantics.interpretConstructor
      constructorArgSpec
      constructorArgCtor
      constructorArgTx
      Verity.defaultState).success = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructor
      constructorArgSpec
      constructorArgCtor
      constructorArgTx
      Verity.defaultState).finalStorage 0 = 13 := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorArgSpec
      0
      constructorArgCtor
      constructorArgTx
      Verity.defaultState).success = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorArgSpec
      0
      constructorArgCtor
      constructorArgTx
      Verity.defaultState).finalStorage 0 = 13 := by
  native_decide

example :
    (SourceSemantics.interpretConstructor
      constructorArgSpec
      constructorArgCtor
      constructorArgTrailingTx
      Verity.defaultState).success = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructor
      constructorArgSpec
      constructorArgCtor
      constructorArgTrailingTx
      Verity.defaultState).finalStorage 0 = 13 := by
  native_decide

example :
    SourceSemantics.constructorExecutionBindings
      constructorHelperArgCtor
      constructorHelperArgTx.args =
      some [("arg0", 17), ("initialValue", 17)] := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorHelperArgSpec
      1
      constructorHelperArgCtor
      constructorHelperArgTx
      Verity.defaultState).success = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorHelperArgSpec
      1
      constructorHelperArgCtor
      constructorHelperArgTx
      Verity.defaultState).finalStorage 0 = 17 := by
  native_decide

example :
    stmtListTouchesUnsupportedConstructorRawCalldataSurface constructorCalldataCtor.body = true := by
  native_decide

example :
    (SourceSemantics.interpretConstructor
      constructorCalldataSpec
      constructorCalldataCtor
      constructorCalldataTx
      Verity.defaultState).success = false := by
  native_decide

example :
    (SourceSemantics.interpretConstructorWithHelpers
      constructorCalldataSpec
      0
      constructorCalldataCtor
      constructorCalldataTx
      Verity.defaultState).success = false := by
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

example :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunctionWithHelpers
        stopOnlySpec
        1
        stopOnlyFunction
        stopOnlyTx
        Verity.defaultState)
      (FunctionBody.irResultOfExecResultWithInternals
        (FunctionBody.initialIRStateForTx stopOnlySpec stopOnlyTx Verity.defaultState)
        (.stop (FunctionBody.initialIRStateForTx stopOnlySpec stopOnlyTx Verity.defaultState))) := by
  have hbind :
      SourceSemantics.bindSupportedParams stopOnlyFunction.params stopOnlyTx.args = some [] := by
    rfl
  have hsource :
      SourceSemantics.execStmtListWithHelpers stopOnlySpec (SourceSemantics.effectiveFields stopOnlySpec)
        1
        { world := SourceSemantics.withTransactionContext Verity.defaultState stopOnlyTx
          bindings := []
          selector := stopOnlyTx.functionSelector }
        stopOnlyFunction.body =
      .stop
        { world := SourceSemantics.withTransactionContext Verity.defaultState stopOnlyTx
          bindings := []
          selector := stopOnlyTx.functionSelector } := by
    simp [stopOnlyFunction, SourceSemantics.execStmtListWithHelpers,
      SourceSemantics.execStmtWithHelpers]
  have hstate :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields stopOnlySpec)
        { world := SourceSemantics.withTransactionContext Verity.defaultState stopOnlyTx
          bindings := []
          selector := stopOnlyTx.functionSelector }
        (FunctionBody.initialIRStateForTx stopOnlySpec stopOnlyTx Verity.defaultState) := by
    simpa using
      Function.initialIRStateForTx_matches_runtime
        stopOnlySpec
        stopOnlyTx
        Verity.defaultState
        stopOnly_txNormalized
        stopOnly_calldataFits
  exact
    Function.interpretFunctionWithHelpers_eq_execResultToIRResultWithInternals_of_body
      (model := stopOnlySpec)
      (fn := stopOnlyFunction)
      (helperFuel := 1)
      (tx := stopOnlyTx)
      (initialWorld := Verity.defaultState)
      (sourceResult := .stop
        { world := SourceSemantics.withTransactionContext Verity.defaultState stopOnlyTx
          bindings := []
          selector := stopOnlyTx.functionSelector })
      (rollback := FunctionBody.initialIRStateForTx stopOnlySpec stopOnlyTx Verity.defaultState)
      (irResult := .stop (FunctionBody.initialIRStateForTx stopOnlySpec stopOnlyTx Verity.defaultState))
      (bindings := [])
      (hbind := hbind)
      (hsource := hsource)
      (hrollbackStorage := by simp [FunctionBody.initialIRStateForTx, stopOnlySpec, stopOnlyTx])
      (hrollbackEvents := by simp [FunctionBody.initialIRStateForTx, stopOnlySpec, stopOnlyTx])
      (hmatch := hstate)

end Compiler.Proofs.IRGeneration.ContractFeatureTest
