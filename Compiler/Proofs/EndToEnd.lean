/-
  Compiler.Proofs.EndToEnd: Composed Layers 2+3 End-to-End Theorem

  Composes the existing Layer 2 (CompilationModel → IR) and Layer 3 (IR → Yul)
  preservation theorems into a single end-to-end result:

    For any CompilationModel, evaluating the compiled Yul via the proof semantics
    produces the same result as the IR semantics.

  This is the first step toward eliminating `interpretSpec` from the TCB
  (Issue #998). Once primitive-level EDSL ≡ compiled-Yul lemmas are proven,
  this end-to-end theorem provides the composition spine.

  **Architecture**:
  - Layer 2: `compile spec selectors = .ok irContract`
             `interpretIR irContract tx irState ≡ interpretSpec spec ...`
             (proven per-contract in Compiler/Proofs/IRGeneration/Expr.lean)
  - Layer 3: `interpretIR irContract tx irState ≡ interpretYulFromIR irContract tx irState`
             (proven generically in Compiler/Proofs/YulGeneration/Preservation.lean)
  - This file: compose them into a single theorem statement.

  **EVMYulLean note (Phase 4)**: The default builtin backend is now
  EVMYulLean, and this file exposes safe-body public wrappers targeting the
  explicit EVMYulLean default-fuel proof-interpreter wrapper
  `interpretYulRuntimeWithBackend .evmYulLean`. Historical
  Verity-backed comparison entry points remain available under explicit
  reference-oracle names. The backend bridge is established in
  `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean`, proving
  that for all 36 bridged builtins, the legacy Verity backend agrees with
  EVMYulLean. The Phase 4 retargeting module (`EvmYulLeanRetarget.lean`)
  composes these per-builtin equivalences through expression evaluation and
  recursive `BridgedTarget` statement execution. It also proves that the emitted
  runtime wrapper satisfies that predicate, and executes equivalently under the
  EVMYulLean backend, when the IR bodies it contains do. It also exposes a
  lower-level Layer-3 theorem whose Yul side is
  `interpretYulRuntimeWithBackend .evmYulLean` and whose body witnesses
  are supplied by this file's public wrappers. Those wrappers derive raw
  external function-body bridge witnesses from source-level `SupportedSpec`,
  static-parameter, and `BridgedSafeStmts` witnesses where the public theorem
  applies.

  Run: lake build Compiler.Proofs.EndToEnd
-/

import Compiler.Proofs.YulGeneration.Preservation
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBodyClosure
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness
import Compiler.Proofs.IRGeneration.Contract
import Compiler.Proofs.IRGeneration.Function
import Compiler.Proofs.IRGeneration.Expr
import Compiler.SimpleStorageNativeWitness

namespace Compiler.Proofs.EndToEnd

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration

/-! ## Native Runtime Result Surface -/

/-- Result comparison surface for the native EVMYulLean harness.

The native harness can still fail closed during Verity-Yul-to-EVMYulLean
lowering, so the native-facing public theorem states both that native execution
returns a `YulResult` and that this result matches IR execution. -/
def nativeResultsMatch
    (ir : IRResult)
    (native : Except Compiler.Proofs.YulGeneration.Backends.AdapterError YulResult) :
    Prop :=
  match native with
  | .ok yul => Compiler.Proofs.YulGeneration.resultsMatch ir yul
  | .error _ => False

/-- Observable result comparison surface for native EVMYulLean execution. -/
def nativeResultsMatchOn
    (observableSlots : List Nat)
    (ir : IRResult)
    (native : Except Compiler.Proofs.YulGeneration.Backends.AdapterError YulResult) :
    Prop :=
  match native with
  | .ok yul =>
      ir.success = yul.success ∧
      ir.returnValue = yul.returnValue ∧
      (∀ slot, slot ∈ observableSlots →
        ir.finalStorage (IRStorageSlot.ofNat slot) = yul.finalStorage (IRStorageSlot.ofNat slot)) ∧
      ir.events = yul.events
  | .error _ => False

/-- Native EVMYulLean execution matches the IR semantics on the observable
result surface.

This is the direct native source-of-truth target for the remaining generic
generated-fragment proof. -/
def nativeIRRuntimeMatchesIR
    (fuel : Nat)
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat) :
    Prop :=
  nativeResultsMatchOn observableSlots (interpretIR contract tx state)
    (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
      fuel contract tx state observableSlots)

/-- Positive-fuel raw native dispatcher-exec target against IR directly.

This compares the projected lowered-dispatcher execution result with
`interpretIR`. -/
def nativeDispatcherExecMatchesIRPositive
    (fuel' : Nat)
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) :
    Prop :=
  let initial :=
    Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
      (YulTransaction.ofIR tx) state.storage
      (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
        (Compiler.runtimeCode contract) observableSlots)
  let nativeResult :=
    match
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial with
    | .error err => .error err
    | .ok finalState =>
        let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
        .ok (restored, [])
  nativeResultsMatchOn observableSlots (interpretIR contract tx state)
    (.ok
      (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events nativeResult))

/-- Lift a direct positive dispatcher-exec native-vs-IR proof through the native
runtime harness. -/
theorem nativeIRRuntimeMatchesIR_of_lowered_dispatcherExec_positive_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hFragment : Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeNativeFragment
      (Compiler.emitYul contract).runtimeCode = true)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul contract).runtimeCode = .ok nativeContract)
    (hEnv :
      Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
        (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx) = .ok ())
    (hMatch :
      nativeDispatcherExecMatchesIRPositive fuel' contract tx state
        observableSlots nativeContract) :
    nativeIRRuntimeMatchesIR (Nat.succ fuel') contract tx state observableSlots := by
  unfold nativeIRRuntimeMatchesIR
  rw
    [Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative_succ_eq_contractDispatcherExecResult_of_lowerRuntimeContractNative
      fuel' contract tx state observableSlots nativeContract hFragment hLower hEnv]
  unfold nativeDispatcherExecMatchesIRPositive at hMatch
  simpa using hMatch

/-- Generated-shape lift for the direct positive dispatcher-exec native-vs-IR
target. -/
theorem nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_positive_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hPrefixUnique : Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique
      ((if contract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
        contract.internalFunctions) = true)
    (hInternals : ∀ stmt, stmt ∈ contract.internalFunctions →
      ∃ name params rets body, stmt = Yul.YulStmt.funcDef name params rets body)
    (hExternalBodies : ∀ fn, fn ∈ contract.functions →
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef fn.body = false)
    (hInternalBodies : ∀ name params rets body,
      Yul.YulStmt.funcDef name params rets body ∈ contract.internalFunctions →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef body = false)
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul contract).runtimeCode = .ok nativeContract)
    (hEnv :
      Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
        (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx) = .ok ())
    (hMatch :
      nativeDispatcherExecMatchesIRPositive fuel' contract tx state
        observableSlots nativeContract) :
    nativeIRRuntimeMatchesIR (Nat.succ fuel') contract tx state observableSlots :=
  nativeIRRuntimeMatchesIR_of_lowered_dispatcherExec_positive_match
    (Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeNativeFragment_emitYul_runtimeCode_noFallback_noReceive
      contract hPrefixUnique hInternals hExternalBodies hInternalBodies
      hNoFallback hNoReceive)
    hLower hEnv hMatch

/-- Intro form for the direct positive-fuel native-vs-IR dispatcher-exec target
when native execution finishes normally. -/
theorem nativeDispatcherExecMatchesIRPositive_of_exec_ok_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    {finalState : EvmYul.Yul.State}
    (hExec :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial =
        .ok finalState)
    (hMatch :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      nativeResultsMatchOn observableSlots (interpretIR contract tx state)
        (.ok
          (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
            (YulTransaction.ofIR tx) state.storage state.events
            (.ok
              (finalState.reviveJump.overwrite? initial |>.setStore initial,
                []))))) :
    nativeDispatcherExecMatchesIRPositive fuel' contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecMatchesIRPositive
  simp [hExec]
  exact hMatch

/-- Intro form for a direct positive-fuel normal finish when a concrete native
execution lemma already packages the projected `YulResult`. -/
theorem nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    {finalState : EvmYul.Yul.State} {nativeYul : YulResult}
    (hExec :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial =
        .ok finalState)
    (hProject :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events
        (.ok (finalState.reviveJump.overwrite? initial |>.setStore initial, [])) =
        nativeYul)
    (hMatch :
      nativeResultsMatchOn observableSlots (interpretIR contract tx state)
        (.ok nativeYul)) :
    nativeDispatcherExecMatchesIRPositive fuel' contract tx state
      observableSlots nativeContract := by
  apply nativeDispatcherExecMatchesIRPositive_of_exec_ok_match
  · exact hExec
  · simpa [hProject] using hMatch

/-- Intro form for the direct positive-fuel native-vs-IR dispatcher-exec target
when native execution halts through EVMYulLean's Yul halt channel. -/
theorem nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    {haltState : EvmYul.Yul.State} {haltValue : EvmYul.Yul.Ast.Literal}
    (hExec :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial =
        .error (.YulHalt haltState haltValue))
    (hMatch :
      nativeResultsMatchOn observableSlots (interpretIR contract tx state)
        (.ok
          (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
            (YulTransaction.ofIR tx) state.storage state.events
            (.error (.YulHalt haltState haltValue))))) :
    nativeDispatcherExecMatchesIRPositive fuel' contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecMatchesIRPositive
  simp [hExec]
  exact hMatch

/-- Intro form for a direct positive-fuel Yul halt when a concrete native
execution lemma already packages the projected `YulResult`. -/
theorem nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    {haltState : EvmYul.Yul.State} {haltValue : EvmYul.Yul.Ast.Literal}
    {nativeYul : YulResult}
    (hExec :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial =
        .error (.YulHalt haltState haltValue))
    (hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events
        (.error (.YulHalt haltState haltValue)) =
        nativeYul)
    (hMatch :
      nativeResultsMatchOn observableSlots (interpretIR contract tx state)
        (.ok nativeYul)) :
    nativeDispatcherExecMatchesIRPositive fuel' contract tx state
      observableSlots nativeContract := by
  apply nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_match
  · exact hExec
  · rw [hProject]
    exact hMatch

/-- Intro form for the direct positive-fuel native-vs-IR dispatcher-exec target
when native execution fails through a non-halt EVMYulLean exception. -/
theorem nativeDispatcherExecMatchesIRPositive_of_exec_error_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    {err : EvmYul.Yul.Exception}
    (hExec :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial =
        .error err)
    (hMatch :
      nativeResultsMatchOn observableSlots (interpretIR contract tx state)
        (.ok
          (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
            (YulTransaction.ofIR tx) state.storage state.events (.error err)))) :
    nativeDispatcherExecMatchesIRPositive fuel' contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecMatchesIRPositive
  simp [hExec]
  exact hMatch

/-- Intro form for a direct positive-fuel error when a concrete native
execution lemma already packages the projected `YulResult`. -/
theorem nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    {err : EvmYul.Yul.Exception} {nativeYul : YulResult}
    (hExec :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        fuel' nativeContract initial =
        .error err)
    (hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) state.storage state.events (.error err) =
        nativeYul)
    (hMatch :
      nativeResultsMatchOn observableSlots (interpretIR contract tx state)
        (.ok nativeYul)) :
    nativeDispatcherExecMatchesIRPositive fuel' contract tx state
      observableSlots nativeContract := by
  apply nativeDispatcherExecMatchesIRPositive_of_exec_error_match
  · exact hExec
  · rw [hProject]
    exact hMatch

/-! ## Layer 3: IR → Yul (Generic) -/

/-- Layer 3 function-level preservation: any IR function body produces equivalent
results under IR execution and fuel-based Yul execution. -/
theorem layer3_function_preserves_semantics
    (fn : IRFunction) (selector : Nat) (args : List Nat) (initialState : IRState) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (execIRFunction fn args initialState)
      (interpretYulBodyFromState fn selector
        (fn.params.zip args |>.foldl (fun s (p, v) => s.setVar p.name v) initialState)
        initialState) :=
  ir_function_body_equiv fn selector args initialState

/-! ## Bridging Helpers -/

/-- Explicit bridge hypothesis for the param-load erasure step. -/
private def paramLoadErasure (fn : IRFunction) (tx : IRTransaction) (state : IRState) : Prop :=
  let paramState := fn.params.zip tx.args |>.foldl
    (fun s (p, v) => s.setVar p.name v) state
  execYulStmts (yulStateOfIR 0 paramState) fn.body =
    execYulStmts (YulState.initial (YulTransaction.ofIR tx) state.storage state.events) fn.body

/-- Result wrapping equivalence: `interpretYulRuntime` produces the same `YulResult`
as `yulResultOfExecWithRollback` when the rollback storage matches. -/
theorem interpretYulRuntime_eq_yulResultOfExec
    (stmts : List Yul.YulStmt) (tx : YulTransaction) (stor : IRStorageSlot → IRStorageWord)
    (events : List (List Nat)) :
    interpretYulRuntime stmts tx stor events =
      yulResultOfExecWithRollback (YulState.initial tx stor events)
        (execYulStmts (YulState.initial tx stor events) stmts) := by
  simp [interpretYulRuntime]
  cases execYulStmts (YulState.initial tx stor events) stmts with
  | «continue» s => simp [yulResultOfExecWithRollback]
  | «return» v s => simp [yulResultOfExecWithRollback]
  | «stop» s => simp [yulResultOfExecWithRollback]
  | «revert» s => simp [yulResultOfExecWithRollback, YulState.initial]

/-- State equivalence: under the entry-point hypotheses, `yulStateOfIR` produces
the same YulState as `YulState.initial`. -/
theorem yulStateOfIR_eq_initial
    (sel : Nat) (state : IRState) (tx : IRTransaction)
    (hcalldata : state.calldata = tx.args)
    (hsender : state.sender = tx.sender)
    (hmsgValue : state.msgValue = tx.msgValue)
    (hthis : state.thisAddress = tx.thisAddress)
    (htimestamp : state.blockTimestamp = tx.blockTimestamp)
    (hnumber : state.blockNumber = tx.blockNumber)
    (hchain : state.chainId = tx.chainId)
    (hblobBaseFee : state.blobBaseFee = tx.blobBaseFee)
    (hselector : state.selector = tx.functionSelector)
    (hreturn : state.returnValue = none)
    (hmemory : state.memory = fun _ => 0)
    (htransient : state.transientStorage = fun _ => 0)
    (hvars : state.vars = []) :
    yulStateOfIR sel state =
      YulState.initial
        { sender := tx.sender
          msgValue := tx.msgValue
          thisAddress := tx.thisAddress
          blockTimestamp := tx.blockTimestamp
          blockNumber := tx.blockNumber
          chainId := tx.chainId
          blobBaseFee := tx.blobBaseFee
          functionSelector := tx.functionSelector
          args := tx.args }
        state.storage state.events := by
  simp [yulStateOfIR, YulState.initial, hvars, hmemory, htransient, hcalldata, hsender, hmsgValue,
    hthis, htimestamp, hnumber, hchain, hblobBaseFee, hselector, hreturn]

/-- Hypothesis-driven param-load erasure. -/
theorem execYulStmts_paramState_eq_emptyVars
    (fn : IRFunction) (tx : IRTransaction) (state : IRState)
    (_hvars : state.vars = [])
    (_hmemory : state.memory = fun _ => 0)
    (_hcalldata : state.calldata = tx.args)
    (_hsender : state.sender = tx.sender)
    (_hmsgValue : state.msgValue = tx.msgValue)
    (_hthis : state.thisAddress = tx.thisAddress)
    (_htimestamp : state.blockTimestamp = tx.blockTimestamp)
    (_hnumber : state.blockNumber = tx.blockNumber)
    (_hchain : state.chainId = tx.chainId)
    (_hselector : state.selector = tx.functionSelector)
    (_hreturn : state.returnValue = none)
    (hparamErase : paramLoadErasure fn tx state) :
    paramLoadErasure fn tx state :=
  hparamErase

/-- Internal function tables are bridged whenever the Layer-3 well-formedness
predicate says they contain only Yul function definitions. The retargeting
bridge treats function-definition nodes as straight-line declarations; the
called-body simulation remains covered by the existing function-body
hypotheses. -/
private theorem internalFunctions_bridged_of_contractWF
    (contract : IRContract) (hWF : ContractWF contract) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts
      contract.internalFunctions := by
  intro stmt hMem
  rcases hWF stmt hMem with ⟨name, params, rets, body, hStmt⟩
  subst hStmt
  exact Compiler.Proofs.YulGeneration.Backends.bridgedStmt_funcDef
    name params rets body

/-- Function-level native-fragment body shape from static scalar parameter loads plus
a body-code shape witness. This isolates the shared append/prologue reasoning
needed before the public generated-native wrappers can derive their own
external-body witnesses from compiler output. -/
theorem compileFunctionSpec_noFuncDefs_of_static_params_and_body
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef)
    (selector : Nat) (spec : CompilationModel.FunctionSpec)
    (irFn : IRFunction)
    (hStaticParams :
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams spec.params)
    (hBodyNoFuncDefs :
      ∀ bodyStmts,
        CompilationModel.compileStmtList fields events errors .calldata [] false
          (spec.params.map (·.name)) [] spec.body = Except.ok bodyStmts →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
          bodyStmts = false)
    (hcompile :
      CompilationModel.compileFunctionSpec fields events errors [] selector spec =
        Except.ok irFn) :
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      irFn.body = false := by
  rcases Compiler.Proofs.IRGeneration.Function.compileFunctionSpec_ok_components
      fields events errors selector spec irFn hcompile with
    ⟨returns, bodyStmts, _hvalidate, _hreturns, hbody, hirFn⟩
  subst irFn
  change
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      (CompilationModel.genParamLoads spec.params ++ bodyStmts) = false
  simp [
    Compiler.Proofs.YulGeneration.Backends.genParamLoads_static_scalar_noFuncDefs
      spec.params hStaticParams,
    hBodyNoFuncDefs bodyStmts hbody]

theorem compileFunctionSpec_noFuncDefs_of_safe_static_params
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef)
    (selector : Nat) (spec : CompilationModel.FunctionSpec)
    (irFn : IRFunction)
    (hStaticParams :
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams spec.params)
    (hSafeBody :
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        fields errors .calldata [] false spec.body)
    (hcompile :
      CompilationModel.compileFunctionSpec fields events errors [] selector spec =
        Except.ok irFn) :
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      irFn.body = false := by
  rcases Compiler.Proofs.IRGeneration.Function.compileFunctionSpec_ok_components
      fields events errors selector spec irFn hcompile with
    ⟨returns, bodyStmts, _hvalidate, _hreturns, hbody, hirFn⟩
  subst irFn
  change
    Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
      (CompilationModel.genParamLoads spec.params ++ bodyStmts) = false
  simp [
    Compiler.Proofs.YulGeneration.Backends.genParamLoads_static_scalar_noFuncDefs
      spec.params hStaticParams,
    Compiler.Proofs.YulGeneration.Backends.compileStmtList_always_noFuncDefs
      fields events errors .calldata [] false spec.body
      (spec.params.map (·.name)) hSafeBody hbody]

/-- Convert the new source-level safe-body closure theorem into the low-level
`BridgedStmts fn.body` witness still consumed by the EVMYulLean runtime
retargeting theorem. This is the key local bridge from compiler-produced
`FunctionSpec` bodies to emitted IR function bodies: static scalar parameter
loads are bridged by the prologue theorem, and the compiled source body is
bridged by `compileStmtList_always_bridged`. -/
theorem compileFunctionSpec_bridged_of_safe_static_params
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef)
    (selector : Nat) (spec : CompilationModel.FunctionSpec)
    (irFn : IRFunction)
    (hStaticParams :
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams spec.params)
    (hSafeBody :
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        fields errors .calldata [] false spec.body)
    (hcompile :
      CompilationModel.compileFunctionSpec fields events errors [] selector spec =
        Except.ok irFn) :
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts irFn.body := by
  rcases Compiler.Proofs.IRGeneration.Function.compileFunctionSpec_ok_components
      fields events errors selector spec irFn hcompile with
    ⟨returns, bodyStmts, _hvalidate, _hreturns, hbody, hirFn⟩
  subst irFn
  change
    Compiler.Proofs.YulGeneration.Backends.BridgedStmts
      (CompilationModel.genParamLoads spec.params ++ bodyStmts)
  exact Compiler.Proofs.YulGeneration.Backends.BridgedStmts_append
    (Compiler.Proofs.YulGeneration.Backends.genParamLoads_static_scalar_bridged
      spec.params hStaticParams)
    (Compiler.Proofs.YulGeneration.Backends.compileStmtList_always_bridged
      fields events errors .calldata [] false spec.body
      (spec.params.map (·.name)) hSafeBody hbody)

/-- Lift the one-function bridge closure theorem across the compiled external
function table. This keeps the public EndToEnd theorem from exposing raw
`BridgedStmts fn.body` obligations when callers already have source-level
safe-body/static-param witnesses for every selector-dispatched function. -/
theorem compiledExternalFunctions_bridged_of_safe_static
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef) :
    ∀ {entries : List (CompilationModel.FunctionSpec × Nat)}
      {irFns : List IRFunction},
      List.Forall₂
        (fun entry irFn =>
          CompilationModel.compileFunctionSpec fields events errors
            [] entry.2 entry.1 = Except.ok irFn)
        entries irFns →
      (∀ entry, entry ∈ entries →
        Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams
          entry.1.params) →
      (∀ entry, entry ∈ entries →
        Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
          fields errors .calldata [] false entry.1.body) →
      ∀ irFn, irFn ∈ irFns →
        Compiler.Proofs.YulGeneration.Backends.BridgedStmts irFn.body := by
  intro entries irFns hcompiled hStatic hSafe
  induction hcompiled with
  | nil =>
      intro irFn hmem
      cases hmem
  | @cons entry irFn entries irFns hhead htail ih =>
      intro target hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmemTail
      · exact compileFunctionSpec_bridged_of_safe_static_params
          fields events errors entry.2 entry.1 target
          (hStatic entry (by simp))
          (hSafe entry (by simp))
          hhead
      · exact ih
          (fun next hnext => hStatic next (by simp [hnext]))
          (fun next hnext => hSafe next (by simp [hnext]))
          target hmemTail

/-- Lift function-level native-fragment body shape across the compiled external
function table. This is the no-`funcDef` analogue of
`compiledExternalFunctions_bridged_of_safe_static`, staged separately because
the body-shape source predicate is still being proved fragment by fragment. -/
theorem compiledExternalFunctions_noFuncDefs_of_static_params_and_body
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef) :
    ∀ {entries : List (CompilationModel.FunctionSpec × Nat)}
      {irFns : List IRFunction},
      List.Forall₂
        (fun entry irFn =>
          CompilationModel.compileFunctionSpec fields events errors
            [] entry.2 entry.1 = Except.ok irFn)
        entries irFns →
      (∀ entry, entry ∈ entries →
        Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams
          entry.1.params) →
      (∀ entry, entry ∈ entries →
        ∀ bodyStmts,
          CompilationModel.compileStmtList fields events errors .calldata [] false
            (entry.1.params.map (·.name)) [] entry.1.body =
              Except.ok bodyStmts →
          Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
            bodyStmts = false) →
      ∀ irFn, irFn ∈ irFns →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
          irFn.body = false := by
  intro entries irFns hcompiled hStatic hBody
  induction hcompiled with
  | nil =>
      intro irFn hmem
      cases hmem
  | @cons entry irFn entries irFns hhead htail ih =>
      intro target hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmemTail
      · exact compileFunctionSpec_noFuncDefs_of_static_params_and_body
          fields events errors entry.2 entry.1 target
          (hStatic entry (by simp))
          (hBody entry (by simp))
          hhead
      · exact ih
          (fun next hnext => hStatic next (by simp [hnext]))
          (fun next hnext => hBody next (by simp [hnext]))
          target hmemTail

theorem compiledExternalFunctions_noFuncDefs_of_safe_static
    (fields : List CompilationModel.Field)
    (events : List CompilationModel.EventDef)
    (errors : List CompilationModel.ErrorDef) :
    ∀ {entries : List (CompilationModel.FunctionSpec × Nat)}
      {irFns : List IRFunction},
      List.Forall₂
        (fun entry irFn =>
          CompilationModel.compileFunctionSpec fields events errors
            [] entry.2 entry.1 = Except.ok irFn)
        entries irFns →
      (∀ entry, entry ∈ entries →
        Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams
          entry.1.params) →
      (∀ entry, entry ∈ entries →
        Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
          fields errors .calldata [] false entry.1.body) →
      ∀ irFn, irFn ∈ irFns →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
          irFn.body = false := by
  intro entries irFns hcompiled hStatic hSafe
  induction hcompiled with
  | nil =>
      intro irFn hmem
      cases hmem
  | @cons entry irFn entries irFns hhead htail ih =>
      intro target hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmemTail
      · exact compileFunctionSpec_noFuncDefs_of_safe_static_params
          fields events errors entry.2 entry.1 target
          (hStatic entry (by simp))
          (hSafe entry (by simp))
          hhead
      · exact ih
          (fun next hnext => hStatic next (by simp [hnext]))
          (fun next hnext => hSafe next (by simp [hnext]))
          target hmemTail

/-- Bridging: the two Yul execution entry points produce the same result
when the IR state has empty vars and zero memory. -/
theorem yulBody_from_state_eq_yulBody
    (fn : IRFunction) (tx : IRTransaction) (state : IRState)
    (hcalldata : state.calldata = tx.args)
    (hsender : state.sender = tx.sender)
    (hmsgValue : state.msgValue = tx.msgValue)
    (hthis : state.thisAddress = tx.thisAddress)
    (htimestamp : state.blockTimestamp = tx.blockTimestamp)
    (hnumber : state.blockNumber = tx.blockNumber)
    (hchain : state.chainId = tx.chainId)
    (hblobBaseFee : state.blobBaseFee = tx.blobBaseFee)
    (hselector : state.selector = tx.functionSelector)
    (hreturn : state.returnValue = none)
    (hmemory : state.memory = fun _ => 0)
    (htransient : state.transientStorage = fun _ => 0)
    (hvars : state.vars = [])
    (hparamErase : paramLoadErasure fn tx state) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (execIRFunction fn tx.args state)
      (interpretYulBody fn tx state) := by
  have h_ir_from := ir_function_body_equiv fn 0 tx.args state
  suffices h_eq : interpretYulBodyFromState fn 0
      (fn.params.zip tx.args |>.foldl (fun s (p, v) => s.setVar p.name v) state)
      state = interpretYulBody fn tx state by
    rwa [h_eq] at h_ir_from
  simp only [interpretYulBodyFromState, interpretYulBody]
  have h_rollback := yulStateOfIR_eq_initial 0 state tx hcalldata hsender hmsgValue hthis htimestamp hnumber hchain hblobBaseFee hselector hreturn hmemory htransient hvars
  have h_exec := execYulStmts_paramState_eq_emptyVars fn tx state hvars hmemory hcalldata hsender hmsgValue hthis htimestamp hnumber hchain hselector hreturn hparamErase
  rw [h_rollback]
  simp only at h_exec
  rw [h_exec]
  exact (interpretYulRuntime_eq_yulResultOfExec fn.body
    (YulTransaction.ofIR tx) state.storage state.events).symm

/-! ## Layer 3 Contract-Level: IR → EVMYulLean-backed Yul -/

/-- Lower-level Layer 3 contract-level preservation targeting the
EVMYulLean-backed Yul runtime. This is the EndToEnd-facing wrapper around
`yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle`;
callers supply the existing
function-body simulation hypotheses plus `BridgedStmts` witnesses for emitted
external function bodies. Fallback/receive witnesses are discharged from the
existing `none` hypotheses, and the internal-function table witness is derived
from `ContractWF`. -/
theorem layer3_contract_preserves_semantics_evmYulLeanBackend_with_function_bridge
    (contract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hWF : ContractWF contract)
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none)
    (hdispatchGuardSafe : ∀ fn, fn ∈ contract.functions →
      DispatchGuardsSafe fn tx)
    (hNoHasSelector : ∀ fn, fn ∈ contract.functions →
      yulStmtsNoRef "__has_selector" fn.body)
    (hHasSelectorDead : ∀ fn, fn ∈ contract.functions →
      HasSelectorDeadBridge fn.body)
    (hLoopFree : ∀ fn, fn ∈ contract.functions →
      yulStmtsLoopFree fn.body = true)
    (hbody : ∀ fn, fn ∈ contract.functions →
      Compiler.Proofs.YulGeneration.resultsMatch
        (execIRFunction fn tx.args (initialState.withTx tx))
        (interpretYulBody fn tx (initialState.withTx tx)))
    (hFunctions : ∀ fn, fn ∈ contract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR contract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackend .evmYulLean (Compiler.emitYul contract).runtimeCode
        (YulTransaction.ofIR tx) initialState.storage initialState.events) :=
  Compiler.Proofs.YulGeneration.Backends.yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle
    contract tx initialState hselector hNoWrap hWF hNoFallback hNoReceive
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead hLoopFree hbody
    hFunctions
    (by intro fb hSome; rw [hNoFallback] at hSome; cases hSome)
    (by intro rc hSome; rw [hNoReceive] at hSome; cases hSome)
    (internalFunctions_bridged_of_contractWF contract hWF)

/-- Layer 3 contract-level preservation targeting EVMYulLean under explicit
function-body bridge witnesses, using the same entry-state normalization
hypotheses as the reference-oracle theorem. -/
theorem layer3_contract_preserves_semantics_evmYulLeanBackend
    (contract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hvars : initialState.vars = [])
    (hmemory : initialState.memory = fun _ => 0)
    (htransient : initialState.transientStorage = fun _ => 0)
    (hreturn : initialState.returnValue = none)
    (hparamErase : ∀ fn, fn ∈ contract.functions → paramLoadErasure fn tx (initialState.withTx tx))
    (hdispatchGuardSafe : ∀ fn, fn ∈ contract.functions → DispatchGuardsSafe fn tx)
    (hNoHasSelector : ∀ fn, fn ∈ contract.functions → yulStmtsNoRef "__has_selector" fn.body)
    (hHasSelectorDead : ∀ fn, fn ∈ contract.functions → HasSelectorDeadBridge fn.body)
    (hLoopFree : ∀ fn, fn ∈ contract.functions →
      yulStmtsLoopFree fn.body = true)
    (hWF : ContractWF contract)
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none)
    (hFunctions : ∀ fn, fn ∈ contract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR contract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackend .evmYulLean (Compiler.emitYul contract).runtimeCode
        (YulTransaction.ofIR tx) initialState.storage initialState.events) := by
  apply layer3_contract_preserves_semantics_evmYulLeanBackend_with_function_bridge contract tx initialState
    hselector hNoWrap hWF hNoFallback hNoReceive hdispatchGuardSafe hNoHasSelector
    hHasSelectorDead hLoopFree
  · intro fn hmem
    exact (yulBody_from_state_eq_yulBody fn tx (initialState.withTx tx)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (by simpa using hreturn)
        (by simpa using hmemory)
        (by simpa using htransient)
        (by simpa using hvars)
        (hparamErase fn hmem))
  · exact hFunctions

/-- Generic native Layer 3 seam on the direct native-vs-IR target. -/
theorem layer3_contract_preserves_semantics_native_of_evmYulLean_bridge
    (fuel : Nat) (contract : IRContract) (tx : IRTransaction)
    (initialState : IRState) (observableSlots : List Nat)
    (_hselector : tx.functionSelector < selectorModulus)
    (_hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (_hvars : initialState.vars = [])
    (_hmemory : initialState.memory = fun _ => 0)
    (_htransient : initialState.transientStorage = fun _ => 0)
    (_hreturn : initialState.returnValue = none)
    (_hparamErase : ∀ fn, fn ∈ contract.functions →
      paramLoadErasure fn tx (initialState.withTx tx))
    (_hdispatchGuardSafe : ∀ fn, fn ∈ contract.functions → DispatchGuardsSafe fn tx)
    (_hNoHasSelector : ∀ fn, fn ∈ contract.functions → yulStmtsNoRef "__has_selector" fn.body)
    (_hHasSelectorDead : ∀ fn, fn ∈ contract.functions → HasSelectorDeadBridge fn.body)
    (_hLoopFree : ∀ fn, fn ∈ contract.functions → yulStmtsLoopFree fn.body = true)
    (_hWF : ContractWF contract) (_hNoFallback : contract.fallbackEntrypoint = none)
    (_hNoReceive : contract.receiveEntrypoint = none)
    (_hFunctions : ∀ fn, fn ∈ contract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body)
    (_hFuel : fuel = sizeOf (Compiler.emitYul contract).runtimeCode + 1)
    (hNativeBridge : nativeIRRuntimeMatchesIR fuel contract tx initialState observableSlots) :
    nativeResultsMatchOn observableSlots (interpretIR contract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        fuel contract tx initialState observableSlots) :=
  hNativeBridge

/-- Native Layer 3 generated-shape variant at raw lowered-dispatcher exec on
the direct native-vs-IR target. -/
theorem layer3_contract_preserves_semantics_native_of_generated_dispatcherExec_positive_match
    (fuel' : Nat) (contract : IRContract) (tx : IRTransaction)
    (initialState : IRState) (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hPrefixUnique : Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique
      ((if contract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
        contract.internalFunctions) = true)
    (hInternals : ∀ stmt, stmt ∈ contract.internalFunctions →
      ∃ name params rets body, stmt = Yul.YulStmt.funcDef name params rets body)
    (hExternalBodies : ∀ fn, fn ∈ contract.functions →
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef fn.body = false)
    (hInternalBodies : ∀ name params rets body,
      Yul.YulStmt.funcDef name params rets body ∈ contract.internalFunctions →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef body = false)
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul contract).runtimeCode = .ok nativeContract)
    (hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
      (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx) = .ok ())
    (hNativeDispatcherExec :
      nativeDispatcherExecMatchesIRPositive fuel' contract tx initialState
        observableSlots nativeContract) :
    nativeResultsMatchOn observableSlots (interpretIR contract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        (Nat.succ fuel') contract tx initialState observableSlots) :=
  nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_positive_match
    hPrefixUnique hInternals hExternalBodies hInternalBodies hNoFallback
    hNoReceive hLower hEnv hNativeDispatcherExec

/-! ## Layers 2+3 Composition -/

/-- End-to-end bridge-witness variant: given a successfully compiled contract,
IR execution matches EVMYulLean-backed Yul execution under explicit
function-body closure hypotheses. Fallback/receive bridge witnesses are
vacuous under the public `none` hypotheses and are discharged internally, as is
the internal function table witness via `ContractWF`. -/
theorem layers2_3_ir_matches_yul_evmYulLeanBackend_with_function_bridge
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (irContract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (_hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hvars : initialState.vars = [])
    (hmemory : initialState.memory = fun _ => 0)
    (htransient : initialState.transientStorage = fun _ => 0)
    (hreturn : initialState.returnValue = none)
    (hparamErase : ∀ fn, fn ∈ irContract.functions →
      paramLoadErasure fn tx (initialState.withTx tx))
    (hdispatchGuardSafe : ∀ fn, fn ∈ irContract.functions →
      DispatchGuardsSafe fn tx)
    (hNoHasSelector : ∀ fn, fn ∈ irContract.functions →
      yulStmtsNoRef "__has_selector" fn.body)
    (hHasSelectorDead : ∀ fn, fn ∈ irContract.functions →
      HasSelectorDeadBridge fn.body)
    (hLoopFree : ∀ fn, fn ∈ irContract.functions →
      yulStmtsLoopFree fn.body = true)
    (hWF : ContractWF irContract)
    (hNoFallback : irContract.fallbackEntrypoint = none)
    (hNoReceive : irContract.receiveEntrypoint = none)
    (hFunctions : ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR irContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackend .evmYulLean (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) initialState.storage initialState.events) :=
  layer3_contract_preserves_semantics_evmYulLeanBackend irContract tx initialState
    hselector hNoWrap hvars hmemory htransient hreturn hparamErase
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead hLoopFree hWF hNoFallback
    hNoReceive hFunctions

/-- End-to-end: for a supported compiler-produced contract whose
selector-dispatched function bodies are in the EVMYulLean-safe source fragment
and whose ABI parameters compile through the static-scalar prologue bridge, IR
execution matches EVMYulLean-backed Yul execution without exposing a raw
`BridgedStmts fn.body` hypothesis to callers. -/
theorem layers2_3_ir_matches_yul_evmYulLeanBackend
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (irContract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams
          entry.1.params)
    (hSafeBodies :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
          spec.fields spec.errors .calldata [] false entry.1.body)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hvars : initialState.vars = [])
    (hmemory : initialState.memory = fun _ => 0)
    (htransient : initialState.transientStorage = fun _ => 0)
    (hreturn : initialState.returnValue = none)
    (hparamErase : ∀ fn, fn ∈ irContract.functions →
      paramLoadErasure fn tx (initialState.withTx tx))
    (hdispatchGuardSafe : ∀ fn, fn ∈ irContract.functions →
      DispatchGuardsSafe fn tx)
    (hNoHasSelector : ∀ fn, fn ∈ irContract.functions →
      yulStmtsNoRef "__has_selector" fn.body)
    (hHasSelectorDead : ∀ fn, fn ∈ irContract.functions →
      HasSelectorDeadBridge fn.body)
    (hLoopFree : ∀ fn, fn ∈ irContract.functions →
      yulStmtsLoopFree fn.body = true)
    (hWF : ContractWF irContract)
    (hNoFallback : irContract.fallbackEntrypoint = none)
    (hNoReceive : irContract.receiveEntrypoint = none) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR irContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackend .evmYulLean (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) initialState.storage initialState.events) :=
  layers2_3_ir_matches_yul_evmYulLeanBackend_with_function_bridge
    spec selectors irContract tx initialState
    hCompile hselector hNoWrap hvars hmemory htransient hreturn hparamErase
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead hLoopFree hWF hNoFallback
    hNoReceive
    (compiledExternalFunctions_bridged_of_safe_static
      spec.fields spec.events spec.errors
      (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
        spec selectors hSupported irContract hCompile)
      hStaticParams hSafeBodies)

/-- Current supported native theorem seam on the direct native-vs-IR target. -/
theorem layers2_3_ir_matches_native_evmYulLean_of_evmYulLean_bridge
    (fuel : Nat)
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (irContract : IRContract) (tx : IRTransaction)
    (initialState : IRState) (observableSlots : List Nat)
    (_hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (_hSupported : SupportedSpec spec selectors)
    (_hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (_hSafeBodies :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts spec.fields
          spec.errors .calldata [] false entry.1.body)
    (_hselector : tx.functionSelector < selectorModulus)
    (_hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (_hvars : initialState.vars = [])
    (_hmemory : initialState.memory = fun _ => 0)
    (_htransient : initialState.transientStorage = fun _ => 0)
    (_hreturn : initialState.returnValue = none)
    (_hparamErase : ∀ fn, fn ∈ irContract.functions →
      paramLoadErasure fn tx (initialState.withTx tx))
    (_hdispatchGuardSafe : ∀ fn, fn ∈ irContract.functions → DispatchGuardsSafe fn tx)
    (_hNoHasSelector : ∀ fn, fn ∈ irContract.functions → yulStmtsNoRef "__has_selector" fn.body)
    (_hHasSelectorDead : ∀ fn, fn ∈ irContract.functions → HasSelectorDeadBridge fn.body)
    (_hLoopFree : ∀ fn, fn ∈ irContract.functions → yulStmtsLoopFree fn.body = true)
    (_hWF : ContractWF irContract) (_hNoFallback : irContract.fallbackEntrypoint = none)
    (_hNoReceive : irContract.receiveEntrypoint = none)
    (_hFuel : fuel = sizeOf (Compiler.emitYul irContract).runtimeCode + 1)
    (hNativeBridge : nativeIRRuntimeMatchesIR fuel irContract tx
      initialState observableSlots) :
    nativeResultsMatchOn observableSlots
      (interpretIR irContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        fuel irContract tx initialState observableSlots) :=
  hNativeBridge

/-- Supported compiler output has a unique generated-runtime helper prefix.

`SupportedSpec` rules out emitted internal helper definitions, leaving only the
optional mapping-slot helper in the generated runtime prefix. -/
theorem generatedRuntimePrefixFunctionNamesUnique_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique
      ((if irContract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
        irContract.internalFunctions) = true := by
  have hInternalNil : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hInternalNil]
  by_cases hUsesMapping : irContract.usesMapping
  · simp [hUsesMapping,
      Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique,
      Compiler.Proofs.YulGeneration.Backends.Native.stringListHasDuplicate,
      Compiler.mappingSlotFuncAt, Compiler.CodegenCommon.mappingSlotFuncAt]
  · simp [hUsesMapping,
      Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique,
      Compiler.Proofs.YulGeneration.Backends.Native.stringListHasDuplicate]

/-- Supported compiler output has no emitted internal helper statements. This
discharges the generated-runtime fragment's internal-function-shape witness. -/
theorem generatedRuntimeInternalsAreFuncDefs_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∀ stmt, stmt ∈ irContract.internalFunctions →
      ∃ name params rets body, stmt = Yul.YulStmt.funcDef name params rets body := by
  intro stmt hmem
  have hInternalNil : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hInternalNil] at hmem
  simp at hmem

/-- Supported compiler output has no internal helper bodies that can contain
nested function definitions. -/
theorem generatedRuntimeInternalBodiesHaveNoFuncDefs_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors) :
    ∀ name params rets body,
      Yul.YulStmt.funcDef name params rets body ∈ irContract.internalFunctions →
        Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef body = false := by
  intro name params rets body hmem
  have hInternalNil : irContract.internalFunctions = [] :=
    Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_internalFunctions_nil
      (model := spec) (selectors := selectors) (hSupported := hSupported)
      (ir := irContract) (hcompile := hCompile)
  rw [hInternalNil] at hmem
  simp at hmem

/-- Source-level body closure discharges the generated runtime fragment's
external-function-body shape witness for supported compiler output. -/
theorem generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_supported
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hBodyNoFuncDefs :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        ∀ bodyStmts,
          CompilationModel.compileStmtList spec.fields spec.events spec.errors
            .calldata [] false (entry.1.params.map (·.name)) [] entry.1.body =
              Except.ok bodyStmts →
          Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
            bodyStmts = false) :
    ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
        fn.body = false :=
  compiledExternalFunctions_noFuncDefs_of_static_params_and_body
    spec.fields spec.events spec.errors
    (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
      spec selectors hSupported irContract hCompile)
    hStaticParams hBodyNoFuncDefs

theorem generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_safe
    {spec : CompilationModel.CompilationModel} {selectors : List Nat}
    {irContract : IRContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hSafeBodies : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body) :
    ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
        fn.body = false :=
  compiledExternalFunctions_noFuncDefs_of_safe_static
    spec.fields spec.events spec.errors
    (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
      spec selectors hSupported irContract hCompile)
    hStaticParams hSafeBodies

theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_match
    {fuel' : Nat} {spec : CompilationModel.CompilationModel}
    {selectors : List Nat} {irContract : IRContract}
    {tx : IRTransaction} {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hExternalBodies : ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef fn.body = false)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
      (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) = .ok ())
    (hMatch :
      nativeDispatcherExecMatchesIRPositive fuel' irContract tx state
        observableSlots nativeContract) :
    nativeIRRuntimeMatchesIR (Nat.succ fuel') irContract tx state observableSlots :=
  nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_positive_match
    (generatedRuntimePrefixFunctionNamesUnique_of_compile_ok_supported
      hCompile hSupported)
    (generatedRuntimeInternalsAreFuncDefs_of_compile_ok_supported
      hCompile hSupported)
    hExternalBodies
    (generatedRuntimeInternalBodiesHaveNoFuncDefs_of_compile_ok_supported
      hCompile hSupported)
    (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_noFallbackEntrypoint
      spec selectors hSupported irContract hCompile)
    (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_noReceiveEntrypoint
      spec selectors hSupported irContract hCompile)
    hLower hEnv hMatch

theorem nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure
    {fuel' : Nat} {spec : CompilationModel.CompilationModel}
    {selectors : List Nat} {irContract : IRContract}
    {tx : IRTransaction} {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors → Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hSafeBodies : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
      (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) = .ok ())
    (hMatch : nativeDispatcherExecMatchesIRPositive fuel' irContract tx state observableSlots nativeContract) :
    nativeIRRuntimeMatchesIR (Nat.succ fuel') irContract tx state observableSlots :=
  nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_match
    hCompile hSupported
    (generatedRuntimeExternalBodiesHaveNoFuncDefs_of_compile_ok_safe
      hCompile hSupported hStaticParams hSafeBodies)
    hLower hEnv hMatch

/-- Supported compiler-produced direct native theorem with an already-closed
external native body-shape witness. -/
theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_external_bodies_match
    (fuel' : Nat) (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (irContract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hExternalBodies : ∀ fn, fn ∈ irContract.functions →
      Compiler.Proofs.YulGeneration.Backends.Native.yulStmtsContainFuncDef
        fn.body = false)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
      (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) = .ok ())
    (hNativeDispatcherExec :
      nativeDispatcherExecMatchesIRPositive fuel' irContract tx initialState
        observableSlots nativeContract) :
    nativeResultsMatchOn observableSlots (interpretIR irContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        (Nat.succ fuel') irContract tx initialState observableSlots) :=
  nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_match
    hCompile hSupported hExternalBodies hLower hEnv hNativeDispatcherExec

/-- Supported compiler-produced positive dispatcher-exec theorem on the direct
native-vs-IR target. -/
theorem layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_match
    (fuel' : Nat) (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (irContract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors → Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hSafeBodies : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts
        spec.fields spec.errors .calldata [] false entry.1.body)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
      (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) = .ok ())
    (hNativeDispatcherExec :
      nativeDispatcherExecMatchesIRPositive fuel' irContract tx initialState
        observableSlots nativeContract) :
    nativeResultsMatchOn observableSlots (interpretIR irContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        (Nat.succ fuel') irContract tx initialState observableSlots) :=
  nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure
    hCompile hSupported hStaticParams hSafeBodies hLower hEnv hNativeDispatcherExec

/-! ## Concrete Instantiation: SimpleStorage -/

/-- The concrete SimpleStorage IR fixture uses only EVMYulLean-bridged Yul
shapes: calldata parameter loading, one literal-slot storage write, one memory
write from `sload`, and `stop`/`return` terminators. -/
private theorem simpleStorage_functions_bridged :
    ∀ fn, fn ∈ simpleStorageIRContract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body := by
  intro fn hmem
  simp [simpleStorageIRContract] at hmem
  rcases hmem with rfl | rfl
  · apply Compiler.Proofs.YulGeneration.Backends.BridgedStmts_cons_let
    · exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.call
        "calldataload" [Yul.YulExpr.lit 4]
        (by
          left
          simp [Compiler.Proofs.YulGeneration.Backends.bridgedBuiltins])
        (by
          intro arg harg
          simp at harg
          subst arg
          exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.lit 4)
    · apply Compiler.Proofs.YulGeneration.Backends.BridgedStmts_cons_sstore_lit
      · exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.ident "value"
      · exact Compiler.Proofs.YulGeneration.Backends.BridgedStmts_singleton_stop
  · apply Compiler.Proofs.YulGeneration.Backends.BridgedStmts_cons_mstore
    · exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.lit 0
    · exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.call
        "sload" [Yul.YulExpr.lit 0]
        (by
          left
          simp [Compiler.Proofs.YulGeneration.Backends.bridgedBuiltins])
        (by
          intro arg harg
          simp at harg
          subst arg
          exact Compiler.Proofs.YulGeneration.Backends.BridgedExpr.lit 0)
    · exact Compiler.Proofs.YulGeneration.Backends.BridgedStmts_singleton_return
        (Yul.YulExpr.lit 0) (Yul.YulExpr.lit 32)
        (Compiler.Proofs.YulGeneration.Backends.BridgedExpr.lit 0)
        (Compiler.Proofs.YulGeneration.Backends.BridgedExpr.lit 32)

private theorem simpleStorage_functions_loop_free :
    ∀ fn, fn ∈ simpleStorageIRContract.functions →
      yulStmtsLoopFree fn.body = true := by
  intro fn hmem
  simp [simpleStorageIRContract] at hmem ⊢
  rcases hmem with rfl | rfl <;> rfl

/-- The emitted SimpleStorage runtime consists of the single generated external
dispatcher shell for the two concrete SimpleStorage functions.

This pins down the outer runtime layer that the native dispatcher bridge must
peel before applying the concrete lowered selector-switch lemmas. -/
theorem simpleStorage_runtimeCode_eq_single_dispatcher :
    (Compiler.emitYul simpleStorageIRContract).runtimeCode =
      [Compiler.CodegenCommon.buildSwitch
        simpleStorageIRContract.functions none none] := by
  dsimp [Compiler.emitYul, Compiler.CodegenCommon.emitYul,
    Compiler.runtimeCode, Compiler.CodegenCommon.runtimeCode,
    simpleStorageIRContract]

theorem lowerRuntimeContractNative_single_stmt_eq_lowerStmtsNative
    (stmt : Yul.YulStmt)
    (hNoFunc : ∀ name params rets body,
      stmt ≠ Yul.YulStmt.funcDef name params rets body) :
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative [stmt] =
      match Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative [stmt] with
      | .ok dispatcher =>
          .ok { dispatcher := .Block dispatcher
                functions :=
                  (∅ :
                    Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap) }
      | .error err => .error err := by
  unfold Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
  unfold Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
  dsimp
  rw [Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNativeAux_stmt_cons]
  · rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons]
    cases hLower :
        Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds
          (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames [stmt])
          0 stmt with
    | ok pair =>
        cases pair with
        | mk lowered next =>
            simp [Bind.bind, Except.bind, Pure.pure, Except.pure,
              Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNativeAux]
    | error err =>
        simp [Bind.bind, Except.bind]
  · exact hNoFunc

noncomputable def simpleStorageNativeDispatcherStmts :
    List EvmYul.Yul.Ast.Stmt :=
  match
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
      [Compiler.CodegenCommon.buildSwitch
        simpleStorageIRContract.functions none none] with
  | .ok stmts => stmts
  | .error _ => []

/-- The executable SimpleStorage native witness is exactly the statement
lowering of the single emitted dispatcher shell.

This exposes the concrete lowered dispatcher block without unfolding the
computed native witness in later selector-case proofs. -/
theorem simpleStorageNativeContract_dispatcher_eq_lowered_stmts :
    Compiler.SimpleStorageNativeWitness.nativeContract.dispatcher =
      .Block simpleStorageNativeDispatcherStmts := by
  unfold Compiler.SimpleStorageNativeWitness.nativeContract
  rw [simpleStorage_runtimeCode_eq_single_dispatcher]
  rw [lowerRuntimeContractNative_single_stmt_eq_lowerStmtsNative]
  · cases hLower :
        Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
          [Compiler.CodegenCommon.buildSwitch
            simpleStorageIRContract.functions none none] with
    | ok stmts =>
        simp [simpleStorageNativeDispatcherStmts, hLower]
    | error err =>
        simp [simpleStorageNativeDispatcherStmts, hLower]
  · intro name params rets body h
    cases h

/-- A `.block` head in the native lowering surfaces as a singleton `.Block`
output when the lowering succeeds.

This is the structural lemma that lets the SimpleStorage native dispatcher
bridge be peeled past its outer block wrapper without unfolding `buildSwitch`.
-/
theorem lowerStmtsNative_single_block_ok_singleton
    (stmts : List Yul.YulStmt)
    (lowered : List EvmYul.Yul.Ast.Stmt)
    (h : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
            [Yul.YulStmt.block stmts] = .ok lowered) :
    ∃ inner, lowered = [.Block inner] := by
  unfold Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative at h
  dsimp at h
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons] at h
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_block] at h
  cases hInner :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
          [Yul.YulStmt.block stmts])
        0 stmts with
  | error err =>
      rw [hInner] at h
      simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok pair =>
      cases pair with
      | mk inner next =>
          rw [hInner] at h
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
            Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
            List.append_nil, Except.ok.injEq] at h
          exact ⟨inner, h.symm⟩

/-- The `simpleStorageNativeDispatcherStmts` lowering succeeds and equals the
SimpleStorage native witness dispatcher contents.

The outer success is inherited from
`Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_eq` (which
itself uses the existing `native_decide` trust chain on the runtime witness),
combined with the structural single-statement equation. -/
theorem simpleStorageNativeDispatcherStmts_lowering_ok :
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
        [Compiler.CodegenCommon.buildSwitch
          simpleStorageIRContract.functions none none] =
      .ok simpleStorageNativeDispatcherStmts := by
  have hOuter := Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_eq
  rw [simpleStorage_runtimeCode_eq_single_dispatcher] at hOuter
  rw [lowerRuntimeContractNative_single_stmt_eq_lowerStmtsNative] at hOuter
  · cases hL : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
        [Compiler.CodegenCommon.buildSwitch
          simpleStorageIRContract.functions none none] with
    | ok stmts =>
        simp [simpleStorageNativeDispatcherStmts, hL]
    | error err =>
        rw [hL] at hOuter
        simp at hOuter
  · intro name params rets body h'
    cases h'

/-- The SimpleStorage native dispatcher statement list is a singleton `.Block`.

Reason: `buildSwitch` produces a `Yul.YulStmt.block`, which the native lowering
maps to `[.Block inner]` for the lowered inner statements. Combined with the
fact that the lowering succeeds (above), this exposes the inner block shape
without further computation. -/
theorem simpleStorageNativeDispatcherStmts_exists_singleton_block :
    ∃ inner : List EvmYul.Yul.Ast.Stmt,
      simpleStorageNativeDispatcherStmts = [.Block inner] := by
  have hOk := simpleStorageNativeDispatcherStmts_lowering_ok
  -- buildSwitch produces a YulStmt.block by definition.
  have hBlock :
      Compiler.CodegenCommon.buildSwitch
          simpleStorageIRContract.functions none none =
        Yul.YulStmt.block _ := rfl
  rw [hBlock] at hOk
  exact lowerStmtsNative_single_block_ok_singleton _ _ hOk

noncomputable def simpleStorageNativeDispatcherInnerStmts :
    List EvmYul.Yul.Ast.Stmt :=
  Classical.choose simpleStorageNativeDispatcherStmts_exists_singleton_block

theorem simpleStorageNativeDispatcherStmts_eq_singleton_block :
    simpleStorageNativeDispatcherStmts =
      [.Block simpleStorageNativeDispatcherInnerStmts] :=
  Classical.choose_spec simpleStorageNativeDispatcherStmts_exists_singleton_block

/-- Transitive form of the SimpleStorage native dispatcher shape: combining
the lowered-stmts and singleton-block equalities exposes the dispatcher value
as `.Block [.Block <inner>]`, which is the exact shape consumed by the harness
dispatcher-exec peel lemma. -/
theorem simpleStorageNativeContract_dispatcher_eq_singleton_block_inner :
    Compiler.SimpleStorageNativeWitness.nativeContract.dispatcher =
      .Block [.Block simpleStorageNativeDispatcherInnerStmts] := by
  rw [simpleStorageNativeContract_dispatcher_eq_lowered_stmts,
    simpleStorageNativeDispatcherStmts_eq_singleton_block]

/-- Reify the SimpleStorage native witness contract as a record whose
dispatcher is the doubly-blocked inner statement list.

This packages record-η with the lowered + singleton-block dispatcher
equalities so that the harness peel lemmas (which expect a
`{ dispatcher := .Block body, functions := … }` shape) apply in one rewrite. -/
theorem simpleStorageNativeContract_eq_record_inner_block :
    Compiler.SimpleStorageNativeWitness.nativeContract =
      { dispatcher := .Block [.Block simpleStorageNativeDispatcherInnerStmts]
        functions :=
          Compiler.SimpleStorageNativeWitness.nativeContract.functions } := by
  have hEta : Compiler.SimpleStorageNativeWitness.nativeContract =
      (⟨Compiler.SimpleStorageNativeWitness.nativeContract.dispatcher,
        Compiler.SimpleStorageNativeWitness.nativeContract.functions⟩ :
          EvmYul.Yul.Ast.YulContract) := rfl
  rw [hEta, simpleStorageNativeContract_dispatcher_eq_singleton_block_inner]

/-- Dispatcher-exec for the SimpleStorage native witness peels TWO outer
`.Block` wrappers (the function-body wrapper installed by the dispatcher exec
plus the singleton-block emitted by `buildSwitch`'s native lowering) into a
direct `EvmYul.Yul.exec` over the inner statement list.

This collapses the bridge's dispatcher invocation into the same shape the
harness's per-selector body lemmas already speak about, in preparation for
discharging the bridge from those lemmas. -/
theorem simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec
    (peeledFuel : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (Nat.succ (Nat.succ (Nat.succ peeledFuel)))
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) =
      EvmYul.Yul.exec (Nat.succ peeledFuel)
        (.Block simpleStorageNativeDispatcherInnerStmts)
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) := by
  rw [simpleStorageNativeContract_eq_record_inner_block]
  rw [Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult_block_dispatcher_eq_exec_block
    (Nat.succ peeledFuel) [.Block simpleStorageNativeDispatcherInnerStmts]
    Compiler.SimpleStorageNativeWitness.nativeContract.functions
    tx storage observableSlots]
  rw [Compiler.Proofs.YulGeneration.Backends.Native.exec_singleton_block_eq_exec_block]

/-- A successful lowering of a singleton `[.block stmts]` reveals exactly the
inner statement-list lowering. This is the structural counterpart of
`lowerStmtsNative_single_block_ok_singleton`: instead of merely existing, the
`inner` argument is the *output* of the inner statement-list lowering. -/
theorem lowerStmtsNative_block_stmts_eq
    (stmts : List Yul.YulStmt)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (h : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative
            [Yul.YulStmt.block stmts] = .ok [.Block inner]) :
    ∃ next : Nat,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
          [Yul.YulStmt.block stmts])
        0 stmts = .ok (inner, next) := by
  unfold Compiler.Proofs.YulGeneration.Backends.lowerStmtsNative at h
  dsimp at h
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons] at h
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_block] at h
  cases hInner :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        (Compiler.Proofs.YulGeneration.Backends.yulStmtsIdentifierNames
          [Yul.YulStmt.block stmts])
        0 stmts with
  | error err =>
      rw [hInner] at h
      simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok pair =>
      cases pair with
      | mk inner' next =>
          rw [hInner] at h
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
            Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
            List.append_nil, Except.ok.injEq] at h
          injection h with hStmt _
          injection hStmt with hEq
          subst hEq
          exact ⟨next, rfl⟩

/-- A `.let_`-headed statement-list lowering peels its head into a singleton
`.Let` statement and threads the unchanged switch counter through the tail.
This generic peel is the per-statement complement of
`lowerStmtsNative_block_stmts_eq`: combined, they reduce a successful native
lowering of a `.let_`-headed block to the lowering of its tail. -/
theorem lowerStmtsNativeWithSwitchIds_let_head_eq
    (reservedNames : List String) (n0 : Nat)
    (name : String) (value : Yul.YulExpr)
    (rest : List Yul.YulStmt)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
            reservedNames n0
            (Yul.YulStmt.let_ name value :: rest) = .ok (inner, next)) :
    ∃ rest' : List EvmYul.Yul.Ast.Stmt,
      inner = EvmYul.Yul.Ast.Stmt.Let [name]
                (some
                  (Compiler.Proofs.YulGeneration.Backends.lowerExprNative value))
                :: rest' ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames n0 rest = .ok (rest', next) := by
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_let]
    at h
  -- Reduce the outer `Except.ok ([letStmt], n0) >>= …` to expose the rest's
  -- lowering call directly threaded with `n0`.
  simp only [Bind.bind, Except.bind] at h
  cases hRest :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames n0 rest with
  | error err =>
      rw [hRest] at h
      simp only [reduceCtorEq] at h
  | ok pair =>
      cases pair with
      | mk rest' n =>
          rw [hRest] at h
          simp only [Pure.pure, Except.pure, List.singleton_append,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hList, hNat⟩ := h
          subst hNat
          exact ⟨rest', hList.symm, rfl⟩

/-- An `.if_`-headed statement-list lowering peels its head into a singleton
`.If` statement and threads the body's switch-counter advance through to the
tail. This is the per-statement complement of
`lowerStmtsNativeWithSwitchIds_let_head_eq` for the `if_` case: combined with
`lowerStmtsNative_block_stmts_eq`, it lets a successful native lowering of a
block be peeled past an `.if_`-headed source statement. -/
theorem lowerStmtsNativeWithSwitchIds_if_head_eq
    (reservedNames : List String) (n0 : Nat)
    (cond : Yul.YulExpr) (body : List Yul.YulStmt)
    (rest : List Yul.YulStmt)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
            reservedNames n0
            (Yul.YulStmt.if_ cond body :: rest) = .ok (inner, next)) :
    ∃ (body' : List EvmYul.Yul.Ast.Stmt) (midN : Nat)
      (rest' : List EvmYul.Yul.Ast.Stmt),
      inner = EvmYul.Yul.Ast.Stmt.If
                (Compiler.Proofs.YulGeneration.Backends.lowerExprNative cond)
                body' :: rest' ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames n0 body = .ok (body', midN) ∧
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames midN rest = .ok (rest', next) := by
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_cons,
      Compiler.Proofs.YulGeneration.Backends.lowerStmtGroupNativeWithSwitchIds_if]
    at h
  cases hBody :
      Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames n0 body with
  | error _ => rw [hBody] at h; simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok bodyPair =>
    obtain ⟨body', midN⟩ := bodyPair
    rw [hBody] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hRest :
        Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
          reservedNames midN rest with
    | error _ =>
      rw [hRest] at h; simp only [reduceCtorEq] at h
    | ok restPair =>
      obtain ⟨rest', _⟩ := restPair
      rw [hRest] at h
      simp only [List.singleton_append, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hList, hNat⟩ := h
      subst hNat
      exact ⟨body', midN, rest', hList.symm, rfl, hRest⟩

set_option linter.unusedSimpArgs false in
/-- A singleton `.switch`-headed statement-list lowering reduces to a singleton
`.lowerNativeSwitchBlock` over the same source expression. This is the
companion of `lowerStmtsNativeWithSwitchIds_let_head_eq` and `_if_head_eq`
specialized to a single source-level `switch` statement (no tail), which is
exactly the shape produced by the body of `buildSwitch`'s selector-hit `if`.
The case-bodies and default-body lowerings remain abstract because their
shape depends on the concrete contract `funcs` list. -/
theorem lowerStmtsNativeWithSwitchIds_singleton_switch_eq
    (reservedNames : List String) (n0 : Nat)
    (expr : Yul.YulExpr) (cases : List (Nat × List Yul.YulStmt))
    (defaultCase : Option (List Yul.YulStmt))
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            [Yul.YulStmt.switch expr cases defaultCase] = .ok (inner, next)) :
    ∃ (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (default' : List EvmYul.Yul.Ast.Stmt),
      inner = [Backends.lowerNativeSwitchBlock expr
        (Backends.freshNativeSwitchId reservedNames n0) cases' default'] := by
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons,
      Backends.lowerStmtGroupNativeWithSwitchIds_switch] at h
  dsimp only [] at h
  cases hCases : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) cases with
  | error _ =>
      rw [hCases] at h; simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok casesPair =>
      obtain ⟨cases', midN⟩ := casesPair
      rw [hCases] at h
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      cases defaultCase with
      | none =>
          simp only [Backends.lowerStmtsNativeWithSwitchIds_nil,
            List.singleton_append, Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨cases', [], h.1.symm⟩
      | some defaultBody =>
          dsimp only [] at h
          cases hDef : Backends.lowerStmtsNativeWithSwitchIds
              reservedNames midN defaultBody with
          | error _ =>
              rw [hDef] at h
              simp only [Bind.bind, Except.bind, reduceCtorEq] at h
          | ok defaultPair =>
              obtain ⟨default', _⟩ := defaultPair
              rw [hDef] at h
              simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
                Backends.lowerStmtsNativeWithSwitchIds_nil,
                List.singleton_append, Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨cases', default', h.1.symm⟩

/-- The head of the SimpleStorage native dispatcher inner-block is the lowered
`let __has_selector := ...` statement. This peels one further layer beyond the
singleton-block extraction (`simpleStorageNativeDispatcherStmts_eq_singleton_block`)
by applying the cons/`_let` lowering equations to the head of `buildSwitch`'s
3-statement block. The remaining tail is left abstract — downstream peels will
expose the second and third statements. -/
theorem simpleStorageNativeDispatcherInnerStmts_head_let_exists :
    ∃ (e : EvmYul.Yul.Ast.Expr) (rest : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        EvmYul.Yul.Ast.Stmt.Let ["__has_selector"] (some e) :: rest := by
  have hOk := simpleStorageNativeDispatcherStmts_lowering_ok
  rw [simpleStorageNativeDispatcherStmts_eq_singleton_block] at hOk
  obtain ⟨next, hInner⟩ := lowerStmtsNative_block_stmts_eq _ _ hOk
  -- `buildSwitch ssIRC.functions none none` unfolds (definitionally) to a
  -- 3-statement `YulStmt.block` whose head is `let __has_selector := …`, so
  -- `hInner` is already a `let_`-headed lowering at the source spine.
  obtain ⟨rest', hSplit, _⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  exact ⟨_, rest', hSplit⟩

/-- The first two statements of the SimpleStorage native dispatcher inner-block
are exactly the lowered `let __has_selector := ...` and the lowered selector-miss
guard `if iszero(__has_selector) { revert(0,0) }`. This peels the second
statement of `buildSwitch`'s 3-statement source block by chaining
`lowerStmtsNative_block_stmts_eq`, `lowerStmtsNativeWithSwitchIds_let_head_eq`,
and `lowerStmtsNativeWithSwitchIds_if_head_eq`. -/
theorem simpleStorageNativeDispatcherInnerStmts_let_if_head_exists :
    ∃ (e : EvmYul.Yul.Ast.Expr) (c : EvmYul.Yul.Ast.Expr)
      (body : List EvmYul.Yul.Ast.Stmt) (rest : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        EvmYul.Yul.Ast.Stmt.Let ["__has_selector"] (some e) ::
          EvmYul.Yul.Ast.Stmt.If c body ::
          rest := by
  have hOk := simpleStorageNativeDispatcherStmts_lowering_ok
  rw [simpleStorageNativeDispatcherStmts_eq_singleton_block] at hOk
  obtain ⟨next, hInner⟩ := lowerStmtsNative_block_stmts_eq _ _ hOk
  obtain ⟨rest', hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body', _midN, rest'', hIf, _, _⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  rw [hIf] at hLet
  exact ⟨_, _, body', rest'', hLet⟩

/-- The full inner-block of the SimpleStorage native dispatcher has exactly the
expected three-statement shape: the lowered `let __has_selector := …`, the
selector-miss `if iszero(__has_selector) { … }` guard, and the selector-hit
`if __has_selector { switch … }` body. The trailing list is empty because
`buildSwitch` produces a 3-statement source block. -/
theorem simpleStorageNativeDispatcherInnerStmts_eq_let_if_if :
    ∃ (e : EvmYul.Yul.Ast.Expr) (c1 : EvmYul.Yul.Ast.Expr)
      (body1 : List EvmYul.Yul.Ast.Stmt)
      (c2 : EvmYul.Yul.Ast.Expr) (body2 : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"] (some e),
         EvmYul.Yul.Ast.Stmt.If c1 body1,
         EvmYul.Yul.Ast.Stmt.If c2 body2] := by
  have hOk := simpleStorageNativeDispatcherStmts_lowering_ok
  rw [simpleStorageNativeDispatcherStmts_eq_singleton_block] at hOk
  obtain ⟨_, hInner⟩ := lowerStmtsNative_block_stmts_eq _ _ hOk
  obtain ⟨rest', hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, rest'', hIf1, _, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨body2', _, rest''', hIf2, _, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  rw [hIf2] at hIf1
  rw [hIf1] at hLet
  exact ⟨_, _, body1', _, body2', hLet⟩

/-- The lowered RHS expression of the SimpleStorage native dispatcher's
`__has_selector` let. Pinned via `Classical.choose` from the let/if/if shape
existential so it can be referenced by downstream proofs without re-`obtain`-ing
the witness each time. -/
noncomputable def simpleStorageNativeDispatcher_letValue :
    EvmYul.Yul.Ast.Expr :=
  Classical.choose simpleStorageNativeDispatcherInnerStmts_eq_let_if_if

/-- The lowered condition of the SimpleStorage native dispatcher's
selector-miss `if iszero(__has_selector) { … }` guard. -/
noncomputable def simpleStorageNativeDispatcher_if1Cond :
    EvmYul.Yul.Ast.Expr :=
  Classical.choose
    (Classical.choose_spec simpleStorageNativeDispatcherInnerStmts_eq_let_if_if)

/-- The lowered body of the SimpleStorage native dispatcher's selector-miss
guard (the `revert(0,0)` revert path). -/
noncomputable def simpleStorageNativeDispatcher_if1Body :
    List EvmYul.Yul.Ast.Stmt :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec simpleStorageNativeDispatcherInnerStmts_eq_let_if_if))

/-- The lowered condition of the SimpleStorage native dispatcher's
selector-hit `if __has_selector { switch … }` body. -/
noncomputable def simpleStorageNativeDispatcher_if2Cond :
    EvmYul.Yul.Ast.Expr :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          simpleStorageNativeDispatcherInnerStmts_eq_let_if_if)))

/-- The lowered body of the SimpleStorage native dispatcher's selector-hit
`if __has_selector { switch … }` body — i.e., the singleton list containing
the lowered `switch` over the three generated cases. -/
noncomputable def simpleStorageNativeDispatcher_if2Body :
    List EvmYul.Yul.Ast.Stmt :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            simpleStorageNativeDispatcherInnerStmts_eq_let_if_if))))

/-- Closed-form decomposition of the SimpleStorage native dispatcher inner
statement list using the named witness defs. Eliminates the existential
boilerplate from the `_eq_let_if_if` lemma so future selector-case proofs can
rewrite the dispatcher inner-stmts to a literal 3-element list. -/
theorem simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if :
    simpleStorageNativeDispatcherInnerStmts =
      [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
          (some simpleStorageNativeDispatcher_letValue),
       EvmYul.Yul.Ast.Stmt.If
          simpleStorageNativeDispatcher_if1Cond
          simpleStorageNativeDispatcher_if1Body,
       EvmYul.Yul.Ast.Stmt.If
          simpleStorageNativeDispatcher_if2Cond
          simpleStorageNativeDispatcher_if2Body] :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            simpleStorageNativeDispatcherInnerStmts_eq_let_if_if))))

/-- Composed structural form of the SimpleStorage native dispatcher exec:
the doubly-blocked dispatcher is exposed at the concrete inner three-statement
spine using the pinned named witnesses. This combines
`simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec` with
`simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if`, replacing the
existential let/if/if shape with a concrete equation in named witnesses. -/
theorem simpleStorageNativeContract_dispatcherExec_eq_named_let_if_if_block_exec
    (peeledFuel : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (Nat.succ (Nat.succ (Nat.succ peeledFuel)))
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) =
      EvmYul.Yul.exec (Nat.succ peeledFuel)
        (.Block
          [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
              (some simpleStorageNativeDispatcher_letValue),
           EvmYul.Yul.Ast.Stmt.If
              simpleStorageNativeDispatcher_if1Cond
              simpleStorageNativeDispatcher_if1Body,
           EvmYul.Yul.Ast.Stmt.If
              simpleStorageNativeDispatcher_if2Cond
              simpleStorageNativeDispatcher_if2Body])
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) := by
  rw [simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec,
      simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if]

/-- Concrete head exposure of the SimpleStorage native dispatcher inner-block:
its first statement is the lowered `let __has_selector := iszero(lt(calldatasize(), 4))`
that `buildSwitch` emits, with the source-Yul RHS pinned explicitly. This is
the same peel as `simpleStorageNativeDispatcherInnerStmts_head_let_exists` but
exposes the *concrete* lowered RHS (not just an abstract Lean witness), so the
`Classical.choose`-pinned `simpleStorageNativeDispatcher_letValue` can be
equated to it via head injection. -/
theorem simpleStorageNativeDispatcherInnerStmts_concrete_let_head :
    ∃ rest : List EvmYul.Yul.Ast.Stmt,
      simpleStorageNativeDispatcherInnerStmts =
        EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some
              (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
                (Yul.YulExpr.call "iszero"
                  [Yul.YulExpr.call "lt"
                    [Yul.YulExpr.call "calldatasize" [],
                     Yul.YulExpr.lit 4]]))) :: rest := by
  have hOk := simpleStorageNativeDispatcherStmts_lowering_ok
  rw [simpleStorageNativeDispatcherStmts_eq_singleton_block] at hOk
  obtain ⟨_, hInner⟩ := lowerStmtsNative_block_stmts_eq _ _ hOk
  obtain ⟨rest', hSplit, _⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  exact ⟨rest', hSplit⟩

/-- Concrete-form equation for the SimpleStorage native dispatcher's full inner
3-statement block, pinning *all three* source-Yul expressions (the let RHS, the
selector-miss `iszero(__has_selector)` guard, and the selector-hit
`__has_selector` guard) to the literal Yul expressions emitted by
`buildSwitch`. Only the two `If` bodies remain existential, since they depend
on the lowering of the inner switch over the generated cases. This is the
companion of `simpleStorageNativeDispatcherInnerStmts_eq_let_if_if` with
abstract Yul witnesses replaced by concrete syntax. -/
theorem simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_if :
    ∃ (body1 body2 : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some
              (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
                (Yul.YulExpr.call "iszero"
                  [Yul.YulExpr.call "lt"
                    [Yul.YulExpr.call "calldatasize" [],
                     Yul.YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
              (Yul.YulExpr.call "iszero"
                [Yul.YulExpr.ident "__has_selector"]))
            body1,
         EvmYul.Yul.Ast.Stmt.If
            (Compiler.Proofs.YulGeneration.Backends.lowerExprNative
              (Yul.YulExpr.ident "__has_selector"))
            body2] := by
  have hOk := simpleStorageNativeDispatcherStmts_lowering_ok
  rw [simpleStorageNativeDispatcherStmts_eq_singleton_block] at hOk
  obtain ⟨_, hInner⟩ := lowerStmtsNative_block_stmts_eq _ _ hOk
  obtain ⟨rest', hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, rest'', hIf1, _, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨body2', _, rest''', hIf2, _, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  rw [hIf2] at hIf1
  rw [hIf1] at hLet
  exact ⟨body1', body2', hLet⟩

/-- Strengthened concrete-form equation for the SimpleStorage native dispatcher
inner-block: same as `simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_if`
except the body of the second (selector-hit) `If` is pinned to a singleton
`lowerNativeSwitchBlock` over the source-Yul `selectorExpr` scrutinee. The
selector cases and default body remain existential because they depend on the
contract's `functions` list. This is the next dispatcher peel beyond the
let/if/if shape and is the foundation for replacing the Classical.choose-pinned
`simpleStorageNativeDispatcher_if2Body` with a concrete switch block. -/
theorem simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (default' : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcherInnerStmts =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero"
                [Yul.YulExpr.call "lt"
                  [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident "__has_selector"]))
            body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases' default']] := by
  have hOk := simpleStorageNativeDispatcherStmts_lowering_ok
  rw [simpleStorageNativeDispatcherStmts_eq_singleton_block] at hOk
  obtain ⟨_, hInner⟩ := lowerStmtsNative_block_stmts_eq _ _ hOk
  obtain ⟨_, hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, _, hIf1, _, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨_, _, _, hIf2, hBody2, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  obtain ⟨cases', default', hBody2Eq⟩ :=
    lowerStmtsNativeWithSwitchIds_singleton_switch_eq _ _ _ _ _ _ _ hBody2
  rw [hBody2Eq] at hIf2; rw [hIf2] at hIf1; rw [hIf1] at hLet
  exact ⟨body1', _, cases', default', hLet⟩

/-- WithSwitchIds-form companion of `lowerStmtsNative_revert_zero_zero`: at any
`reservedNames`/`nextSwitchId` pair, the singleton list `[expr (revert(0,0))]`
emitted by `defaultDispatchCase none none` lowers to
`[nativeRevertZeroZeroStmt]` while leaving the switch counter unchanged. The
dispatcher peel uses `lowerStmtsNativeWithSwitchIds` directly (via
`_block_stmts_eq` / `_let_head_eq` / `_if_head_eq`), so the wrapper-level
`lowerStmtsNative_revert_zero_zero` lemma alone is insufficient when pinning
the selector-miss `If` body. -/
theorem lowerStmtsNativeWithSwitchIds_revert_zero_zero
    (reservedNames : List String) (n : Nat) :
    Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds
        reservedNames n
        [Yul.YulStmt.expr (Yul.YulExpr.call "revert"
          [Yul.YulExpr.lit 0, Yul.YulExpr.lit 0])] =
      .ok ([Backends.Native.nativeRevertZeroZeroStmt], n) := by
  simp [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds,
        Backends.Native.nativeRevertZeroZeroStmt,
        Compiler.Proofs.YulGeneration.Backends.lowerExprNative,
        Compiler.Proofs.YulGeneration.Backends.lookupRuntimePrimOp]
  rfl

set_option linter.unusedSimpArgs false in
/-- Strengthened companion of `lowerStmtsNativeWithSwitchIds_singleton_switch_eq`:
when the source-level switch's `defaultCase` is fixed to the
`defaultDispatchCase none none` body — namely the singleton list
`[expr (revert(0,0))]` — the lowered default body is concretely
`[nativeRevertZeroZeroStmt]`. The lowered case bodies remain existential
(they depend on the contract `funcs` list). This pins the previously-existential
`default'` produced by `_singleton_switch_eq`, unblocking downstream proofs
that need to plug the lowered-switch exec into a concrete default-revert
endpoint. -/
theorem lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq
    (reservedNames : List String) (n0 : Nat)
    (expr : Yul.YulExpr) (cases : List (Nat × List Yul.YulStmt))
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            [Yul.YulStmt.switch expr cases
              (some [Yul.YulStmt.expr (Yul.YulExpr.call "revert"
                [Yul.YulExpr.lit 0, Yul.YulExpr.lit 0])])] = .ok (inner, next)) :
    ∃ (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      inner = [Backends.lowerNativeSwitchBlock expr
        (Backends.freshNativeSwitchId reservedNames n0) cases'
        [Backends.Native.nativeRevertZeroZeroStmt]] := by
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons,
      Backends.lowerStmtGroupNativeWithSwitchIds_switch] at h
  dsimp only [] at h
  cases hCases : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) cases with
  | error _ =>
      rw [hCases] at h; simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok casesPair =>
      obtain ⟨cases', midN⟩ := casesPair
      rw [hCases] at h
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      rw [lowerStmtsNativeWithSwitchIds_revert_zero_zero] at h
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
        Backends.lowerStmtsNativeWithSwitchIds_nil,
        List.singleton_append, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨cases', h.1.symm⟩

set_option linter.unusedSimpArgs false in
/-- Source-lowered companion of `_singleton_switch_revert_default_eq`: also
exposes the `lowerSwitchCasesNativeWithSwitchIds` equation linking the source
case list to the lowered `cases'`. Downstream selector-miss reductions chain
this with `lowerSwitchCasesNativeWithSwitchIds_tags_eq` /
`lowerSwitchCasesNativeWithSwitchIds_find?_none` to lift source-level selector
facts through the lowering. -/
theorem lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered
    (reservedNames : List String) (n0 : Nat)
    (expr : Yul.YulExpr) (cases : List (Nat × List Yul.YulStmt))
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            [Yul.YulStmt.switch expr cases
              (some [Yul.YulStmt.expr (Yul.YulExpr.call "revert"
                [Yul.YulExpr.lit 0, Yul.YulExpr.lit 0])])] = .ok (inner, next)) :
    ∃ (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      inner = [Backends.lowerNativeSwitchBlock expr
        (Backends.freshNativeSwitchId reservedNames n0) cases'
        [Backends.Native.nativeRevertZeroZeroStmt]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) cases =
          .ok (cases', midN) := by
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons,
      Backends.lowerStmtGroupNativeWithSwitchIds_switch] at h
  dsimp only [] at h
  cases hCases : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) cases with
  | error _ =>
      rw [hCases] at h; simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok casesPair =>
      obtain ⟨cases', midN⟩ := casesPair
      rw [hCases] at h
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      rw [lowerStmtsNativeWithSwitchIds_revert_zero_zero] at h
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
        Backends.lowerStmtsNativeWithSwitchIds_nil,
        List.singleton_append, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨cases', midN, h.1.symm, rfl⟩

/-- Strengthened companion of `simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton`:
the lowered default body of the inner switch is pinned to the concrete
`[nativeRevertZeroZeroStmt]` singleton. The lowered case bodies (and the
selector-miss `If` body `body1`) remain existential as before. Combines the
existing concrete decomposition with the new
`lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq`, exploiting
the definitional fact that `simpleStorageIRContract` has both `fallback` and
`receive` set to `none`, so the switch's source-level `defaultCase` is
`defaultDispatchCase none none = [revert(0,0)]`. -/
theorem simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton_revert_default :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      simpleStorageNativeDispatcherInnerStmts =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero"
                [Yul.YulExpr.call "lt"
                  [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident "__has_selector"]))
            body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases'
              [Backends.Native.nativeRevertZeroZeroStmt]]] := by
  have hOk := simpleStorageNativeDispatcherStmts_lowering_ok
  rw [simpleStorageNativeDispatcherStmts_eq_singleton_block] at hOk
  obtain ⟨_, hInner⟩ := lowerStmtsNative_block_stmts_eq _ _ hOk
  obtain ⟨_, hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, _, hIf1, _, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨_, _, _, hIf2, hBody2, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  obtain ⟨cases', hBody2Eq⟩ :=
    lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq
      _ _ _ _ _ _ hBody2
  rw [hBody2Eq] at hIf2; rw [hIf2] at hIf1; rw [hIf1] at hLet
  exact ⟨body1', _, cases', hLet⟩

/-- The source-level switch cases that `buildSwitch` emits for SimpleStorage
(one entry per source IR function, keyed by selector). Used by the
`_sourceLowered` companion below as the explicit input to
`lowerSwitchCasesNativeWithSwitchIds`, anchoring the switch lowering to the
concrete source-level selector list. -/
abbrev simpleStorageBuildSwitchSourceCases : List (Nat × List Yul.YulStmt) :=
  simpleStorageIRContract.functions.map (fun fn =>
    (fn.selector,
      Compiler.CodegenCommon.dispatchBody fn.payable s!"{fn.name}()"
        ([Compiler.CodegenCommon.calldatasizeGuard fn.params.length] ++ fn.body)))

/-- Source-lowered companion of `_eq_concrete_let_if_switchSingleton_revert_default`:
additionally exposes the lowering equation for the buildSwitch-emitted source
case list `simpleStorageBuildSwitchSourceCases` into the lowered `cases'`.
Bridge lemma for the selector-miss closed-form: chained with
`lowerSwitchCasesNativeWithSwitchIds_tags_eq` it converts source-level
selector facts into lowered-level `find?` results. -/
theorem simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton_revert_default_sourceLowered :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      simpleStorageNativeDispatcherInnerStmts =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some (Backends.lowerExprNative (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident "__has_selector"])) body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [Backends.Native.nativeRevertZeroZeroStmt]]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        simpleStorageBuildSwitchSourceCases = .ok (cases', midN) := by
  have hOk := simpleStorageNativeDispatcherStmts_lowering_ok
  rw [simpleStorageNativeDispatcherStmts_eq_singleton_block] at hOk
  obtain ⟨_, hInner⟩ := lowerStmtsNative_block_stmts_eq _ _ hOk
  obtain ⟨_, hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, _, hIf1, _, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨_, _, _, hIf2, hBody2, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  obtain ⟨cases', midN, hBody2Eq, hLowerCases⟩ :=
    lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered
      _ _ _ _ _ _ hBody2
  rw [hBody2Eq] at hIf2; rw [hIf2] at hIf1; rw [hIf1] at hLet
  exact ⟨body1', _, _, cases', midN, hLet, hLowerCases⟩

/-- The `Classical.choose`-pinned let RHS of the SimpleStorage native dispatcher
equals the lowered `iszero(lt(calldatasize(), 4))` Yul expression that
`buildSwitch` emits. Combining the named-form decomposition
(`simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if`) with the
concrete-head exposure
(`simpleStorageNativeDispatcherInnerStmts_concrete_let_head`) and head
injection eliminates the structural existential between the named witness and
the concrete source expression, letting downstream proofs evaluate the let
RHS directly via the existing harness lemmas. -/
theorem simpleStorageNativeDispatcher_letValue_eq :
    simpleStorageNativeDispatcher_letValue =
      Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.call "iszero"
          [Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [],
             Yul.YulExpr.lit 4]]) := by
  obtain ⟨_, hConcrete⟩ :=
    simpleStorageNativeDispatcherInnerStmts_concrete_let_head
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.Let.injEq, Option.some.injEq,
    true_and] at hCombo
  exact hCombo.1

/-- The `Classical.choose`-pinned selector-miss guard condition of the
SimpleStorage native dispatcher equals the lowered `iszero(__has_selector)`
Yul expression that `buildSwitch` emits. Derived by head injection from the
concrete-form full equation and the named-form decomposition. -/
theorem simpleStorageNativeDispatcher_if1Cond_eq :
    simpleStorageNativeDispatcher_if1Cond =
      Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.call "iszero"
          [Yul.YulExpr.ident "__has_selector"]) := by
  obtain ⟨_, _, hConcrete⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_if
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact hCombo.2.1.1

/-- The `Classical.choose`-pinned selector-hit guard condition of the
SimpleStorage native dispatcher equals the lowered `__has_selector` ident
expression that `buildSwitch` emits. Derived by head injection from the
concrete-form full equation and the named-form decomposition. -/
theorem simpleStorageNativeDispatcher_if2Cond_eq :
    simpleStorageNativeDispatcher_if2Cond =
      Compiler.Proofs.YulGeneration.Backends.lowerExprNative
        (Yul.YulExpr.ident "__has_selector") := by
  obtain ⟨_, _, hConcrete⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_if
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact hCombo.2.2.1.1

/-- The `Classical.choose`-pinned selector-hit `If` body of the SimpleStorage
native dispatcher equals a singleton `lowerNativeSwitchBlock` over the
source-Yul `selectorExpr` (i.e., `shr(selectorShift, calldataload(0))`). The
switch-id, lowered case bodies, and lowered default body remain existential
because they depend on the concrete contract `functions` list — but their
existence as a closed-form switch block is enough to drive the next dispatcher
peel into selector-case dispatch. Derived by head injection from the
strengthened concrete-form `_eq_concrete_let_if_switchSingleton` and the
named-form decomposition. -/
theorem simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_exists :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (default' : List EvmYul.Yul.Ast.Stmt),
      simpleStorageNativeDispatcher_if2Body =
        [Compiler.Proofs.YulGeneration.Backends.lowerNativeSwitchBlock
          (Yul.YulExpr.call "shr"
            [Yul.YulExpr.lit Compiler.Constants.selectorShift,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
          switchId cases' default'] := by
  obtain ⟨_, switchId, cases', default', hConcrete⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact ⟨switchId, cases', default', hCombo.2.2.1.2⟩

/-- Strengthened companion of `simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_exists`:
the lowered default body of the dispatcher's selector-hit switch is pinned to
`[nativeRevertZeroZeroStmt]`. Derived by head injection from the strengthened
concrete-form `_eq_concrete_let_if_switchSingleton_revert_default` and the
named-form decomposition. -/
theorem simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_revert_default_exists :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      simpleStorageNativeDispatcher_if2Body =
        [Compiler.Proofs.YulGeneration.Backends.lowerNativeSwitchBlock
          (Yul.YulExpr.call "shr"
            [Yul.YulExpr.lit Compiler.Constants.selectorShift,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
          switchId cases'
          [Backends.Native.nativeRevertZeroZeroStmt]] := by
  obtain ⟨_, switchId, cases', hConcrete⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton_revert_default
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact ⟨switchId, cases', hCombo.2.2.1.2⟩

/-- Source-lowered companion of `_if2Body_eq_lowerSwitchBlock_revert_default_exists`:
the `if2Body` equality additionally exposes `switchId =
freshNativeSwitchId reservedNames n0` and the source-cases lowering equation
linking `simpleStorageBuildSwitchSourceCases` to the lowered `cases'`. This is
the form the dispatcher selector-miss closed-form consumes — chaining it with
`lowerSwitchCasesNativeWithSwitchIds_tags_eq` lifts source-level selector
facts through the lowering. -/
theorem simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_revert_default_sourceLowered :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      simpleStorageNativeDispatcher_if2Body =
        [Compiler.Proofs.YulGeneration.Backends.lowerNativeSwitchBlock
          (Yul.YulExpr.call "shr"
            [Yul.YulExpr.lit Compiler.Constants.selectorShift,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
          (Backends.freshNativeSwitchId reservedNames n0) cases'
          [Backends.Native.nativeRevertZeroZeroStmt]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        simpleStorageBuildSwitchSourceCases = .ok (cases', midN) := by
  obtain ⟨_, reservedNames, n0, cases', midN, hConcrete, hLowerCases⟩ :=
    simpleStorageNativeDispatcherInnerStmts_eq_concrete_let_if_switchSingleton_revert_default_sourceLowered
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hConcrete
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact ⟨reservedNames, n0, cases', midN, hCombo.2.2.1.2, hLowerCases⟩

/-- The `Classical.choose`-pinned selector-miss `If` body of the SimpleStorage
native dispatcher equals the singleton list `[nativeRevertZeroZeroStmt]`.
Combines `simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if` with a
fully-pinned concrete-form decomposition of the inner block (where body1 is
also pinned via the WithSwitchIds revert lowering equation), then uses head
injection on the second `If` to extract the body equation. Lets downstream
selector-miss exec proofs invoke `exec_revert_zero_zero_error` directly. -/
theorem simpleStorageNativeDispatcher_if1Body_eq :
    simpleStorageNativeDispatcher_if1Body =
      [Backends.Native.nativeRevertZeroZeroStmt] := by
  have hOk := simpleStorageNativeDispatcherStmts_lowering_ok
  rw [simpleStorageNativeDispatcherStmts_eq_singleton_block] at hOk
  obtain ⟨_, hInner⟩ := lowerStmtsNative_block_stmts_eq _ _ hOk
  obtain ⟨rest', hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, rest'', hIf1, hBody1, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨body2', _, rest''', hIf2, _, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Compiler.Proofs.YulGeneration.Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  have hDef :
      Compiler.CodegenCommon.defaultDispatchCase
          (none : Option Compiler.IREntrypoint)
          (none : Option Compiler.IREntrypoint) =
        [Yul.YulStmt.expr
          (Yul.YulExpr.call "revert" [Yul.YulExpr.lit 0, Yul.YulExpr.lit 0])] :=
    rfl
  rw [hDef, lowerStmtsNativeWithSwitchIds_revert_zero_zero,
      Except.ok.injEq, Prod.mk.injEq] at hBody1
  obtain ⟨hBody1Eq, _⟩ := hBody1
  subst hBody1Eq
  rw [hIf2] at hIf1
  rw [hIf1] at hLet
  have hCombo :=
    simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if.symm.trans hLet
  simp only [List.cons.injEq, EvmYul.Yul.Ast.Stmt.If.injEq] at hCombo
  exact hCombo.2.1.2

/-- Closed-form selector-miss revert exec for the SimpleStorage native
dispatcher's first `If` body. The body is the singleton list
`[nativeRevertZeroZeroStmt]` (by `simpleStorageNativeDispatcher_if1Body_eq`),
so a `.Block` execution at any fuel `≥ 7` peels the head via
`exec_block_cons_error` and reduces to `exec_revert_zero_zero_error`,
producing EVMYulLean's `Revert` exception. Self-contained — no premise on
state/eval is needed because the body has no side effects before the revert.

This is the per-statement halt lemma the selector-miss dispatcher proof will
chain after the `let __has_selector := …` and `if iszero(__has_selector)`
peels: once `__has_selector = 0` is established, the if guard fires, and this
lemma immediately closes the dispatcher result as `.error Revert`. -/
theorem exec_block_simpleStorageNativeDispatcher_if1Body_revert
    (fuel : Nat) (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.exec (fuel + 7) (.Block simpleStorageNativeDispatcher_if1Body)
        codeOverride state =
      .error EvmYul.Yul.Exception.Revert := by
  rw [simpleStorageNativeDispatcher_if1Body_eq]
  exact Compiler.Proofs.YulGeneration.Backends.Native.exec_block_cons_error
    (fuel + 6)
    Compiler.Proofs.YulGeneration.Backends.Native.nativeRevertZeroZeroStmt
    [] codeOverride state EvmYul.Yul.Exception.Revert
    (Compiler.Proofs.YulGeneration.Backends.Native.exec_revert_zero_zero_error
      fuel state codeOverride)

/-- Composed dispatcher peel exposing the SimpleStorage native dispatcher's
inner three-statement block exec as a singleton `lowerNativeSwitchBlock` exec
on the post-Let state. Chains the named let/if/if normalization with the
let-selector / if1-skip / if2-take peel
(`exec_block_letSelector_if1Skip_if2Take_initialState_fuel`, which discharges
calldatasize ≥ 4 via `hNoWrap` so the let binds `__has_selector` to 1) and the
just-landed `simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_exists`
characterization, leaving the dispatcher inner-block exec equal to a single
lowered switch-block exec on
`(nativeSwitchInitialOkState).insert "__has_selector" 1`. The switch-id,
lowered case bodies, and lowered default body remain existential — they are
fixed by the concrete `simpleStorageIRContract.functions` list and threaded
through later case-dispatch peels using
`exec_lowerNativeSwitchBlock_simpleStorageConcrete_*` lemmas. -/
theorem exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_exec
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (default' : List EvmYul.Yul.Ast.Stmt),
      EvmYul.Yul.exec (fuel + 12)
          (.Block simpleStorageNativeDispatcherInnerStmts)
          (some contract)
          (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            contract tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases' default'])
          (some contract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            contract tx storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
  obtain ⟨switchId, cases', default', hIf2Body⟩ :=
    simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_exists
  refine ⟨switchId, cases', default', ?_⟩
  rw [simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if,
      simpleStorageNativeDispatcher_letValue_eq,
      simpleStorageNativeDispatcher_if1Cond_eq,
      simpleStorageNativeDispatcher_if2Cond_eq, hIf2Body]
  exact Backends.Native.exec_block_letSelector_if1Skip_if2Take_initialState_fuel
    fuel contract tx storage observableSlots "__has_selector"
    simpleStorageNativeDispatcher_if1Body
    [Backends.lowerNativeSwitchBlock
      (Yul.YulExpr.call "shr"
        [Yul.YulExpr.lit Compiler.Constants.selectorShift,
         Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
      switchId cases' default']
    hNoWrap

/-- Strengthened companion of `exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_exec`
where the lowered default body of the inner switch is pinned to
`[nativeRevertZeroZeroStmt]`. Uses
`simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_revert_default_exists`
in place of the unpinned existential variant. -/
theorem exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_revert_default_exec
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      EvmYul.Yul.exec (fuel + 12)
          (.Block simpleStorageNativeDispatcherInnerStmts)
          (some contract)
          (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            contract tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases'
              [Backends.Native.nativeRevertZeroZeroStmt]])
          (some contract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            contract tx storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
  obtain ⟨switchId, cases', hIf2Body⟩ :=
    simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_revert_default_exists
  refine ⟨switchId, cases', ?_⟩
  rw [simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if,
      simpleStorageNativeDispatcher_letValue_eq,
      simpleStorageNativeDispatcher_if1Cond_eq,
      simpleStorageNativeDispatcher_if2Cond_eq, hIf2Body]
  exact Backends.Native.exec_block_letSelector_if1Skip_if2Take_initialState_fuel
    fuel contract tx storage observableSlots "__has_selector"
    simpleStorageNativeDispatcher_if1Body
    [Backends.lowerNativeSwitchBlock
      (Yul.YulExpr.call "shr"
        [Yul.YulExpr.lit Compiler.Constants.selectorShift,
         Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
      switchId cases'
      [Backends.Native.nativeRevertZeroZeroStmt]]
    hNoWrap

/-- Source-lowered companion of `exec_block_..._eq_lowerNativeSwitchBlock_revert_default_exec`:
the inner-stmts-to-lowered-switch-block exec equation additionally exposes
`switchId = freshNativeSwitchId reservedNames n0` and the source-cases lowering
equation linking `simpleStorageBuildSwitchSourceCases` to the lowered `cases'`.
Built by switching the underlying `if2Body` decomposition to its sourceLowered
companion. -/
theorem exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      EvmYul.Yul.exec (fuel + 12)
          (.Block simpleStorageNativeDispatcherInnerStmts)
          (some contract)
          (Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            contract tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [Backends.Native.nativeRevertZeroZeroStmt]])
          (some contract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            contract tx storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        simpleStorageBuildSwitchSourceCases = .ok (cases', midN) := by
  obtain ⟨reservedNames, n0, cases', midN, hIf2Body, hLowerCases⟩ :=
    simpleStorageNativeDispatcher_if2Body_eq_lowerSwitchBlock_revert_default_sourceLowered
  refine ⟨reservedNames, n0, cases', midN, ?_, hLowerCases⟩
  rw [simpleStorageNativeDispatcherInnerStmts_eq_named_let_if_if,
      simpleStorageNativeDispatcher_letValue_eq,
      simpleStorageNativeDispatcher_if1Cond_eq,
      simpleStorageNativeDispatcher_if2Cond_eq, hIf2Body]
  exact Backends.Native.exec_block_letSelector_if1Skip_if2Take_initialState_fuel
    fuel contract tx storage observableSlots "__has_selector"
    simpleStorageNativeDispatcher_if1Body
    [Backends.lowerNativeSwitchBlock
      (Yul.YulExpr.call "shr"
        [Yul.YulExpr.lit Compiler.Constants.selectorShift,
         Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
      (Backends.freshNativeSwitchId reservedNames n0) cases'
      [Backends.Native.nativeRevertZeroZeroStmt]]
    hNoWrap

/-- Bridge-level lift of the inner-block-to-lowerNativeSwitchBlock combinator:
chains `simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec` with the
just-landed `_innerStmts_eq_lowerNativeSwitchBlock_exec`, so the bridge's
`contractDispatcherExecResult` at fuel `peeledFuel + 14` reduces to an exec of
a singleton lowered-switch block at fuel `peeledFuel + 8` on
`(initialOk).insert "__has_selector" 1`. -/
theorem simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_exec
    (peeledFuel : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (default' : List EvmYul.Yul.Ast.Stmt),
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (peeledFuel + 14)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (peeledFuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases' default'])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
  obtain ⟨switchId, cases', default', hExec⟩ :=
    exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_exec
      peeledFuel Compiler.SimpleStorageNativeWitness.nativeContract
      tx storage observableSlots hNoWrap
  refine ⟨switchId, cases', default', ?_⟩
  have hShape : peeledFuel + 14 =
      Nat.succ (Nat.succ (Nat.succ (peeledFuel + 11))) := by omega
  rw [hShape, simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec
        (peeledFuel + 11) tx storage observableSlots]
  exact hExec

/-- Strengthened companion of `simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_exec`
with the lowered default body pinned to `[nativeRevertZeroZeroStmt]`. Chains
the `_innerBlock_exec` combinator with the strengthened
`_innerStmts_eq_lowerNativeSwitchBlock_revert_default_exec`. This is the entry
point that downstream selector-miss bridge proofs will plug into the new
store-parametric `exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_fuel`
endpoint. -/
theorem simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec
    (peeledFuel : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (switchId : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (peeledFuel + 14)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (peeledFuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases'
              [Backends.Native.nativeRevertZeroZeroStmt]])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
  obtain ⟨switchId, cases', hExec⟩ :=
    exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_revert_default_exec
      peeledFuel Compiler.SimpleStorageNativeWitness.nativeContract
      tx storage observableSlots hNoWrap
  refine ⟨switchId, cases', ?_⟩
  have hShape : peeledFuel + 14 =
      Nat.succ (Nat.succ (Nat.succ (peeledFuel + 11))) := by omega
  rw [hShape, simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec
        (peeledFuel + 11) tx storage observableSlots]
  exact hExec

/-- Source-lowered companion of `_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec`:
the dispatcher-level reduction additionally exposes
`switchId = freshNativeSwitchId reservedNames n0` and the source-cases lowering
equation. This is the form selector-miss closed-form proofs will consume —
they open the existential, then chain `lowerSwitchCasesNativeWithSwitchIds_tags_eq`
to lift source-level selector facts (decided from `simpleStorageIRContract`)
into the lowered `cases'.find?` results required by the `_via_reduction`
endpoint. -/
theorem simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
    (peeledFuel : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    ∃ (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (peeledFuel + 14)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (peeledFuel + 8)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [Backends.Native.nativeRevertZeroZeroStmt]])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        simpleStorageBuildSwitchSourceCases = .ok (cases', midN) := by
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    exec_block_simpleStorageNativeDispatcherInnerStmts_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      peeledFuel Compiler.SimpleStorageNativeWitness.nativeContract
      tx storage observableSlots hNoWrap
  refine ⟨reservedNames, n0, cases', midN, ?_, hLowerCases⟩
  have hShape : peeledFuel + 14 =
      Nat.succ (Nat.succ (Nat.succ (peeledFuel + 11))) := by omega
  rw [hShape, simpleStorageNativeContract_dispatcherExec_eq_innerBlock_exec
        (peeledFuel + 11) tx storage observableSlots]
  exact hExec

/-- Bridge-level selector-miss endpoint, parametric in `cases'` and `switchId`:
composes the harness-level
`exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_error` with
the strengthened-reduction equation at the matching fuel
`peeledFuel = fuel + cases'.length + 5`. The reduction equation is taken as a
hypothesis so the caller can pin a specific `cases'` (e.g. by opening the
existential of `_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec`)
without forcing the fuel parameter to depend on a not-yet-bound term. This is
the direct selector-miss discharge composing into
`contractDispatcherExecResult = .error Revert`. -/
theorem simpleStorageNativeContract_dispatcherExec_selectorMiss_revert_via_reduction
    (fuel selector switchId : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hFind : cases'.find? (fun entry => entry.1 == selector) = none)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases' → tag < EvmYul.UInt256.size)
    (hReduction :
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (fuel + cases'.length + 19)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block
            [Backends.lowerNativeSwitchBlock
              (Yul.YulExpr.call "shr"
                [Yul.YulExpr.lit Compiler.Constants.selectorShift,
                 Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
              switchId cases'
              [Backends.Native.nativeRevertZeroZeroStmt]])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1))) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + cases'.length + 19)
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert := by
  rw [hReduction]
  exact Backends.Native.exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_error
    fuel selector switchId cases'
    Compiler.SimpleStorageNativeWitness.nativeContract
    tx storage observableSlots hSelector hFind hSelectorRange hTagsRange

/-- The source-level switch cases emitted by `buildSwitch` for SimpleStorage
project to the concrete two-element selector list `[0x6057361d, 0x2e64cec1]`.
This anchors source-level selector-miss reasoning at the IR layer so the rest
of the dispatcher proof can stay parametric in `cases'`. -/
theorem simpleStorageBuildSwitchSourceCases_map_fst :
    simpleStorageBuildSwitchSourceCases.map (·.1) =
      [(0x6057361d : Nat), (0x2e64cec1 : Nat)] := rfl

/-- Source-cases find?-none for SimpleStorage: the selector-miss assumption
`sel ≠ 0x6057361d ∧ sel ≠ 0x2e64cec1` (the two SimpleStorage IR selectors)
suffices to discharge `find?` on the buildSwitch-emitted source case list.
This is the source-level half of the selector-miss closed form. -/
theorem simpleStorageBuildSwitchSourceCases_find?_none {sel : Nat}
    (h1 : sel ≠ 0x6057361d) (h2 : sel ≠ 0x2e64cec1) :
    simpleStorageBuildSwitchSourceCases.find? (fun entry => entry.1 == sel) =
      none := by
  show ([_, _] : List _).find? _ = none
  simp only [List.find?_cons, List.find?_nil]
  have hb1 : ((0x6057361d : Nat) == sel) = false :=
    beq_eq_false_iff_ne.mpr (Ne.symm h1)
  have hb2 : ((0x2e64cec1 : Nat) == sel) = false :=
    beq_eq_false_iff_ne.mpr (Ne.symm h2)
  rw [hb1, hb2]

/-- All tags in the buildSwitch-emitted source cases for SimpleStorage are
strictly less than `EvmYul.UInt256.size = 2^256`. The two source selectors
(`0x6057361d`, `0x2e64cec1`) both fit in 32 bits, far below the EVM word
modulus. -/
theorem simpleStorageBuildSwitchSourceCases_tags_lt_uint256_size :
    ∀ tag body, (tag, body) ∈ simpleStorageBuildSwitchSourceCases →
      tag < EvmYul.UInt256.size := by
  intro tag body h
  simp only [simpleStorageBuildSwitchSourceCases, simpleStorageIRContract,
    List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq,
    List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

/-- Shape characterization for the lowered SimpleStorage source switch cases.

Exactly two entries — the SimpleStorage IR selectors `0x6057361d` and
`0x2e64cec1` — flow through `lowerSwitchCasesNativeWithSwitchIds`, so the
output `cases'` is forced to a two-element shape with lowered bodies. Each
selector tag is preserved unchanged by the lowering; only the case bodies
are recursively lowered. Hit-case proofs consume this shape to convert the
parametric `cases'` (opened from the `_sourceLowered` existential) into the
concrete `[(0x6057361d, _), (0x2e64cec1, _)]` form that matches the
generic harness lemmas like
`exec_lowerNativeSwitchBlock_simpleStorageSelectors_store_hit_error_fuel`. -/
theorem simpleStorageBuildSwitchSourceCases_lowered_shape
    (reservedNames : List String) (nextSwitchId final : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLower :
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId
        simpleStorageBuildSwitchSourceCases = .ok (cases', final)) :
    ∃ storeBody' retrieveBody',
      cases' = [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')] := by
  have hTags := Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq
    _ _ _ _ _ hLower
  have hLen := Backends.lowerSwitchCasesNativeWithSwitchIds_length_eq
    _ _ _ _ _ hLower
  rw [simpleStorageBuildSwitchSourceCases_map_fst] at hTags
  match cases', hLen, hTags with
  | [(t1, b1), (t2, b2)], _, hTags =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hTags
    obtain ⟨ht1, ht2⟩ := hTags
    exact ⟨b1, b2, by rw [ht1, ht2]⟩

/-- Lowered native body shape of the `store(uint256)` selector arm of the
SimpleStorage source switch cases (leading `.Block []` from the `dispatchBody`
comment, followed by callvalue/calldatasize guards and the calldataload/
sstore/stop primitive sequence). Pinning this lets downstream hit-case proofs
specialize to a fixed concrete body instead of carrying a parametric
`storeBody'`. -/
def simpleStorageLoweredStoreCaseBody : List EvmYul.Yul.Ast.Stmt :=
  [EvmYul.Yul.Ast.Stmt.Block [],
   .If (Backends.lowerExprNative (.call "callvalue" []))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 36]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .Let ["value"] (some (Backends.lowerExprNative
     (.call "calldataload" [.lit 4]))),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "sstore" [.lit 0, .ident "value"])),
   .ExprStmtCall (Backends.lowerExprNative (.call "stop" []))]

/-- Lowered native body shape of the `retrieve()` selector arm of the
SimpleStorage source switch cases. Mirrors `simpleStorageLoweredStoreCaseBody`
for the source `mstore(0, sload(0)); return(0, 32)` body. -/
def simpleStorageLoweredRetrieveCaseBody : List EvmYul.Yul.Ast.Stmt :=
  [EvmYul.Yul.Ast.Stmt.Block [],
   .If (Backends.lowerExprNative (.call "callvalue" []))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 4]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .ExprStmtCall (Backends.lowerExprNative
     (.call "mstore" [.lit 0, .call "sload" [.lit 0]])),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "return" [.lit 0, .lit 32]))]

/-- 5-statement tail of `simpleStorageLoweredStoreCaseBody`, with the leading
no-op `.Block []` (from the `dispatchBody` source comment) stripped. -/
def simpleStorageLoweredStoreCaseBodyTail : List EvmYul.Yul.Ast.Stmt :=
  [.If (Backends.lowerExprNative (.call "callvalue" []))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 36]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .Let ["value"] (some (Backends.lowerExprNative
     (.call "calldataload" [.lit 4]))),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "sstore" [.lit 0, .ident "value"])),
   .ExprStmtCall (Backends.lowerExprNative (.call "stop" []))]

/-- 4-statement tail of `simpleStorageLoweredRetrieveCaseBody`, with the leading
no-op `.Block []` (from the `dispatchBody` source comment) stripped. -/
def simpleStorageLoweredRetrieveCaseBodyTail : List EvmYul.Yul.Ast.Stmt :=
  [.If (Backends.lowerExprNative (.call "callvalue" []))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 4]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .ExprStmtCall (Backends.lowerExprNative
     (.call "mstore" [.lit 0, .call "sload" [.lit 0]])),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "return" [.lit 0, .lit 32]))]

/-- Strip the leading `.Block []` no-op (a `dispatchBody` source-comment
artifact) from the lowered store-case body when proving a `.error err`
obligation. Combines `exec_block_nil_ok` (the empty inner block is a no-op at
positive fuel, returning the input state unchanged) with
`exec_block_cons_tail_error` (a successful head followed by an erroring tail
makes the whole block error). Reduces a 6-statement obligation to a strictly
smaller 5-statement tail obligation. -/
theorem exec_block_simpleStorageLoweredStoreCaseBody_head_strip_error
    (fuel' : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) (err : EvmYul.Yul.Exception)
    (hTail :
      EvmYul.Yul.exec (fuel' + 1)
        (.Block simpleStorageLoweredStoreCaseBodyTail) codeOverride state =
        .error err) :
    EvmYul.Yul.exec (fuel' + 2)
      (.Block simpleStorageLoweredStoreCaseBody) codeOverride state =
      .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel' + 1))
    (.Block (.Block [] :: simpleStorageLoweredStoreCaseBodyTail))
    codeOverride state = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel' + 1) (.Block [])
    simpleStorageLoweredStoreCaseBodyTail codeOverride state state err ?_ hTail
  exact Backends.Native.exec_block_nil_ok fuel' codeOverride state

/-- Retrieve-case dual of
`exec_block_simpleStorageLoweredStoreCaseBody_head_strip_error`. -/
theorem exec_block_simpleStorageLoweredRetrieveCaseBody_head_strip_error
    (fuel' : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) (err : EvmYul.Yul.Exception)
    (hTail :
      EvmYul.Yul.exec (fuel' + 1)
        (.Block simpleStorageLoweredRetrieveCaseBodyTail) codeOverride state =
        .error err) :
    EvmYul.Yul.exec (fuel' + 2)
      (.Block simpleStorageLoweredRetrieveCaseBody) codeOverride state =
      .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel' + 1))
    (.Block (.Block [] :: simpleStorageLoweredRetrieveCaseBodyTail))
    codeOverride state = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel' + 1) (.Block [])
    simpleStorageLoweredRetrieveCaseBodyTail codeOverride state state err ?_ hTail
  exact Backends.Native.exec_block_nil_ok fuel' codeOverride state

/-- 4-statement callvalue-stripped tail of `simpleStorageLoweredStoreCaseBody`,
with both the leading no-op `.Block []` and the leading `if callvalue() {…}`
revert guard removed. Used to further shrink the dispatcher hit-case body-exec
obligation when the transaction has zero `msgValue`. -/
def simpleStorageLoweredStoreCaseBodyTail2 : List EvmYul.Yul.Ast.Stmt :=
  [.If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 36]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .Let ["value"] (some (Backends.lowerExprNative
     (.call "calldataload" [.lit 4]))),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "sstore" [.lit 0, .ident "value"])),
   .ExprStmtCall (Backends.lowerExprNative (.call "stop" []))]

/-- 3-statement calldatasize-stripped tail of
`simpleStorageLoweredStoreCaseBodyTail2`, with the argument-length revert guard
removed after proving the transaction supplies the setter argument. -/
def simpleStorageLoweredStoreCaseBodyTail3 : List EvmYul.Yul.Ast.Stmt :=
  [.Let ["value"] (some (Backends.lowerExprNative
     (.call "calldataload" [.lit 4]))),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "sstore" [.lit 0, .ident "value"])),
   .ExprStmtCall (Backends.lowerExprNative (.call "stop" []))]

/-- 3-statement callvalue-stripped tail of `simpleStorageLoweredRetrieveCaseBody`. -/
def simpleStorageLoweredRetrieveCaseBodyTail2 : List EvmYul.Yul.Ast.Stmt :=
  [.If (Backends.lowerExprNative
          (.call "lt" [.call "calldatasize" [], .lit 4]))
     [.ExprStmtCall (Backends.lowerExprNative (.call "revert" [.lit 0, .lit 0]))],
   .ExprStmtCall (Backends.lowerExprNative
     (.call "mstore" [.lit 0, .call "sload" [.lit 0]])),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "return" [.lit 0, .lit 32]))]

/-- 2-statement lt-calldatasize-stripped tail of
`simpleStorageLoweredRetrieveCaseBodyTail2`, with both the callvalue revert
guard and the inner `if lt(calldatasize, 4) {…}` argument-length revert
guard removed. Used to further shrink the dispatcher hit-case body-exec
obligation when the calldata is at least 4 bytes (which is automatic for any
ABI-conforming call since the selector itself is 4 bytes). -/
def simpleStorageLoweredRetrieveCaseBodyTail3 : List EvmYul.Yul.Ast.Stmt :=
  [.ExprStmtCall (Backends.lowerExprNative
     (.call "mstore" [.lit 0, .call "sload" [.lit 0]])),
   .ExprStmtCall (Backends.lowerExprNative
     (.call "return" [.lit 0, .lit 32]))]

/-- Strip the leading `if callvalue() { revert(0,0) }` guard from
`simpleStorageLoweredStoreCaseBodyTail` when proving a `.error err`
obligation, given that the current `executionEnv.weiValue` is zero (the
canonical zero literal). Combines the harness skip lemma
`exec_if_lowerExprNative_callvalue_skip_zero_fuel` (the callvalue guard
is a no-op at zero `weiValue`) with `exec_block_cons_tail_error` (a
successful head followed by an erroring tail makes the whole block
error). Reduces a 5-statement tail obligation to a 4-statement
callvalue-stripped tail2 obligation. -/
theorem exec_block_simpleStorageLoweredStoreCaseBodyTail_callvalue_strip_error
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hWei : shared.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal))
    (hTail2 :
      EvmYul.Yul.exec (fuel + 7) (.Block simpleStorageLoweredStoreCaseBodyTail2)
        codeOverride (.Ok shared store) = .error err) :
    EvmYul.Yul.exec (fuel + 8) (.Block simpleStorageLoweredStoreCaseBodyTail)
      codeOverride (.Ok shared store) = .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 7))
    (.Block ((simpleStorageLoweredStoreCaseBodyTail).head! ::
      simpleStorageLoweredStoreCaseBodyTail2))
    codeOverride (.Ok shared store) = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel + 7) _
    simpleStorageLoweredStoreCaseBodyTail2 codeOverride
    (.Ok shared store) (.Ok shared store) err ?_ hTail2
  show EvmYul.Yul.exec ((fuel + 1) + 6)
    (.If (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
      [.ExprStmtCall (Backends.lowerExprNative
        (.call "revert" [.lit 0, .lit 0]))])
    codeOverride (.Ok shared store) = .ok (.Ok shared store)
  exact Backends.Native.exec_if_lowerExprNative_callvalue_skip_zero_fuel
    (fuel + 1) _ codeOverride shared store hWei

/-- Retrieve-case dual of
`exec_block_simpleStorageLoweredStoreCaseBodyTail_callvalue_strip_error`. -/
theorem exec_block_simpleStorageLoweredRetrieveCaseBodyTail_callvalue_strip_error
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hWei : shared.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal))
    (hTail2 :
      EvmYul.Yul.exec (fuel + 6)
        (.Block simpleStorageLoweredRetrieveCaseBodyTail2)
        codeOverride (.Ok shared store) = .error err) :
    EvmYul.Yul.exec (fuel + 7) (.Block simpleStorageLoweredRetrieveCaseBodyTail)
      codeOverride (.Ok shared store) = .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 6))
    (.Block ((simpleStorageLoweredRetrieveCaseBodyTail).head! ::
      simpleStorageLoweredRetrieveCaseBodyTail2))
    codeOverride (.Ok shared store) = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel + 6) _
    simpleStorageLoweredRetrieveCaseBodyTail2 codeOverride
    (.Ok shared store) (.Ok shared store) err ?_ hTail2
  show EvmYul.Yul.exec ((fuel) + 6)
    (.If (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
      [.ExprStmtCall (Backends.lowerExprNative
        (.call "revert" [.lit 0, .lit 0]))])
    codeOverride (.Ok shared store) = .ok (.Ok shared store)
  exact Backends.Native.exec_if_lowerExprNative_callvalue_skip_zero_fuel
    fuel _ codeOverride shared store hWei

/-- Strip the leading `if lt(calldatasize(), 4) { revert(0,0) }` argument-length
guard from `simpleStorageLoweredRetrieveCaseBodyTail2` when proving a
`.error err` obligation, given that the current calldata has at least 4
bytes (the selector). Combines the harness skip lemma
`exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel` with
`exec_block_cons_tail_error`. Reduces a 3-statement tail2 obligation to a
2-statement lt-stripped tail3 obligation. -/
theorem exec_block_simpleStorageLoweredRetrieveCaseBodyTail2_lt_strip_error
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hGe : 4 ≤ shared.executionEnv.calldata.size)
    (hTail3 :
      EvmYul.Yul.exec (fuel + 9)
        (.Block simpleStorageLoweredRetrieveCaseBodyTail3)
        codeOverride (.Ok shared store) = .error err) :
    EvmYul.Yul.exec (fuel + 10)
      (.Block simpleStorageLoweredRetrieveCaseBodyTail2)
      codeOverride (.Ok shared store) = .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 9))
    (.Block ((simpleStorageLoweredRetrieveCaseBodyTail2).head! ::
      simpleStorageLoweredRetrieveCaseBodyTail3))
    codeOverride (.Ok shared store) = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel + 9) _
    simpleStorageLoweredRetrieveCaseBodyTail3 codeOverride
    (.Ok shared store) (.Ok shared store) err ?_ hTail3
  show EvmYul.Yul.exec (fuel + 9)
    (.If (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit 4]))
      [.ExprStmtCall (Backends.lowerExprNative
        (.call "revert" [.lit 0, .lit 0]))])
    codeOverride (.Ok shared store) = .ok (.Ok shared store)
  exact Backends.Native.exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel
    fuel _ codeOverride shared store 4 hSize (by decide) hGe

/-- Store-case dual of
`exec_block_simpleStorageLoweredRetrieveCaseBodyTail2_lt_strip_error`, with
the ABI argument guard threshold `36 = 4 + 32`. -/
theorem exec_block_simpleStorageLoweredStoreCaseBodyTail2_lt_strip_error
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hGe : 36 ≤ shared.executionEnv.calldata.size)
    (hTail3 :
      EvmYul.Yul.exec (fuel + 10)
        (.Block simpleStorageLoweredStoreCaseBodyTail3)
        codeOverride (.Ok shared store) = .error err) :
    EvmYul.Yul.exec (fuel + 11)
      (.Block simpleStorageLoweredStoreCaseBodyTail2)
      codeOverride (.Ok shared store) = .error err := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 10))
    (.Block ((simpleStorageLoweredStoreCaseBodyTail2).head! ::
      simpleStorageLoweredStoreCaseBodyTail3))
    codeOverride (.Ok shared store) = .error err
  refine Backends.Native.exec_block_cons_tail_error (fuel + 10) _
    simpleStorageLoweredStoreCaseBodyTail3 codeOverride
    (.Ok shared store) (.Ok shared store) err ?_ hTail3
  show EvmYul.Yul.exec (fuel + 10)
    (.If (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit 36]))
      [.ExprStmtCall (Backends.lowerExprNative
        (.call "revert" [.lit 0, .lit 0]))])
    codeOverride (.Ok shared store) = .ok (.Ok shared store)
  exact Backends.Native.exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel
    (fuel + 1) _ codeOverride shared store 36 hSize (by decide) hGe

/-- Store-case argument-length guard fires when calldata contains only the
selector. This is the short-calldata counterpart to
`exec_block_simpleStorageLoweredStoreCaseBodyTail2_lt_strip_error`. -/
theorem exec_block_simpleStorageLoweredStoreCaseBodyTail2_short_revert
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hSizeEq : shared.executionEnv.calldata.size = 4) :
    EvmYul.Yul.exec (fuel + 11)
      (.Block simpleStorageLoweredStoreCaseBodyTail2)
      codeOverride (.Ok shared store) =
      .error EvmYul.Yul.Exception.Revert := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 10))
    (.Block ((simpleStorageLoweredStoreCaseBodyTail2).head! ::
      simpleStorageLoweredStoreCaseBodyTail3))
    codeOverride (.Ok shared store) = .error EvmYul.Yul.Exception.Revert
  refine Backends.Native.exec_block_cons_error (fuel + 10) _
    simpleStorageLoweredStoreCaseBodyTail3 codeOverride
    (.Ok shared store) EvmYul.Yul.Exception.Revert ?_
  refine Backends.Native.exec_if_eval_nonzero_error (fuel + 9) _ _
    codeOverride (.Ok shared store) (.Ok shared store)
    (EvmYul.UInt256.ofNat 1) EvmYul.Yul.Exception.Revert ?_ ?_ ?_
  · rw [Backends.Native.eval_lowerExprNative_lt_calldatasize_ok_fuel]
    simp [hSizeEq, EvmYul.UInt256.lt, EvmYul.UInt256.ofNat, Fin.ofNat,
      EvmYul.UInt256.size]
    decide
  · change (EvmYul.UInt256.ofNat 1 : EvmYul.UInt256) ≠ ⟨0⟩
    decide
  · simpa [Backends.Native.nativeRevertZeroZeroStmt, Backends.lowerExprNative,
      Backends.lookupRuntimePrimOp] using
      (Backends.Native.exec_block_cons_error (fuel + 8)
      Backends.Native.nativeRevertZeroZeroStmt [] codeOverride
      (.Ok shared store) EvmYul.Yul.Exception.Revert
      (Backends.Native.exec_revert_zero_zero_error (fuel + 2)
        (.Ok shared store) codeOverride))

/-- Closed-form native exec of the store hit-case 3-statement payload
    `let value := calldataload(4); sstore(0, value); stop` after the
    callvalue and argument-length guards have been stripped. -/
theorem exec_block_simpleStorageLoweredStoreCaseBodyTail3_halt
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (store : EvmYul.Yul.VarStore)
    (arg : Nat) (rest : List Nat) (hArgs : tx.args = arg :: rest) :
    let initialWithStore : EvmYul.Yul.State :=
      .Ok (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    EvmYul.Yul.exec (fuel + 10)
        (.Block simpleStorageLoweredStoreCaseBodyTail3)
        codeOverride initialWithStore =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  intro initialWithStore withValue finalState
  have hWord :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.calldataload (EvmYul.UInt256.ofNat 4) =
        Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg := by
    simpa [EvmYul.Yul.State.toState] using
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataload4_arg0_word
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage observableSlots
        arg rest hArgs
  simp [simpleStorageLoweredStoreCaseBodyTail3, Backends.lowerExprNative,
    Backends.lookupRuntimePrimOp, EvmYul.Yul.exec, EvmYul.Yul.eval,
    EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.State.multifill, initialWithStore, withValue, finalState,
    hWord, EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]
  have hPerm :
      (EvmYul.Yul.State.Ok
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots).sharedState
        (Finmap.insert "value"
          (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
          store)).executionEnv.perm = true := by
    rfl
  rw [show fuel + 7 = (fuel + 6) + 1 by omega]
  rw [Compiler.Proofs.YulGeneration.Backends.Native.primCall_sstore_ok
    (fuel + 6) _ _ _ hPerm]
  rfl

/-- Composed body-level closed form for the SimpleStorage store hit-case when
the calldata contains the setter argument. -/
theorem exec_block_simpleStorageLoweredStoreCaseBody_halt
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (store : EvmYul.Yul.VarStore)
    (arg : Nat) (rest : List Nat) (hArgs : tx.args = arg :: rest)
    (hWei :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.weiValue =
      (⟨0⟩ : EvmYul.Literal))
    (hSize :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.calldata.size <
      EvmYul.UInt256.size)
    (hGe :
      36 ≤ (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.calldata.size) :
    let initialWithStore : EvmYul.Yul.State :=
      .Ok (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    EvmYul.Yul.exec (fuel + 13) (.Block simpleStorageLoweredStoreCaseBody)
        codeOverride initialWithStore =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  intro initialWithStore withValue finalState
  have hTail3 := exec_block_simpleStorageLoweredStoreCaseBodyTail3_halt
    fuel codeOverride tx storage observableSlots store arg rest hArgs
  have hTail2 := exec_block_simpleStorageLoweredStoreCaseBodyTail2_lt_strip_error
    fuel codeOverride
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState
      store _ hSize hGe hTail3
  have hTail := exec_block_simpleStorageLoweredStoreCaseBodyTail_callvalue_strip_error
    (fuel + 4) codeOverride
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState
      store _ hWei hTail2
  exact exec_block_simpleStorageLoweredStoreCaseBody_head_strip_error
    (fuel + 11) codeOverride initialWithStore _ hTail

/-- Closed-form native exec of the retrieve hit-case 2-statement payload
    `mstore(0, sload(0)) ; return(0, 32)`. EVMYulLean models `RETURN` as a
    halt error; the exec composes the harness's exec-side
    `mstore(lit, sload(lit))` seam with the exec-side `return(lit, lit)`
    halt seam through `exec_block_cons_tail_error`. The resulting halt state
    threads (i) storage-access tracking from the SLOAD on slot zero,
    (ii) the memory write of the loaded word at offset zero, and
    (iii) the post-`evmReturn` machine state holding the 32-byte return
    buffer. Discharges the `hTail3` premise of
    `exec_block_simpleStorageLoweredRetrieveCaseBodyTail2_lt_strip_error`
    unconditionally — no extra calldata/wei hypotheses needed because the
    payload reads only from storage and writes only to memory. -/
theorem exec_block_simpleStorageLoweredRetrieveCaseBodyTail3_closed
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.exec (fuel + 9)
        (.Block simpleStorageLoweredRetrieveCaseBodyTail3)
        codeOverride (.Ok shared store) =
      let (state', value) := shared.sload (EvmYul.UInt256.ofNat 0)
      let shared1 : EvmYul.SharedState .Yul := { shared with toState := state' }
      let shared2 : EvmYul.SharedState .Yul :=
        { shared1 with
          toMachineState :=
            shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
      let shared3 : EvmYul.SharedState .Yul :=
        { shared2 with
          toMachineState :=
            shared2.toMachineState.evmReturn
              (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
      .error (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store) ⟨1⟩) := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 8))
    (.Block ((simpleStorageLoweredRetrieveCaseBodyTail3).head! ::
      [(simpleStorageLoweredRetrieveCaseBodyTail3).getLast!]))
    codeOverride (.Ok shared store) = _
  refine Backends.Native.exec_block_cons_tail_error (fuel + 8) _ _ codeOverride
    (.Ok shared store) _ _
    (Backends.Native.exec_lowerExprNative_mstore_lit_sload_lit_ok_fuel
      fuel shared store codeOverride 0 0) ?_
  -- Tail [return(0, 32)] errors via the singleton-return harness lemma.
  have hSeam :=
    Backends.Native.exec_block_singleton_lowerExprNative_return_lit_lit_error_fuel
      (fuel + 1)
      ({ ({ shared with toState := (shared.sload (EvmYul.UInt256.ofNat 0)).1 }
            : EvmYul.SharedState .Yul) with
          toMachineState :=
            ({ shared with toState := (shared.sload (EvmYul.UInt256.ofNat 0)).1 }
              : EvmYul.SharedState .Yul).toMachineState.mstore
              (EvmYul.UInt256.ofNat 0) (shared.sload (EvmYul.UInt256.ofNat 0)).2 })
      store codeOverride 0 32
  have hF : (fuel + 1) + 7 = fuel + 8 := by omega
  rw [hF] at hSeam
  simpa [simpleStorageLoweredRetrieveCaseBodyTail3] using hSeam

/-- Composed body-level closed form for the SimpleStorage retrieve hit-case.
Stacks the three guard-strip lemmas (head no-op, callvalue, lt-calldatasize)
on top of `_Tail3_closed` to characterize the full lowered retrieve body's
exec output as the closed-form halt error produced by
`mstore(0, sload(0)); return(0, 32)`. The `shared3` form mirrors `_Tail3_closed`. -/
theorem exec_block_simpleStorageLoweredRetrieveCaseBody_halt
    (fuel : Nat) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hWei : shared.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal))
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hGe : 4 ≤ shared.executionEnv.calldata.size) :
    EvmYul.Yul.exec (fuel + 12) (.Block simpleStorageLoweredRetrieveCaseBody)
        codeOverride (.Ok shared store) =
      let (state', value) := shared.sload (EvmYul.UInt256.ofNat 0)
      let shared1 : EvmYul.SharedState .Yul := { shared with toState := state' }
      let shared2 : EvmYul.SharedState .Yul :=
        { shared1 with
          toMachineState :=
            shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value }
      let shared3 : EvmYul.SharedState .Yul :=
        { shared2 with
          toMachineState :=
            shared2.toMachineState.evmReturn
              (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
      .error (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store) ⟨1⟩) := by
  have hTail3 := exec_block_simpleStorageLoweredRetrieveCaseBodyTail3_closed
    fuel codeOverride shared store
  have hTail2 := exec_block_simpleStorageLoweredRetrieveCaseBodyTail2_lt_strip_error
    fuel codeOverride shared store _ hSize hGe hTail3
  have hTail := exec_block_simpleStorageLoweredRetrieveCaseBodyTail_callvalue_strip_error
    (fuel + 4) codeOverride shared store _ hWei hTail2
  exact exec_block_simpleStorageLoweredRetrieveCaseBody_head_strip_error
    (fuel + 10) codeOverride (.Ok shared store) _ hTail

/-- Concrete characterization of the lowered SimpleStorage source switch
cases. Both bodies are straight-line, so the lowering is deterministic and
the threaded `nextSwitchId` returns unchanged. Strengthens `_lowered_shape`
from a two-element shape with unspecified bodies to a fixed shape with
explicit lowered bodies, anchoring downstream hit-case proofs against the
harness primitive-call lemmas. -/
theorem simpleStorageBuildSwitchSourceCases_lowered_concrete
    (reservedNames : List String) (nextSwitchId : Nat) :
    Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId
        simpleStorageBuildSwitchSourceCases =
      .ok ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
            (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)],
        nextSwitchId) := by
  simp only [simpleStorageLoweredStoreCaseBody,
    simpleStorageLoweredRetrieveCaseBody,
    simpleStorageBuildSwitchSourceCases, simpleStorageIRContract,
    Compiler.CodegenCommon.dispatchBody,
    Compiler.CodegenCommon.callvalueGuard,
    Compiler.CodegenCommon.calldatasizeGuard,
    List.map_cons, List.map_nil, List.append_nil,
    List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    if_false, Bool.false_eq_true,
    Backends.lowerSwitchCasesNativeWithSwitchIds_cons,
    Backends.lowerSwitchCasesNativeWithSwitchIds_nil,
    Backends.lowerStmtsNativeWithSwitchIds_cons,
    Backends.lowerStmtsNativeWithSwitchIds_nil,
    Backends.lowerStmtGroupNativeWithSwitchIds_comment,
    Backends.lowerStmtGroupNativeWithSwitchIds_let,
    Backends.lowerStmtGroupNativeWithSwitchIds_expr,
    Backends.lowerStmtGroupNativeWithSwitchIds_if,
    Bind.bind, Except.bind, pure, Except.pure]

/-- Closed-form selector-miss bridge endpoint for SimpleStorage native
dispatcher. Takes only source-level selector facts (`selector ≠ 0x6057361d`
and `selector ≠ 0x2e64cec1`, the two SimpleStorage IR selectors) and
produces the dispatcher exec result `.error Revert` at fuel `fuel + 21`
(`= fuel + cases'.length + 19` with `cases'.length = 2`). The proof opens the
`_sourceLowered` existential, derives `cases'.find? = none` and `tags-range`
from the source-cases facts via `_find?_none` / `_tags_eq` chained with
`simpleStorageBuildSwitchSourceCases_find?_none` and `_tags_lt_uint256_size`,
then composes through `_selectorMiss_revert_via_reduction`. This lifts the
remaining selector-miss obligation in the SimpleStorage native dispatcher
bridge to a purely source-level statement. -/
theorem simpleStorageNativeContract_dispatcherExec_selectorMiss_revert
    (fuel selector : Nat)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hSelMissStore : selector ≠ 0x6057361d)
    (hSelMissRetrieve : selector ≠ 0x2e64cec1)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 21)
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert := by
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (fuel + 7) tx storage observableSlots hNoWrap
  have hLen : cases'.length = 2 := by
    have h := Backends.lowerSwitchCasesNativeWithSwitchIds_length_eq
      _ _ _ _ _ hLowerCases
    rw [h]; rfl
  have hFind : cases'.find? (fun entry => entry.1 == selector) = none :=
    Backends.lowerSwitchCasesNativeWithSwitchIds_find?_none
      _ _ _ _ _ _ hLowerCases
      (simpleStorageBuildSwitchSourceCases_find?_none hSelMissStore hSelMissRetrieve)
  have hTags := Backends.lowerSwitchCasesNativeWithSwitchIds_tags_eq
    _ _ _ _ _ hLowerCases
  have hTagsRange : ∀ tag body, (tag, body) ∈ cases' →
      tag < EvmYul.UInt256.size := by
    intro tag body hMem
    have hMemTag : tag ∈ cases'.map (·.1) := List.mem_map_of_mem hMem
    rw [hTags, simpleStorageBuildSwitchSourceCases_map_fst] at hMemTag
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMemTag
    rcases hMemTag with rfl | rfl <;> decide
  have hReduction := hExec
  rw [show (fuel + 7 + 14 : Nat) = fuel + cases'.length + 19 by rw [hLen],
      show (fuel + 7 + 8 : Nat) = fuel + cases'.length + 13 by rw [hLen]]
    at hReduction
  have h := simpleStorageNativeContract_dispatcherExec_selectorMiss_revert_via_reduction
    fuel selector (Backends.freshNativeSwitchId reservedNames n0) cases'
    tx storage observableSlots hSelector hSelectorRange hFind hTagsRange
    hReduction
  rw [show fuel + cases'.length + 19 = fuel + 21 by rw [hLen]] at h
  exact h

/-- Post-`__has_selector := 1` switch-prefix state at a hit, with the matched
flag set: the input state shape consumed by the selected body inside the
lowered native switch's hit branch. -/
def simpleStorageDispatcherHitBodyInputState
    (switchId : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) : EvmYul.Yul.State :=
  ((((.Ok (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots).sharedState
            ((∅ : EvmYul.Yul.VarStore).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1)) : EvmYul.Yul.State).insert
          (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1))

/-- Hit-case dual of `_selectorMiss_revert_via_reduction` for the
SimpleStorage `store(uint256)` selector: composes the harness-level
`exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error`
with the strengthened-reduction equation, parametric in `cases'`, the lowered
bodies, and the body-execution `err`. -/
theorem simpleStorageNativeContract_dispatcherExec_storeHit_error_via_reduction
    (fuel switchId : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector :
      0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hCases : cases' = [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')])
    (hBody : ∀ pre suffix, cases' = pre ++ (0x6057361d, storeBody') :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block storeBody')
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) = .error err)
    (hReduction :
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (fuel + cases'.length + 19)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block [Backends.lowerNativeSwitchBlock
            (Yul.YulExpr.call "shr" [Yul.YulExpr.lit Compiler.Constants.selectorShift,
              Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
            switchId cases' [Backends.Native.nativeRevertZeroZeroStmt]])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1))) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + cases'.length + 19)
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) = .error err := by
  rw [hReduction]
  refine Backends.Native.exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error
    fuel 0x6057361d switchId 0x6057361d cases'
    [Backends.Native.nativeRevertZeroZeroStmt] storeBody'
    Compiler.SimpleStorageNativeWitness.nativeContract
    tx storage observableSlots err hSelector ?_ ?_ ?_ ?_
  · rw [hCases]; rfl
  · norm_num [EvmYul.UInt256.size]
  · intro tag body hMem; rw [hCases] at hMem
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hMem
    rcases hMem with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  · simpa [simpleStorageDispatcherHitBodyInputState] using hBody

def simpleStorageLoweredHitCasesShape
    (reservedNames : List String) (n0 midN : Nat)
    (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt) : Prop :=
  Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1)
      simpleStorageBuildSwitchSourceCases =
    .ok ([(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')], midN)

theorem simpleStorageNativeContract_dispatcherExec_storeHit_error
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : ∀ (reservedNames : List String) (n0 midN : Nat)
              (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt),
        simpleStorageLoweredHitCasesShape reservedNames n0 midN storeBody' retrieveBody' →
        EvmYul.Yul.exec (fuel + 9) (.Block storeBody')
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0) tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 21) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage observableSlots) =
      .error err := by
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (fuel + 7) tx storage observableSlots hNoWrap
  obtain ⟨storeBody', retrieveBody', hCases⟩ :=
    simpleStorageBuildSwitchSourceCases_lowered_shape reservedNames _ midN cases' hLowerCases
  subst hCases
  have hBody' := hBody reservedNames n0 midN storeBody' retrieveBody' hLowerCases
  have hReduction := hExec
  rw [show (fuel + 7 + 14 : Nat) = fuel + 2 + 19 from by omega,
      show (fuel + 7 + 8 : Nat) = fuel + 2 + 13 from by omega,
      show (2 : Nat) = ([(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length from rfl] at hReduction
  have h := simpleStorageNativeContract_dispatcherExec_storeHit_error_via_reduction
    fuel (Backends.freshNativeSwitchId reservedNames n0)
    [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')]
    storeBody' retrieveBody' tx storage observableSlots err
    hSelector rfl ?_ hReduction
  · rw [show fuel + ([(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length + 19 = fuel + 21 from rfl] at h
    exact h
  · rintro (_ | ⟨⟨_, _⟩, rest⟩) suffix hDecomp
    · simp only [List.nil_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hSuf⟩ := hDecomp; subst hSuf; simpa using hBody'
    · exfalso
      simp only [List.cons_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hRest⟩ := hDecomp
      cases rest with
      | nil => simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hRest
               exact absurd hRest.1.1 (by decide)
      | cons _ _ => simp at hRest

theorem simpleStorageLoweredHitCasesShape_concrete
    {reservedNames : List String} {n0 midN : Nat}
    {storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt}
    (hShape : simpleStorageLoweredHitCasesShape reservedNames n0 midN
      storeBody' retrieveBody') :
    storeBody' = simpleStorageLoweredStoreCaseBody ∧
      retrieveBody' = simpleStorageLoweredRetrieveCaseBody := by
  have hC := simpleStorageBuildSwitchSourceCases_lowered_concrete
    reservedNames (Backends.freshNativeSwitchId reservedNames n0 + 1)
  unfold simpleStorageLoweredHitCasesShape at hShape
  rw [hC] at hShape
  simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq] at hShape
  exact ⟨hShape.1.1.2.symm, hShape.1.2.1.2.symm⟩

/-- Concrete-body variant of `_dispatcherExec_storeHit_error`. The caller now
only has to discharge the body-exec obligation on the *fixed* lowered body
`simpleStorageLoweredStoreCaseBody`, instead of universally over any
`storeBody'` that might come out of the lowering. Uses
`simpleStorageLoweredHitCasesShape_concrete` to specialize the underlying
parametric premise. This strictly weakens the hit-case obligation that the
dispatcher bridge proof has to supply. -/
theorem simpleStorageNativeContract_dispatcherExec_storeHit_error_concrete
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 9) (.Block simpleStorageLoweredStoreCaseBody)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 21) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_storeHit_error
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0 _ storeBody' _ hShape
  obtain ⟨hStore, _⟩ := simpleStorageLoweredHitCasesShape_concrete hShape
  rw [hStore]
  exact hBody reservedNames n0

theorem simpleStorageNativeContract_dispatcherExec_storeHit_error_concrete_tail
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hTail : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 8) (.Block simpleStorageLoweredStoreCaseBodyTail)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 21) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_storeHit_error_concrete
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0
  exact exec_block_simpleStorageLoweredStoreCaseBody_head_strip_error
    (fuel + 7) _ _ err (hTail reservedNames n0)

/-- Callvalue-stripped version of `_storeHit_error_concrete_tail`: when the
transaction has zero `msgValue`, the leading `if callvalue() { revert }` guard
is a no-op, so the body-execution premise can be expressed against the
4-statement `simpleStorageLoweredStoreCaseBodyTail2` at fuel `+7` instead of
the 5-statement `simpleStorageLoweredStoreCaseBodyTail` at fuel `+8`. Strictly
shrinks the dispatcher hit-case body-exec obligation under the natural Solidity
assumption that non-payable functions are called with `msg.value = 0`. -/
theorem simpleStorageNativeContract_dispatcherExec_storeHit_error_concrete_tail2
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue = 0)
    (hTail2 : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 7)
          (.Block simpleStorageLoweredStoreCaseBodyTail2)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 21) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_storeHit_error_concrete_tail
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0
  have hWei :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.weiValue =
      (⟨0⟩ : EvmYul.Literal) := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_weiValue,
        hMsgValue]
    rfl
  have hT2 := hTail2 reservedNames n0
  show EvmYul.Yul.exec (fuel + 8) (.Block simpleStorageLoweredStoreCaseBodyTail)
    (some Compiler.SimpleStorageNativeWitness.nativeContract)
    (.Ok _ _) = .error err
  exact exec_block_simpleStorageLoweredStoreCaseBodyTail_callvalue_strip_error
    fuel _ _ _ err hWei hT2

theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error_via_reduction
    (fuel switchId : Nat)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector :
      0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hCases : cases' = [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')])
    (hBody : ∀ pre suffix, cases' = pre ++ (0x2e64cec1, retrieveBody') :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block retrieveBody')
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) = .error err)
    (hReduction :
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          (fuel + cases'.length + 19)
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots) =
        EvmYul.Yul.exec (fuel + cases'.length + 13)
          (.Block [Backends.lowerNativeSwitchBlock
            (Yul.YulExpr.call "shr" [Yul.YulExpr.lit Compiler.Constants.selectorShift,
              Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 0]])
            switchId cases' [Backends.Native.nativeRevertZeroZeroStmt]])
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          ((Compiler.Proofs.YulGeneration.Backends.Native.nativeSwitchInitialOkState
            Compiler.SimpleStorageNativeWitness.nativeContract
            tx storage observableSlots).insert "__has_selector"
              (EvmYul.UInt256.ofNat 1))) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + cases'.length + 19)
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract
          tx storage observableSlots) = .error err := by
  rw [hReduction]
  refine Backends.Native.exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error
    fuel 0x2e64cec1 switchId 0x2e64cec1 cases'
    [Backends.Native.nativeRevertZeroZeroStmt] retrieveBody'
    Compiler.SimpleStorageNativeWitness.nativeContract
    tx storage observableSlots err hSelector ?_ ?_ ?_ ?_
  · rw [hCases]; rfl
  · norm_num [EvmYul.UInt256.size]
  · intro tag body hMem; rw [hCases] at hMem
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hMem
    rcases hMem with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  · simpa [simpleStorageDispatcherHitBodyInputState] using hBody

theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : ∀ (reservedNames : List String) (n0 midN : Nat)
              (storeBody' retrieveBody' : List EvmYul.Yul.Ast.Stmt),
        simpleStorageLoweredHitCasesShape reservedNames n0 midN storeBody' retrieveBody' →
        EvmYul.Yul.exec (fuel + 8) (.Block retrieveBody')
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0) tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 21) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage observableSlots) =
      .error err := by
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (fuel + 7) tx storage observableSlots hNoWrap
  obtain ⟨storeBody', retrieveBody', hCases⟩ :=
    simpleStorageBuildSwitchSourceCases_lowered_shape reservedNames _ midN cases' hLowerCases
  subst hCases
  have hBody' := hBody reservedNames n0 midN storeBody' retrieveBody' hLowerCases
  have hReduction := hExec
  rw [show (fuel + 7 + 14 : Nat) = fuel + 2 + 19 from by omega,
      show (fuel + 7 + 8 : Nat) = fuel + 2 + 13 from by omega,
      show (2 : Nat) = ([(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length from rfl] at hReduction
  have h := simpleStorageNativeContract_dispatcherExec_retrieveHit_error_via_reduction
    fuel (Backends.freshNativeSwitchId reservedNames n0)
    [(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')]
    storeBody' retrieveBody' tx storage observableSlots err
    hSelector rfl ?_ hReduction
  · rw [show fuel + ([(0x6057361d, storeBody'), (0x2e64cec1, retrieveBody')] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length + 19 = fuel + 21 from rfl] at h
    exact h
  · rintro (_ | ⟨⟨_, _⟩, rest⟩) suffix hDecomp
    · exfalso
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hDecomp
      exact absurd hDecomp.1.1 (by decide)
    · simp only [List.cons_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hRest⟩ := hDecomp
      cases rest with
      | nil => simp only [List.nil_append, List.cons.injEq] at hRest
               obtain ⟨_, hSuf⟩ := hRest; subst hSuf; simpa using hBody'
      | cons _ _ => simp at hRest

theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hBody : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 8) (.Block simpleStorageLoweredRetrieveCaseBody)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 21) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_retrieveHit_error
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0 _ _ retrieveBody' hShape
  obtain ⟨_, hRetrieve⟩ := simpleStorageLoweredHitCasesShape_concrete hShape
  rw [hRetrieve]
  exact hBody reservedNames n0

theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete_tail
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hTail : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 7) (.Block simpleStorageLoweredRetrieveCaseBodyTail)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 21) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0
  exact exec_block_simpleStorageLoweredRetrieveCaseBody_head_strip_error
    (fuel + 6) _ _ err (hTail reservedNames n0)

/-- Retrieve-case dual of `_storeHit_error_concrete_tail2`. -/
theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete_tail2
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0)
    (hTail2 : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 6)
          (.Block simpleStorageLoweredRetrieveCaseBodyTail2)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 21) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete_tail
    fuel tx storage observableSlots err hSelector hNoWrap ?_
  intro reservedNames n0
  have hWei :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.weiValue =
      (⟨0⟩ : EvmYul.Literal) := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_weiValue]
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    simpa [Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256,
      EvmYul.UInt256.ofNat, Fin.ofNat] using hMsgValue
  have hT2 := hTail2 reservedNames n0
  show EvmYul.Yul.exec (fuel + 7) (.Block simpleStorageLoweredRetrieveCaseBodyTail)
    (some Compiler.SimpleStorageNativeWitness.nativeContract)
    (.Ok _ _) = .error err
  exact exec_block_simpleStorageLoweredRetrieveCaseBodyTail_callvalue_strip_error
    fuel _ _ _ err hWei hT2

/-- Retrieve-case wrapper that further shrinks the body-exec obligation by
also stripping the inner `if lt(calldatasize(), 4) {…}` argument-length revert
guard. The user supplies the tail3 obligation (the 2-statement
`mstore(0, sload(0)); return(0, 32)` core) and the wrapper discharges both
the callvalue and lt-calldatasize guards via the strip lemmas. The
calldata-size assumptions are derived automatically from `hNoWrap` and
`initialState_calldataSize`. -/
theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete_tail3
    (fuel : Nat) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (err : EvmYul.Yul.Exception)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0)
    (hTail3 : ∀ (reservedNames : List String) (n0 : Nat),
        EvmYul.Yul.exec (fuel + 9)
          (.Block simpleStorageLoweredRetrieveCaseBodyTail3)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState
            (Backends.freshNativeSwitchId reservedNames n0)
            tx storage observableSlots) =
          .error err) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        (fuel + 25) Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error err := by
  refine simpleStorageNativeContract_dispatcherExec_retrieveHit_error_concrete_tail2
    (fuel + 4) tx storage observableSlots err hSelector hNoWrap hMsgValue ?_
  intro reservedNames n0
  have hT3 := hTail3 reservedNames n0
  have hSize :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.calldata.size <
      EvmYul.UInt256.size := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataSize]
    exact hNoWrap
  have hGe :
      4 ≤ (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.calldata.size := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataSize]
    exact Nat.le_add_right 4 _
  show EvmYul.Yul.exec ((fuel + 4) + 6)
    (.Block simpleStorageLoweredRetrieveCaseBodyTail2)
    (some Compiler.SimpleStorageNativeWitness.nativeContract)
    (.Ok _ _) = .error err
  exact exec_block_simpleStorageLoweredRetrieveCaseBodyTail2_lt_strip_error
    fuel _ _ _ err hSize hGe hT3

noncomputable def simpleStorageNativeDispatcherFuel : Nat :=
  sizeOf [Compiler.CodegenCommon.buildSwitch
    simpleStorageIRContract.functions none none]

/-- Lower bound on the SimpleStorage native dispatcher fuel constant for
the retrieve-hit and store-hit bridges, which use the `_concrete_tail3`
chain that produces dispatcher exec at `fuel + 25`. -/
theorem simpleStorageNativeDispatcherFuel_ge_25 :
    simpleStorageNativeDispatcherFuel ≥ 25 := by
  unfold simpleStorageNativeDispatcherFuel
  decide

theorem simpleStorageNativeDispatcherFuel_ge_21 :
    simpleStorageNativeDispatcherFuel ≥ 21 := by
  exact Nat.le_trans (by decide) simpleStorageNativeDispatcherFuel_ge_25

/-- Native dispatcher exec at exactly `simpleStorageNativeDispatcherFuel`
reduces to `.error Revert` for the selector-miss class. -/
theorem simpleStorageNativeContract_dispatcherExec_selectorMiss_revert_atFuel
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelectorRange : tx.functionSelector % Compiler.Constants.selectorModulus
        < EvmYul.UInt256.size)
    (hSelMissStore : tx.functionSelector % Compiler.Constants.selectorModulus
        ≠ 0x6057361d)
    (hSelMissRetrieve : tx.functionSelector % Compiler.Constants.selectorModulus
        ≠ 0x2e64cec1)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        simpleStorageNativeDispatcherFuel
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error EvmYul.Yul.Exception.Revert := by
  have hReshape : simpleStorageNativeDispatcherFuel =
      (simpleStorageNativeDispatcherFuel - 21) + 21 :=
    (Nat.sub_add_cancel simpleStorageNativeDispatcherFuel_ge_21).symm
  rw [hReshape]
  exact simpleStorageNativeContract_dispatcherExec_selectorMiss_revert
    (simpleStorageNativeDispatcherFuel - 21)
    (tx.functionSelector % Compiler.Constants.selectorModulus)
    tx storage observableSlots
    rfl hSelectorRange hSelMissStore hSelMissRetrieve hNoWrap

/-- Closed-form `interpretIR` reduction for the SimpleStorage selector-miss
class. Given the two raw selector mismatches (`≠ 0x6057361d` and
`≠ 0x2e64cec1`), `interpretIR` falls into the `find?`-`none` branch and returns
the trivial reverted shape with storage and events untouched. -/
theorem interpretIR_simpleStorage_selectorMiss
    (tx : IRTransaction) (initialState : IRState)
    (hSelMissStore : tx.functionSelector ≠ 0x6057361d)
    (hSelMissRetrieve : tx.functionSelector ≠ 0x2e64cec1) :
    interpretIR simpleStorageIRContract tx initialState =
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events } := by
  unfold interpretIR
  simp only [simpleStorageIRContract, List.find?]
  have hstore : (0x6057361d == tx.functionSelector) = false := by
    simp [BEq.beq, hSelMissStore.symm]
  have hretrieve : (0x2e64cec1 == tx.functionSelector) = false := by
    simp [BEq.beq, hSelMissRetrieve.symm]
  simp [hstore, hretrieve]

/-- Closed-form `interpretIR` reduction for the SimpleStorage retrieve-hit
class. Given the raw selector match (`= 0x2e64cec1`), `interpretIR` enters the
`retrieve` body which is read-only on storage: it loads slot 0 via `sload`,
mirrors it into memory[0..32] via `mstore`, and returns those 32 bytes. The
returned word equals `(state.storage (IRStorageSlot.ofNat 0)).toNat` (where `state` is
`initialState.withTx tx`). Storage and events are unchanged.

  After Phase 1 of the IR storage refactor,
  `state.storage (IRStorageSlot.ofNat 0) : IRStorageWord` is `UInt256`-bounded,
  so `(state.storage (IRStorageSlot.ofNat 0)).toNat < 2^256`. This is the
IR-side input to the direct native retrieve-hit match proof. -/
theorem interpretIR_simpleStorage_retrieveHit
    (tx : IRTransaction) (initialState : IRState)
    (hSel : tx.functionSelector = 0x2e64cec1) :
      interpretIR simpleStorageIRContract tx initialState =
        { success := true
          returnValue := some ((initialState.storage (IRStorageSlot.ofNat 0)).toNat)
          finalStorage := initialState.storage
          finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
          events := initialState.events } := by
  have hstore : (0x6057361d == tx.functionSelector) = false := by
    simp [BEq.beq, hSel]
  have hretrieve : (0x2e64cec1 == tx.functionSelector) = true := by
    simp [BEq.beq, hSel]
  -- Closed-form evaluation of the retrieve body for any fuel ≥ 2.
  have hbody : ∀ (n : Nat) (s : IRState), 2 ≤ n →
      execIRStmts (n + 1) s
        [Yul.YulStmt.expr (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
         Yul.YulStmt.expr (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] =
          .return ((s.storage (IRStorageSlot.ofNat 0)).toNat)
            { s with memory := fun o =>
                if o = 0 then (s.storage (IRStorageSlot.ofNat 0)).toNat else s.memory o } := by
    intro n s hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    -- Fuel `k + 2 + 1 = k + 3` is `Nat.succ (Nat.succ (Nat.succ k))`, allowing
    -- both the outer `execIRStmts` and the inner `execIRStmt` to step.
    simp +decide only [execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
      Compiler.Proofs.YulGeneration.legacyEvalBuiltinCallWithContext,
      Compiler.Proofs.abstractLoadStorageOrMapping,
      Option.bind_some, bind, pure, ↓reduceIte]
  -- The retrieve body has at least 2 statements, so `sizeOf body ≥ 2` by
  -- direct computation on the auto-derived size measure.
  have hsize : 2 ≤ sizeOf
      ([Yul.YulStmt.expr (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
        Yul.YulStmt.expr (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])] : List Yul.YulStmt) := by
    decide
  unfold interpretIR
  simp only [simpleStorageIRContract, List.find?, hstore, hretrieve,
    List.length_nil, Nat.zero_le, ↓reduceDIte]
  -- Now goal involves `execIRFunction retrieveFn tx.args state'`.
  unfold execIRFunction
  simp only [List.zip_nil_left, List.foldl_nil]
  -- Goal: `match execIRStmts (sizeOf body + 1) state' body with ... = ...`.
  rw [hbody _ _ hsize]

/-- Closed-form `interpretIR` reduction for the SimpleStorage store-hit class
when the ABI argument is present. The IR setter writes the first calldata word
to bounded storage slot zero and stops successfully. -/
theorem interpretIR_simpleStorage_storeHit_arg
    (tx : IRTransaction) (initialState : IRState)
    (arg : Nat) (rest : List Nat)
    (hSel : tx.functionSelector = 0x6057361d)
    (hArgs : tx.args = arg :: rest) :
      interpretIR simpleStorageIRContract tx initialState =
        { success := true
          returnValue := none
          finalStorage :=
            Compiler.Proofs.abstractStoreStorageOrMapping initialState.storage 0
              (arg % evmModulus)
          finalMappings :=
            Compiler.Proofs.storageAsMappings
              (Compiler.Proofs.abstractStoreStorageOrMapping initialState.storage 0
                (arg % evmModulus))
          events := initialState.events } := by
  have hstore : (0x6057361d == tx.functionSelector) = true := by
    simp [BEq.beq, hSel]
  have hbody : ∀ (n : Nat) (s : IRState), 3 ≤ n →
      execIRStmts (n + 1) s
        [Yul.YulStmt.let_ "value" (Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]),
         Yul.YulStmt.expr (Yul.YulExpr.call "sstore"
            [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
         Yul.YulStmt.expr (Yul.YulExpr.call "stop" [])] =
          .stop
            { s.setVar "value" (Compiler.Proofs.YulGeneration.calldataloadWord
                s.selector s.calldata 4) with
              storage := Compiler.Proofs.abstractStoreStorageOrMapping
                s.storage 0 (Compiler.Proofs.YulGeneration.calldataloadWord
                  s.selector s.calldata 4) } := by
    intro n s hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    simp +decide [execIRStmts, execIRStmt, evalIRExpr, IRState.getVar,
      IRState.setVar]
  have hsize : 3 ≤ sizeOf
      ([Yul.YulStmt.let_ "value" (Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]),
        Yul.YulStmt.expr (Yul.YulExpr.call "sstore"
          [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
        Yul.YulStmt.expr (Yul.YulExpr.call "stop" [])] : List Yul.YulStmt) := by
    decide
  unfold interpretIR
  simp only [simpleStorageIRContract, List.find?, hstore, List.length_cons,
    List.length_nil, Nat.reduceAdd]
  unfold execIRFunction
  simp only [hArgs, List.zip_cons_cons, List.zip_nil_left, List.foldl_cons,
    List.foldl_nil]
  rw [hbody _ _ hsize]
  simp [IRState.setVar, Compiler.Proofs.abstractStoreStorageOrMapping_eq,
    Compiler.Proofs.YulGeneration.calldataloadWord, evmModulus]

/-- Closed-form `interpretIR` reduction for the SimpleStorage store-hit class
when calldata is too short for the single setter argument. The dispatcher
selects the function, but the IR arity guard fails before executing the body. -/
theorem interpretIR_simpleStorage_storeHit_short
    (tx : IRTransaction) (initialState : IRState)
    (hSel : tx.functionSelector = 0x6057361d)
    (hShort : tx.args = []) :
      interpretIR simpleStorageIRContract tx initialState =
        { success := false
          returnValue := none
          finalStorage := initialState.storage
          finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
          events := initialState.events } := by
  have hstore : (0x6057361d == tx.functionSelector) = true := by
    simp [BEq.beq, hSel]
  unfold interpretIR
  simp [simpleStorageIRContract, hstore, hShort]

/-- Native dispatcher exec at exactly `simpleStorageNativeDispatcherFuel`
reduces to `.error (YulHalt (.Ok shared3 _) ⟨1⟩)` for the retrieve-hit class,
where `shared3` is the closed-form shared state after the
`mstore(0, sload(0))` and `return(0, 32)` updates. The Yul varStore inside
the halt state depends on the fresh switch identifier (which the dispatcher
chose internally), so it is left existentially quantified — `projectResult`
on `.error (YulHalt _ _)` ignores the varStore, so this is sufficient for
the bridge proof. Composes the body-level closed form
`exec_block_simpleStorageLoweredRetrieveCaseBody_halt` with
`_retrieveHit_error_via_reduction` after opening the `_sourceLowered`
existential and pinning `cases'` via `_lowered_shape` and
`_lowered_concrete`. The `_concrete_tail*` chain is bypassed because it
universally quantifies over `(reservedNames, n0)` against a single fixed
`err`, which is incompatible with the switchId-dependent varStore inside
the halt-error term. -/
theorem simpleStorageNativeContract_dispatcherExec_retrieveHit_halt_atFuel
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hSelector : 0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) :
    let shared := (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState
    let p := shared.sload (EvmYul.UInt256.ofNat 0)
    let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
    let shared3 : EvmYul.SharedState .Yul :=
      { shared2 with
        toMachineState :=
          shared2.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    ∃ store : EvmYul.Yul.VarStore,
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          simpleStorageNativeDispatcherFuel
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract tx storage
            observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store) ⟨1⟩) := by
  -- Bring the let-bound names from the goal into the local context.
  intro shared p shared1 shared2 shared3
  -- Reshape dispatcher fuel to `g + 25` where `g := dispatcherFuel - 25`.
  set g := simpleStorageNativeDispatcherFuel - 25 with hg_def
  have hReshape : simpleStorageNativeDispatcherFuel = g + 25 :=
    (Nat.sub_add_cancel simpleStorageNativeDispatcherFuel_ge_25).symm
  rw [hReshape]
  -- Open the `_sourceLowered` existential at `peeledFuel := g + 11`, so the
  -- dispatcher LHS lands at `(g + 11) + 14 = g + 25`.
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (g + 11) tx storage observableSlots hNoWrap
  -- Pin `cases'` to the two-element shape.
  obtain ⟨storeBody', retrieveBody', hCases⟩ :=
    simpleStorageBuildSwitchSourceCases_lowered_shape reservedNames _ midN
      cases' hLowerCases
  subst hCases
  -- Pin the lowered bodies to the concrete forms.
  obtain ⟨hStoreBody, hRetrieveBody⟩ :=
    simpleStorageLoweredHitCasesShape_concrete hLowerCases
  subst hStoreBody
  subst hRetrieveBody
  -- The chained-insert varStore for the dispatcher hit-body input state.
  set switchId := Backends.freshNativeSwitchId reservedNames n0 with hSw
  let store_body : EvmYul.Yul.VarStore :=
    ((((∅ : EvmYul.Yul.VarStore).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)).insert
          (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1)
  -- Provide `store := store_body` for the existential.
  refine ⟨store_body, ?_⟩
  -- Discharge the body-level closed form via `_RetrieveCaseBody_halt`.
  have hWei :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.weiValue =
      (⟨0⟩ : EvmYul.Literal) := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_weiValue]
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    simpa [Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256,
      EvmYul.UInt256.ofNat, Fin.ofNat] using hMsgValue
  have hSize :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.calldata.size <
      EvmYul.UInt256.size := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataSize]
    exact hNoWrap
  have hGe :
      4 ≤ (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.calldata.size := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataSize]
    exact Nat.le_add_right 4 _
  have hBodyHalt :=
    exec_block_simpleStorageLoweredRetrieveCaseBody_halt g
      (some Compiler.SimpleStorageNativeWitness.nativeContract)
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState
      store_body hWei hSize hGe
  -- Reshape `hExec` into the form expected by `_via_reduction`'s
  -- `hReduction` parameter.
  have hReduction := hExec
  rw [show (g + 11 + 14 : Nat) = (g + 4) + 2 + 19 from by omega,
      show (g + 11 + 8 : Nat) = (g + 4) + 2 + 13 from by omega,
      show (2 : Nat) = ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length from rfl] at hReduction
  -- Body-execution premise of `_via_reduction`: only valid decomposition is
  -- `pre = [(0x6057361d, store)]`, `suffix = []`. Body fuel is
  -- `(g + 4 + 1) + 0 + 7 = g + 12`, matching `hBodyHalt`.
  have hBodyExec : ∀ pre suffix,
      ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)) =
        pre ++ (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody) :: suffix →
      EvmYul.Yul.exec (((g + 4) + 1) + suffix.length + 7)
        (.Block simpleStorageLoweredRetrieveCaseBody)
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store_body) ⟨1⟩) := by
    rintro pre suffix hDecomp
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hDecomp
      exfalso
      exact absurd hDecomp.1.1 (by decide)
    | cons _ rest =>
      simp only [List.cons_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hRest⟩ := hDecomp
      cases rest with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hRest
        obtain ⟨_, hSuf⟩ := hRest
        subst hSuf
        simpa [simpleStorageDispatcherHitBodyInputState] using hBodyHalt
      | cons _ _ => simp at hRest
  -- Apply `_retrieveHit_error_via_reduction` at `fuel := g + 4` with
  -- `err := YulHalt (.Ok shared3 store_body) ⟨1⟩`.
  have h := simpleStorageNativeContract_dispatcherExec_retrieveHit_error_via_reduction
    (g + 4) switchId
    [(0x6057361d, simpleStorageLoweredStoreCaseBody),
     (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)]
    simpleStorageLoweredStoreCaseBody simpleStorageLoweredRetrieveCaseBody
    tx storage observableSlots
    (EvmYul.Yul.Exception.YulHalt (.Ok shared3 store_body) ⟨1⟩)
    hSelector rfl hBodyExec hReduction
  -- `h` has dispatcher fuel `(g + 4) + cases'.length + 19`. Reshape to `g + 25`.
  have hLen :
      ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length = 2 := rfl
  rw [hLen, show (g + 4) + 2 + 19 = g + 25 from by omega] at h
  exact h

/-- Native dispatcher exec at exactly `simpleStorageNativeDispatcherFuel`
reduces to the `STOP` halt for the store-hit class when calldata supplies the
setter argument. -/
theorem simpleStorageNativeContract_dispatcherExec_storeHit_halt_atFuel
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (arg : Nat) (rest : List Nat) (hArgs : tx.args = arg :: rest)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) :
    ∃ store_body haltState,
      Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
          simpleStorageNativeDispatcherFuel
          Compiler.SimpleStorageNativeWitness.nativeContract
          (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract tx storage
            observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt haltState ⟨0⟩) ∧
      haltState =
        let initialWithStore : EvmYul.Yul.State :=
          .Ok (Compiler.Proofs.YulGeneration.Backends.Native.initialState
            Compiler.SimpleStorageNativeWitness.nativeContract tx storage
            observableSlots).sharedState store_body
        let withValue := initialWithStore.insert "value"
          (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
        withValue.setState
          (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
            (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)) := by
  set g := simpleStorageNativeDispatcherFuel - 25 with hg_def
  have hReshape : simpleStorageNativeDispatcherFuel = g + 25 :=
    (Nat.sub_add_cancel simpleStorageNativeDispatcherFuel_ge_25).symm
  rw [hReshape]
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (g + 11) tx storage observableSlots hNoWrap
  obtain ⟨storeBody', retrieveBody', hCases⟩ :=
    simpleStorageBuildSwitchSourceCases_lowered_shape reservedNames _ midN
      cases' hLowerCases
  subst hCases
  obtain ⟨hStoreBody, hRetrieveBody⟩ :=
    simpleStorageLoweredHitCasesShape_concrete hLowerCases
  subst hStoreBody
  subst hRetrieveBody
  set switchId := Backends.freshNativeSwitchId reservedNames n0 with hSw
  let store_body : EvmYul.Yul.VarStore :=
    ((((∅ : EvmYul.Yul.VarStore).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)).insert
          (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1)
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (Compiler.Proofs.YulGeneration.Backends.Native.initialState
      Compiler.SimpleStorageNativeWitness.nativeContract tx storage
      observableSlots).sharedState store_body
  let withValue := initialWithStore.insert "value"
    (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
  let finalState := withValue.setState
    (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
  refine ⟨store_body, finalState, ?_, ?_⟩
  · have hWei :
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots).sharedState.executionEnv.weiValue =
        (⟨0⟩ : EvmYul.Literal) := by
      rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_weiValue]
      apply congrArg EvmYul.UInt256.mk
      apply Fin.ext
      simpa [Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256,
        EvmYul.UInt256.ofNat, Fin.ofNat] using hMsgValue
    have hSize :
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots).sharedState.executionEnv.calldata.size <
        EvmYul.UInt256.size := by
      rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataSize]
      exact hNoWrap
    have hGe :
        36 ≤ (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots).sharedState.executionEnv.calldata.size := by
      rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataSize]
      rw [hArgs]
      simp
      omega
    have hBodyHalt :=
      exec_block_simpleStorageLoweredStoreCaseBody_halt g
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        tx storage observableSlots store_body arg rest hArgs hWei hSize hGe
    have hReduction := hExec
    rw [show (g + 11 + 14 : Nat) = (g + 4) + 2 + 19 from by omega,
        show (g + 11 + 8 : Nat) = (g + 4) + 2 + 13 from by omega,
        show (2 : Nat) = ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
          (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
          List (Nat × List EvmYul.Yul.Ast.Stmt)).length from rfl] at hReduction
    have hBodyExec : ∀ pre suffix,
        ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
          (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
          List (Nat × List EvmYul.Yul.Ast.Stmt)) =
          pre ++ (0x6057361d, simpleStorageLoweredStoreCaseBody) :: suffix →
        EvmYul.Yul.exec (((g + 4) + 1) + suffix.length + 7)
          (.Block simpleStorageLoweredStoreCaseBody)
          (some Compiler.SimpleStorageNativeWitness.nativeContract)
          (simpleStorageDispatcherHitBodyInputState switchId tx storage
            observableSlots) =
          .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
      rintro pre suffix hDecomp
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hDecomp
        obtain ⟨_, hSuf⟩ := hDecomp
        subst hSuf
        simpa [simpleStorageDispatcherHitBodyInputState, initialWithStore,
          withValue, finalState] using hBodyHalt
      | cons _ restPre =>
        exfalso
        simp only [List.cons_append, List.cons.injEq] at hDecomp
        obtain ⟨_, hRest⟩ := hDecomp
        cases restPre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hRest
          exact absurd hRest.1.1 (by decide)
        | cons _ _ => simp at hRest
    have h := simpleStorageNativeContract_dispatcherExec_storeHit_error_via_reduction
      (g + 4) switchId
      [(0x6057361d, simpleStorageLoweredStoreCaseBody),
       (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)]
      simpleStorageLoweredStoreCaseBody simpleStorageLoweredRetrieveCaseBody
      tx storage observableSlots
      (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩)
      hSelector rfl hBodyExec hReduction
    have hLen :
        ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
          (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
          List (Nat × List EvmYul.Yul.Ast.Stmt)).length = 2 := rfl
    rw [hLen, show (g + 4) + 2 + 19 = g + 25 from by omega] at h
    exact h
  · rfl

/-- Native dispatcher exec at exactly `simpleStorageNativeDispatcherFuel`
reverts for the store-hit class when calldata contains no setter argument. -/
theorem simpleStorageNativeContract_dispatcherExec_storeHit_short_revert_atFuel
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (hArgs : tx.args = [])
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size)
    (hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0) :
    Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
        simpleStorageNativeDispatcherFuel
        Compiler.SimpleStorageNativeWitness.nativeContract
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          Compiler.SimpleStorageNativeWitness.nativeContract tx storage
          observableSlots) =
      .error EvmYul.Yul.Exception.Revert := by
  set g := simpleStorageNativeDispatcherFuel - 25 with hg_def
  have hReshape : simpleStorageNativeDispatcherFuel = g + 25 :=
    (Nat.sub_add_cancel simpleStorageNativeDispatcherFuel_ge_25).symm
  rw [hReshape]
  obtain ⟨reservedNames, n0, cases', midN, hExec, hLowerCases⟩ :=
    simpleStorageNativeContract_dispatcherExec_eq_lowerNativeSwitchBlock_revert_default_exec_sourceLowered
      (g + 11) tx storage observableSlots hNoWrap
  obtain ⟨storeBody', retrieveBody', hCases⟩ :=
    simpleStorageBuildSwitchSourceCases_lowered_shape reservedNames _ midN
      cases' hLowerCases
  subst hCases
  obtain ⟨hStoreBody, hRetrieveBody⟩ :=
    simpleStorageLoweredHitCasesShape_concrete hLowerCases
  subst hStoreBody
  subst hRetrieveBody
  set switchId := Backends.freshNativeSwitchId reservedNames n0 with hSw
  let store_body : EvmYul.Yul.VarStore :=
    ((((∅ : EvmYul.Yul.VarStore).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)).insert
          (Backends.nativeSwitchDiscrTempName switchId)
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 0)).insert
      (Backends.nativeSwitchMatchedTempName switchId)
      (EvmYul.UInt256.ofNat 1)
  have hWei :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.weiValue =
      (⟨0⟩ : EvmYul.Literal) := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_weiValue]
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    simpa [Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256,
      EvmYul.UInt256.ofNat, Fin.ofNat] using hMsgValue
  have hSizeEq :
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState.executionEnv.calldata.size = 4 := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.initialState_calldataSize]
    simp [hArgs]
  have hTail2 :=
    exec_block_simpleStorageLoweredStoreCaseBodyTail2_short_revert
      g (some Compiler.SimpleStorageNativeWitness.nativeContract)
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState
      store_body hSizeEq
  have hTail :=
    exec_block_simpleStorageLoweredStoreCaseBodyTail_callvalue_strip_error
      (g + 4) (some Compiler.SimpleStorageNativeWitness.nativeContract)
      (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        observableSlots).sharedState
      store_body _ hWei hTail2
  have hBodyRevert :
      EvmYul.Yul.exec (g + 13) (.Block simpleStorageLoweredStoreCaseBody)
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) =
        .error EvmYul.Yul.Exception.Revert := by
    exact exec_block_simpleStorageLoweredStoreCaseBody_head_strip_error
      (g + 11) _ _ _ hTail
  have hReduction := hExec
  rw [show (g + 11 + 14 : Nat) = (g + 4) + 2 + 19 from by omega,
      show (g + 11 + 8 : Nat) = (g + 4) + 2 + 13 from by omega,
      show (2 : Nat) = ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length from rfl] at hReduction
  have hBodyExec : ∀ pre suffix,
      ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)) =
        pre ++ (0x6057361d, simpleStorageLoweredStoreCaseBody) :: suffix →
      EvmYul.Yul.exec (((g + 4) + 1) + suffix.length + 7)
        (.Block simpleStorageLoweredStoreCaseBody)
        (some Compiler.SimpleStorageNativeWitness.nativeContract)
        (simpleStorageDispatcherHitBodyInputState switchId tx storage
          observableSlots) =
        .error EvmYul.Yul.Exception.Revert := by
    rintro pre suffix hDecomp
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hSuf⟩ := hDecomp
      subst hSuf
      simpa [simpleStorageDispatcherHitBodyInputState, store_body] using hBodyRevert
    | cons _ restPre =>
      exfalso
      simp only [List.cons_append, List.cons.injEq] at hDecomp
      obtain ⟨_, hRest⟩ := hDecomp
      cases restPre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hRest
        exact absurd hRest.1.1 (by decide)
      | cons _ _ => simp at hRest
  have h := simpleStorageNativeContract_dispatcherExec_storeHit_error_via_reduction
    (g + 4) switchId
    [(0x6057361d, simpleStorageLoweredStoreCaseBody),
     (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)]
    simpleStorageLoweredStoreCaseBody simpleStorageLoweredRetrieveCaseBody
    tx storage observableSlots EvmYul.Yul.Exception.Revert
    hSelector rfl hBodyExec hReduction
  have hLen :
      ([(0x6057361d, simpleStorageLoweredStoreCaseBody),
        (0x2e64cec1, simpleStorageLoweredRetrieveCaseBody)] :
        List (Nat × List EvmYul.Yul.Ast.Stmt)).length = 2 := rfl
  rw [hLen, show (g + 4) + 2 + 19 = g + 25 from by omega] at h
  exact h

/-- Projected native storage after the generated `store(uint256)` body agrees
with the IR setter update on every materialized slot. The native zero-write
case erases slot zero from the finite EVM map; projected lookup still agrees
with IR storage because missing native storage reads as the zero word. -/
theorem projectStorageFromState_storeHit_initialState_materialized
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat) (store : EvmYul.Yul.VarStore)
    (arg slot : Nat)
    (hSlot : slot ∈ slots) :
    let initialWithStore : EvmYul.Yul.State :=
      .Ok (Compiler.Proofs.YulGeneration.Backends.Native.initialState
        Compiler.SimpleStorageNativeWitness.nativeContract tx storage
        slots).sharedState store
    let withValue := initialWithStore.insert "value"
      (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg)
    let finalState := withValue.setState
      (withValue.toState.sstore (EvmYul.UInt256.ofNat 0)
        (Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256 arg))
    Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState tx
        finalState (IRStorageSlot.ofNat slot) =
      (Compiler.Proofs.abstractStoreStorageOrMapping storage 0 arg)
        (IRStorageSlot.ofNat slot) := by
  intro initialWithStore withValue finalState
  simp only [Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.extractStorage,
    finalState, withValue, initialWithStore,
    EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
    EvmYul.Yul.State.toState, EvmYul.Yul.State.insert,
    EvmYul.State.sstore, EvmYul.State.lookupAccount,
    EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
    EvmYul.Account.updateStorage,
    Compiler.Proofs.YulGeneration.Backends.Native.initialState,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
    YulState.initial,
    Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256]
  simp only [Option.option,
    Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  by_cases hValueZero :
      (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) = true
  · rw [hValueZero]
    simp only [ite_true, IRStorageSlot.toUInt256, IRStorageSlot.ofNat]
    have hArgZeroUInt :
        EvmYul.UInt256.ofNat arg = (⟨0⟩ : EvmYul.UInt256) := by
      cases hArg : EvmYul.UInt256.ofNat arg with
      | mk v =>
          rw [hArg] at hValueZero
          change (v == (0 : Fin EvmYul.UInt256.size)) = true at hValueZero
          have hv : v = (0 : Fin EvmYul.UInt256.size) :=
            of_decide_eq_true hValueZero
          subst hv
          rfl
    have hArgZero : IRStorageWord.ofNat arg = (0 : IRStorageWord) := by
      simpa [Compiler.Proofs.IRGeneration.IRStorageWord.ofNat] using hArgZeroUInt
    by_cases hKey :
        compare (EvmYul.UInt256.ofNat slot) (EvmYul.UInt256.ofNat 0) =
          Ordering.eq
    · have hSlotEq :
          IRStorageSlot.ofNat slot = IRStorageSlot.ofNat 0 := by
        have hUInt :
            EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 :=
          Compiler.Proofs.YulGeneration.Backends.StateBridge.UInt256_eq_of_compare_eq
            hKey
        simpa [IRStorageSlot.ofNat] using hUInt
      have hUInt :
          EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 := by
        simpa [IRStorageSlot.ofNat] using hSlotEq
      have hErase :
          (Batteries.RBMap.erase
            (Compiler.Proofs.YulGeneration.Backends.StateBridge.projectStorage
              storage slots)
            (EvmYul.UInt256.ofNat 0)).find? (EvmYul.UInt256.ofNat slot) =
            none := by
        simpa [hUInt] using
          (Batteries.RBMap.find?_erase_self
            (Compiler.Proofs.YulGeneration.Backends.StateBridge.projectStorage
              storage slots)
            (EvmYul.UInt256.ofNat 0))
      rw [hErase, hUInt]
      simp only [Compiler.Proofs.abstractStoreStorageOrMapping,
        Compiler.Proofs.IRGeneration.IRStorageWord.ofNat, IRStorageSlot.ofNat]
      simp only [if_true]
      rw [hArgZeroUInt]
      rfl
    · have hErase :
          (Batteries.RBMap.erase
            (Compiler.Proofs.YulGeneration.Backends.StateBridge.projectStorage
              storage slots)
            (EvmYul.UInt256.ofNat 0)).find? (EvmYul.UInt256.ofNat slot) =
          (Compiler.Proofs.YulGeneration.Backends.StateBridge.projectStorage
              storage slots).find? (EvmYul.UInt256.ofNat slot) := by
        exact Batteries.RBMap.find?_erase_of_ne _ hKey
      have hLookup :=
        Compiler.Proofs.YulGeneration.Backends.StateBridge.storageLookup_projectStorage_projected
          storage slots slot hSlot
      have hLookup' :
          (match
            (Compiler.Proofs.YulGeneration.Backends.StateBridge.projectStorage
              storage slots).find? (EvmYul.UInt256.ofNat slot) with
          | some val => val
          | none => (⟨0⟩ : EvmYul.UInt256)) =
            storage (IRStorageSlot.ofNat slot) := by
        simpa [Compiler.Proofs.YulGeneration.Backends.StateBridge.storageLookup,
          Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256]
          using hLookup
      rw [hErase]
      have hSlotNe :
          IRStorageSlot.ofNat slot ≠ IRStorageSlot.ofNat 0 := by
        intro hEq
        apply hKey
        have hUIntEq :
            EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 := by
          simpa [IRStorageSlot.ofNat] using hEq
        rw [hUIntEq]
        exact Std.ReflCmp.compare_self
      have hSlotNe' :
          EvmYul.UInt256.ofNat slot ≠ IRStorageSlot.ofNat 0 := by
        simpa [IRStorageSlot.ofNat] using hSlotNe
      have hSlotNeUInt :
          EvmYul.UInt256.ofNat slot ≠ EvmYul.UInt256.ofNat 0 := by
        intro hEq
        exact hSlotNe' (by simpa [IRStorageSlot.ofNat] using hEq)
      simpa [Compiler.Proofs.abstractStoreStorageOrMapping, IRStorageSlot.ofNat,
        hSlotNeUInt] using hLookup'
  · have hValueNonzero :
        (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) =
          false := by
      cases h :
          (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) <;>
        simp [h] at hValueZero ⊢
    rw [hValueNonzero]
    simp only [Bool.false_eq_true, ite_false, IRStorageSlot.toUInt256,
      IRStorageSlot.ofNat]
    by_cases hKey :
        compare (EvmYul.UInt256.ofNat slot) (EvmYul.UInt256.ofNat 0) =
          Ordering.eq
    · have hSlotEq :
          IRStorageSlot.ofNat slot = IRStorageSlot.ofNat 0 := by
        have hUInt :
            EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 :=
          Compiler.Proofs.YulGeneration.Backends.StateBridge.UInt256_eq_of_compare_eq
            hKey
        simpa [IRStorageSlot.ofNat] using hUInt
      have hUInt :
          EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 := by
        simpa [IRStorageSlot.ofNat] using hSlotEq
      rw [Batteries.RBMap.find?_insert_of_eq _ hKey]
      rw [hUInt]
      simp [Compiler.Proofs.abstractStoreStorageOrMapping,
        Compiler.Proofs.IRGeneration.IRStorageWord.ofNat, IRStorageSlot.ofNat]
    · rw [Batteries.RBMap.find?_insert_of_ne _ hKey]
      have hLookup :=
        Compiler.Proofs.YulGeneration.Backends.StateBridge.storageLookup_projectStorage_projected
          storage slots slot hSlot
      have hLookup' :
          (match
            (Compiler.Proofs.YulGeneration.Backends.StateBridge.projectStorage
              storage slots).find? (EvmYul.UInt256.ofNat slot) with
          | some val => val
          | none => (⟨0⟩ : EvmYul.UInt256)) =
            storage (IRStorageSlot.ofNat slot) := by
        simpa [Compiler.Proofs.YulGeneration.Backends.StateBridge.storageLookup,
          Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256]
          using hLookup
      have hSlotNe :
          IRStorageSlot.ofNat slot ≠ IRStorageSlot.ofNat 0 := by
        intro hEq
        apply hKey
        have hUIntEq :
            EvmYul.UInt256.ofNat slot = EvmYul.UInt256.ofNat 0 := by
          simpa [IRStorageSlot.ofNat] using hEq
        rw [hUIntEq]
        exact Std.ReflCmp.compare_self
      have hSlotNe' :
          EvmYul.UInt256.ofNat slot ≠ IRStorageSlot.ofNat 0 := by
        simpa [IRStorageSlot.ofNat] using hSlotNe
      have hSlotNeUInt :
          EvmYul.UInt256.ofNat slot ≠ EvmYul.UInt256.ofNat 0 := by
        intro hEq
        exact hSlotNe' (by simpa [IRStorageSlot.ofNat] using hEq)
      simpa [Compiler.Proofs.abstractStoreStorageOrMapping, IRStorageSlot.ofNat,
        hSlotNeUInt] using hLookup'

/-- Closed-form evaluation of `projectResult` on the retrieve-hit halt error
produced by the lowered SimpleStorage retrieve body. The halt state is built
by chaining `sload(0)` (toState override), `mstore(0, _)` (toMachineState
override), and `evmReturn(0, 32)` (toMachineState override) starting from a
shared state with empty memory. The native projected return value is the
`Nat`-normalized form of the loaded slot-zero word; storage and logs are
read off the halt's `sharedState` directly. -/
theorem projectResult_retrieveHit_eq
    (tx : YulTransaction) (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hMemory : shared.memory = ByteArray.empty) :
    let p := shared.sload (EvmYul.UInt256.ofNat 0)
    let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
    let shared3 : EvmYul.SharedState .Yul :=
      { shared2 with
        toMachineState :=
          shared2.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        tx initialStorage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt
          (EvmYul.Yul.State.Ok shared3 store) ⟨1⟩)) =
      { success := true,
        returnValue := some p.2.toNat,
        finalStorage :=
          Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
            tx (EvmYul.Yul.State.Ok shared3 store),
        finalMappings :=
          Compiler.Proofs.storageAsMappings
            (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
              tx (EvmYul.Yul.State.Ok shared3 store)),
        events :=
          initialEvents ++
            Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
              (EvmYul.Yul.State.Ok shared3 store) } := by
  intro p shared1 shared2 shared3
  -- shared1 inherits memory from shared because only `toState` was overridden.
  have hMemory1 : shared1.memory = ByteArray.empty := hMemory
  -- The harness helpers describe the result via `setMachineState` chains;
  -- those equal the structural overrides used in `shared3`.
  have hSize :
      (EvmYul.Yul.State.Ok shared3 store).sharedState.H_return.size = 32 := by
    have h := Compiler.Proofs.YulGeneration.Backends.Native.mstore0_then_return32_hReturn_size
      shared1 store p.2
    simpa [shared3, shared2, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.sharedState] using h
  have hH_return :
      (EvmYul.Yul.State.Ok shared3 store).sharedState.H_return = p.2.toByteArray := by
    have h :=
      Compiler.Proofs.YulGeneration.Backends.Native.mstore0_then_return32_emptyMemory_hReturn_eq_toByteArray
        shared1 store p.2 hMemory1
    simpa [shared3, shared2, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.sharedState] using h
  have hHaltNotZero : (⟨1⟩ : EvmYul.Yul.Ast.Literal) ≠ ⟨0⟩ := by
    intro h
    norm_num [EvmYul.UInt256.size] at h
  have hReturnValue :
      Compiler.Proofs.YulGeneration.Backends.Native.projectHaltReturn
          (EvmYul.Yul.State.Ok shared3 store) ⟨1⟩ = some p.2.toNat := by
    rw [Compiler.Proofs.YulGeneration.Backends.Native.projectHaltReturn_32ByteReturn
      (EvmYul.Yul.State.Ok shared3 store) ⟨1⟩ hHaltNotZero hSize]
    rw [hH_return,
      Compiler.Proofs.YulGeneration.Backends.Native.byteArrayWord_uint256_toByteArray]
  simp only [Compiler.Proofs.YulGeneration.Backends.Native.projectResult,
    hReturnValue]

/-- Named SimpleStorage native dispatcher direct-match obligation.

The lowered native dispatcher result is compared with `interpretIR` directly
instead of with the EVMYulLean fuel wrapper. -/
def simpleStorageNativeCallDispatcherMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    Compiler.SimpleStorageNativeWitness.nativeContract

/-! ### Per-case sub-bridges for the SimpleStorage native dispatcher. -/

/-- Direct-match per-case sub-bridge for the `retrieve()` selector hit. -/
def simpleStorageNativeRetrieveHitMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  tx.functionSelector % Compiler.Constants.selectorModulus = 0x2e64cec1 →
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    Compiler.SimpleStorageNativeWitness.nativeContract

/-- Direct-match per-case sub-bridge for the `store(uint256)` selector hit. -/
def simpleStorageNativeStoreHitMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  tx.functionSelector % Compiler.Constants.selectorModulus = 0x6057361d →
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    Compiler.SimpleStorageNativeWitness.nativeContract

/-- Direct-match per-case sub-bridge for the selector-miss revert arm. -/
def simpleStorageNativeSelectorMissMatchBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  tx.functionSelector % Compiler.Constants.selectorModulus ≠ 0x2e64cec1 →
  tx.functionSelector % Compiler.Constants.selectorModulus ≠ 0x6057361d →
  nativeDispatcherExecMatchesIRPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    Compiler.SimpleStorageNativeWitness.nativeContract

/-- Retrieve-hit direct-match native dispatcher bridge. -/
theorem simpleStorageNativeRetrieveHitMatchBridge_proved
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hdispatchGuardSafe : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      DispatchGuardsSafe fn tx) :
    simpleStorageNativeRetrieveHitMatchBridge tx initialState observableSlots := by
  intro hRetrieve
  have hSelectorEq : tx.functionSelector = 0x2e64cec1 := by
    have hmod := Nat.mod_eq_of_lt hselector
    rw [hmod] at hRetrieve
    exact hRetrieve
  have hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0 := by
    let retrieveFn : IRFunction :=
      { name := "retrieve"
        selector := 0x2e64cec1
        params := []
        ret := IRType.uint256
        body := [
          Yul.YulStmt.expr (Yul.YulExpr.call "mstore" [Yul.YulExpr.lit 0, Yul.YulExpr.call "sload" [Yul.YulExpr.lit 0]]),
          Yul.YulStmt.expr (Yul.YulExpr.call "return" [Yul.YulExpr.lit 0, Yul.YulExpr.lit 32])
        ] }
    have hmem : retrieveFn ∈ simpleStorageIRContract.functions := by
      simp [retrieveFn, simpleStorageIRContract]
    have hguards := hdispatchGuardSafe retrieveFn hmem
    have hzero : tx.msgValue % evmModulus = 0 := by
      rcases hguards with ⟨hValue, _⟩
      rcases hValue with hPayable | hZero
      · simp [retrieveFn] at hPayable
      · exact hZero
    simpa [evmModulus, EvmYul.UInt256.size] using hzero
  have hIR := interpretIR_simpleStorage_retrieveHit tx initialState hSelectorEq
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode simpleStorageIRContract) observableSlots
  let shared :=
    (Compiler.Proofs.YulGeneration.Backends.Native.initialState
      Compiler.SimpleStorageNativeWitness.nativeContract yulTx
      initialState.storage slots).sharedState
  let p := shared.sload (EvmYul.UInt256.ofNat 0)
  let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
  let shared2 : EvmYul.SharedState .Yul :=
    { shared1 with
      toMachineState :=
        shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
  let shared3 : EvmYul.SharedState .Yul :=
    { shared2 with
      toMachineState :=
        shared2.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
  obtain ⟨store, hExec⟩ :=
    simpleStorageNativeContract_dispatcherExec_retrieveHit_halt_atFuel
      yulTx initialState.storage slots
      (by
        simp [yulTx]
        exact hRetrieve.symm)
      (by simpa [yulTx, YulTransaction.ofIR, evmModulus] using hNoWrap)
      (by simpa [yulTx, YulTransaction.ofIR] using hMsgValue)
  have hSlotZero : 0 ∈ slots := by
    simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots]
  have hp :
      p.2 = initialState.storage (IRStorageSlot.ofNat 0) := by
    have hload :=
      Compiler.Proofs.YulGeneration.Backends.Native.initialState_sload_materializedSlot_value
        Compiler.SimpleStorageNativeWitness.nativeContract yulTx initialState.storage
        slots 0 hSlotZero
    simpa [p, shared, Compiler.Proofs.YulGeneration.Backends.StateBridge.natToUInt256]
      using hload
  have hProject :
      Compiler.Proofs.YulGeneration.Backends.Native.projectResult
        (YulTransaction.ofIR tx) initialState.storage initialState.events
        (.error (EvmYul.Yul.Exception.YulHalt
          (EvmYul.Yul.State.Ok shared3 store) ⟨1⟩)) =
      { success := true,
        returnValue := some p.2.toNat,
        finalStorage :=
          Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
            (YulTransaction.ofIR tx) (EvmYul.Yul.State.Ok shared3 store),
        finalMappings :=
          Compiler.Proofs.storageAsMappings
            (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
              (YulTransaction.ofIR tx) (EvmYul.Yul.State.Ok shared3 store)),
        events :=
          initialState.events ++
            Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
              (EvmYul.Yul.State.Ok shared3 store) } := by
    have hMemory : shared.memory = ByteArray.empty := by
      simp [shared, Compiler.Proofs.YulGeneration.Backends.Native.initialState,
        Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
        YulState.initial, EvmYul.Yul.State.sharedState]
    simpa [yulTx, shared, p, shared1, shared2, shared3] using
      projectResult_retrieveHit_eq yulTx initialState.storage initialState.events
        shared store hMemory
  have hLogs :
      Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
        (EvmYul.Yul.State.Ok shared3 store) = [] := by
    simp [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
      shared3, shared2, shared1, p, shared,
      Compiler.Proofs.YulGeneration.Backends.Native.initialState,
      Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
      YulState.initial, EvmYul.State.sload, EvmYul.State.addAccessedStorageKey,
      EvmYul.Substate.addAccessedStorageKey, EvmYul.Yul.State.sharedState]
    rfl
  apply nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match
    (haltState := EvmYul.Yul.State.Ok shared3 store) (haltValue := ⟨1⟩)
  · simpa [simpleStorage_runtimeCode_eq_single_dispatcher, yulTx, slots,
      shared, p, shared1, shared2, shared3] using hExec
  · exact hProject
  · rw [hIR]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [hp, Compiler.Proofs.IRGeneration.IRStorageWord.toNat]
    · intro slot hslot
      have hslot' : slot ∈ slots := by
        simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
          hslot]
      have hNative :=
        Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState_retrieveHit_initialState_materialized
          Compiler.SimpleStorageNativeWitness.nativeContract yulTx initialState.storage
          slots store slot hslot'
      exact hNative.symm
    · rw [hLogs, List.append_nil]

/-- Store-hit direct-match native dispatcher bridge.

The proof splits on the setter calldata argument. Short calldata projects the
native argument-guard revert directly to the IR arity failure; present calldata
uses the closed-form native store halt and compares projected storage on the
materialized observable slots. -/
theorem simpleStorageNativeStoreHitMatchBridge_proved
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hdispatchGuardSafe : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      DispatchGuardsSafe fn tx) :
    simpleStorageNativeStoreHitMatchBridge tx initialState observableSlots := by
  intro hStore
  have hSelectorEq : tx.functionSelector = 0x6057361d := by
    have hmod := Nat.mod_eq_of_lt hselector
    rw [hmod] at hStore
    exact hStore
  have hMsgValue : tx.msgValue % EvmYul.UInt256.size = 0 := by
    let storeFn : IRFunction :=
      { name := "store"
        selector := 0x6057361d
        params := [{ name := "value", ty := IRType.uint256 }]
        ret := IRType.unit
        body := [
          Yul.YulStmt.let_ "value" (Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit 4]),
          Yul.YulStmt.expr (Yul.YulExpr.call "sstore" [Yul.YulExpr.lit 0, Yul.YulExpr.ident "value"]),
          Yul.YulStmt.expr (Yul.YulExpr.call "stop" [])
        ] }
    have hmem : storeFn ∈ simpleStorageIRContract.functions := by
      simp [storeFn, simpleStorageIRContract]
    have hguards := hdispatchGuardSafe storeFn hmem
    have hzero : tx.msgValue % evmModulus = 0 := by
      rcases hguards with ⟨hValue, _⟩
      rcases hValue with hPayable | hZero
      · simp [storeFn] at hPayable
      · exact hZero
    simpa [evmModulus, EvmYul.UInt256.size] using hzero
  let yulTx := YulTransaction.ofIR tx
  let slots :=
    Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
      (Compiler.runtimeCode simpleStorageIRContract) observableSlots
  cases hArgs : tx.args with
  | nil =>
      have hIR := interpretIR_simpleStorage_storeHit_short tx initialState
        hSelectorEq hArgs
      refine nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
        (err := EvmYul.Yul.Exception.Revert)
        (nativeYul :=
          { success := false
            returnValue := none
            finalStorage := initialState.storage
            finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
            events := initialState.events })
        ?_ ?_ ?_
      · simpa [simpleStorage_runtimeCode_eq_single_dispatcher, yulTx, slots] using
          (simpleStorageNativeContract_dispatcherExec_storeHit_short_revert_atFuel
            yulTx initialState.storage slots
            (by simpa [yulTx, YulTransaction.ofIR] using hArgs)
            (by
              simp [yulTx]
              exact hStore.symm)
            (by simpa [yulTx, YulTransaction.ofIR, evmModulus] using hNoWrap)
            (by simpa [yulTx, YulTransaction.ofIR] using hMsgValue))
      · rfl
      · rw [hIR]
        exact ⟨rfl, rfl, (by intro slot _; rfl), rfl⟩
  | cons arg rest =>
      have hIR := interpretIR_simpleStorage_storeHit_arg tx initialState arg rest
        hSelectorEq hArgs
      obtain ⟨store, haltState, hExec, hHaltState⟩ :=
        simpleStorageNativeContract_dispatcherExec_storeHit_halt_atFuel
          yulTx initialState.storage slots arg rest
          (by simpa [yulTx, YulTransaction.ofIR] using hArgs)
          (by
            simp [yulTx]
            exact hStore.symm)
          (by simpa [yulTx, YulTransaction.ofIR, evmModulus] using hNoWrap)
          (by simpa [yulTx, YulTransaction.ofIR] using hMsgValue)
      have hProject :
          Compiler.Proofs.YulGeneration.Backends.Native.projectResult
            (YulTransaction.ofIR tx) initialState.storage initialState.events
            (.error (EvmYul.Yul.Exception.YulHalt haltState ⟨0⟩)) =
          { success := true,
            returnValue := none,
            finalStorage :=
              Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
                (YulTransaction.ofIR tx) haltState,
            finalMappings :=
              Compiler.Proofs.storageAsMappings
                (Compiler.Proofs.YulGeneration.Backends.Native.projectStorageFromState
                  (YulTransaction.ofIR tx) haltState),
            events :=
              initialState.events ++
                Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
                  haltState } := by
        simp
      have hLogs :
          Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState
            haltState = [] := by
        subst hHaltState
        simp only [Compiler.Proofs.YulGeneration.Backends.Native.projectLogsFromState,
          Compiler.Proofs.YulGeneration.Backends.Native.initialState,
          Compiler.Proofs.YulGeneration.Backends.StateBridge.toSharedState,
          YulState.initial, EvmYul.Yul.State.sharedState,
          EvmYul.Yul.State.setState, EvmYul.Yul.State.toState,
          EvmYul.Yul.State.insert, EvmYul.State.sstore,
          EvmYul.State.setAccount, EvmYul.State.lookupAccount,
          EvmYul.State.addAccessedStorageKey,
          EvmYul.Account.updateStorage,
          EvmYul.Substate.addAccessedStorageKey, Option.option]
        split <;> rfl
      apply nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match
        (haltState := haltState) (haltValue := ⟨0⟩)
      · simpa [simpleStorage_runtimeCode_eq_single_dispatcher, yulTx, slots] using hExec
      · exact hProject
      · rw [hIR]
        refine ⟨rfl, rfl, ?_, ?_⟩
        · intro slot hslot
          have hslot' : slot ∈ slots := by
            simp [slots, Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots,
              hslot]
          have hNative :=
            projectStorageFromState_storeHit_initialState_materialized
              yulTx initialState.storage slots store arg slot hslot'
          have hArgMod :
              EvmYul.UInt256.ofNat arg =
                EvmYul.UInt256.ofNat (arg % evmModulus) := by
            unfold EvmYul.UInt256.ofNat
            simp [Id.run, Fin.ofNat, evmModulus, EvmYul.UInt256.size]
          simpa [hHaltState, Compiler.Proofs.abstractStoreStorageOrMapping,
            Compiler.Proofs.IRGeneration.IRStorageWord.ofNat, hArgMod] using hNative.symm
        · rw [hLogs, List.append_nil]

/-- Selector-miss direct-match native dispatcher bridge.

The native selector-miss path projects to the same revert result as the IR
selector-miss interpreter case, so this proof avoids the compatibility
fuel-wrapper bridge entirely. -/
theorem simpleStorageNativeSelectorMissMatchBridge_proved
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus) :
    simpleStorageNativeSelectorMissMatchBridge tx initialState observableSlots := by
  intro hSelMissRetrieve hSelMissStore
  have hSelEq : tx.functionSelector % selectorModulus = tx.functionSelector :=
    Nat.mod_eq_of_lt hselector
  have hSelMissTxStore : tx.functionSelector ≠ 0x6057361d := by
    rw [← hSelEq]
    exact hSelMissStore
  have hSelMissTxRetrieve : tx.functionSelector ≠ 0x2e64cec1 := by
    rw [← hSelEq]
    exact hSelMissRetrieve
  have hIR := interpretIR_simpleStorage_selectorMiss tx initialState
    hSelMissTxStore hSelMissTxRetrieve
  refine nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match
    (err := EvmYul.Yul.Exception.Revert)
    (nativeYul :=
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events })
    ?_ ?_ ?_
  · apply simpleStorageNativeContract_dispatcherExec_selectorMiss_revert_atFuel
    · have hMod :
          (YulTransaction.ofIR tx).functionSelector
            % Compiler.Constants.selectorModulus
            < Compiler.Constants.selectorModulus :=
        Nat.mod_lt _ (by decide)
      exact Nat.lt_trans hMod (by decide)
    · change (YulTransaction.ofIR tx).functionSelector % selectorModulus ≠ _
      change tx.functionSelector % selectorModulus ≠ _
      exact hSelMissStore
    · change (YulTransaction.ofIR tx).functionSelector % selectorModulus ≠ _
      change tx.functionSelector % selectorModulus ≠ _
      exact hSelMissRetrieve
    · change 4 + (YulTransaction.ofIR tx).args.length * 32 < EvmYul.UInt256.size
      change 4 + tx.args.length * 32 < EvmYul.UInt256.size
      simpa [evmModulus, EvmYul.UInt256.size] using hNoWrap
  · rfl
  · rw [hIR]
    exact ⟨rfl, rfl, (by intro slot _; rfl), rfl⟩

/-- Recover the direct-match monolithic SimpleStorage dispatcher obligation
from the three direct per-case sub-bridges. -/
theorem simpleStorageNativeCallDispatcherMatchBridge_of_per_case
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hRetrieveHit :
      simpleStorageNativeRetrieveHitMatchBridge tx initialState observableSlots)
    (hStoreHit :
      simpleStorageNativeStoreHitMatchBridge tx initialState observableSlots)
    (hSelectorMiss :
      simpleStorageNativeSelectorMissMatchBridge tx initialState observableSlots) :
    simpleStorageNativeCallDispatcherMatchBridge tx initialState observableSlots := by
  unfold simpleStorageNativeCallDispatcherMatchBridge
  by_cases hR :
      tx.functionSelector % Compiler.Constants.selectorModulus = 0x2e64cec1
  · exact hRetrieveHit hR
  · by_cases hS :
        tx.functionSelector % Compiler.Constants.selectorModulus = 0x6057361d
    · exact hStoreHit hS
    · exact hSelectorMiss hR hS

/-- SimpleStorage end-to-end: compile → IR → EVMYulLean-backed Yul preserves
semantics. The concrete function-body bridge witnesses are discharged above. -/
theorem simpleStorage_endToEnd_evmYulLeanBackend
    (tx : IRTransaction) (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hvars : initialState.vars = [])
    (hmemory : initialState.memory = fun _ => 0)
    (htransient : initialState.transientStorage = fun _ => 0)
    (hreturn : initialState.returnValue = none)
    (hdispatchGuardSafe : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      DispatchGuardsSafe fn tx)
    (hNoHasSelector : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      yulStmtsNoRef "__has_selector" fn.body)
    (hHasSelectorDead : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      HasSelectorDeadBridge fn.body)
    (hparamErase : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      paramLoadErasure fn tx (initialState.withTx tx)) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR simpleStorageIRContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackend .evmYulLean (Compiler.emitYul simpleStorageIRContract).runtimeCode
        (YulTransaction.ofIR tx) initialState.storage initialState.events) :=
  layer3_contract_preserves_semantics_evmYulLeanBackend simpleStorageIRContract tx initialState
    hselector hNoWrap hvars hmemory htransient hreturn hparamErase
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead
    (by intro fn hmem; simp [simpleStorageIRContract] at hmem ⊢; rcases hmem with rfl | rfl <;> rfl)
    (by intro s hs; simp [simpleStorageIRContract] at hs) rfl rfl
    simpleStorage_functions_bridged

/-- Native SimpleStorage wrapper at the positive dispatcher-exec direct-match
target.

Callers prove the lowered dispatcher result matches `interpretIR` directly,
without comparing through the compatibility EVMYulLean fuel-wrapper bridge. -/
theorem simpleStorage_endToEnd_native_evmYulLean_of_positive_dispatcherExec_match
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hEnv :
        Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
          (Compiler.emitYul simpleStorageIRContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ())
    (hNativeDispatcherExec :
      nativeDispatcherExecMatchesIRPositive
        simpleStorageNativeDispatcherFuel simpleStorageIRContract tx initialState
        observableSlots Compiler.SimpleStorageNativeWitness.nativeContract) :
    nativeResultsMatchOn observableSlots
      (interpretIR simpleStorageIRContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        (sizeOf (Compiler.emitYul simpleStorageIRContract).runtimeCode + 1)
        simpleStorageIRContract tx initialState observableSlots) := by
  rw [simpleStorage_runtimeCode_eq_single_dispatcher]
  exact
    layer3_contract_preserves_semantics_native_of_generated_dispatcherExec_positive_match
      simpleStorageNativeDispatcherFuel simpleStorageIRContract tx initialState
      observableSlots Compiler.SimpleStorageNativeWitness.nativeContract
      (by
        simp [simpleStorageIRContract,
          Compiler.Proofs.YulGeneration.Backends.Native.generatedRuntimeFunctionNamesUnique,
          Compiler.Proofs.YulGeneration.Backends.Native.stringListHasDuplicate])
      (by
        intro stmt hmem
        simp [simpleStorageIRContract] at hmem)
      (by
        intro fn hmem
        simp [simpleStorageIRContract] at hmem ⊢
        rcases hmem with rfl | rfl <;> rfl)
      (by
        intro name params rets body hmem
        simp [simpleStorageIRContract] at hmem)
      rfl
      rfl
      Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_eq
      hEnv
      hNativeDispatcherExec

/-- Native SimpleStorage end-to-end theorem with the concrete native dispatcher
bridge fully discharged for retrieve hit, store hit, and selector miss. -/
theorem simpleStorage_endToEnd_native_evmYulLean
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (_hvars : initialState.vars = [])
    (_hmemory : initialState.memory = fun _ => 0)
    (_htransient : initialState.transientStorage = fun _ => 0)
    (_hreturn : initialState.returnValue = none)
    (hdispatchGuardSafe : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      DispatchGuardsSafe fn tx)
    (_hNoHasSelector : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      yulStmtsNoRef "__has_selector" fn.body)
    (_hHasSelectorDead : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      HasSelectorDeadBridge fn.body)
    (_hparamErase : ∀ fn, fn ∈ simpleStorageIRContract.functions →
      paramLoadErasure fn tx (initialState.withTx tx))
    (hEnv :
        Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
          (Compiler.emitYul simpleStorageIRContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ()) :
    nativeResultsMatchOn observableSlots
      (interpretIR simpleStorageIRContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        (sizeOf (Compiler.emitYul simpleStorageIRContract).runtimeCode + 1)
        simpleStorageIRContract tx initialState observableSlots) :=
  simpleStorage_endToEnd_native_evmYulLean_of_positive_dispatcherExec_match
    tx initialState observableSlots hEnv
    (simpleStorageNativeCallDispatcherMatchBridge_of_per_case
      tx initialState observableSlots
      (simpleStorageNativeRetrieveHitMatchBridge_proved tx initialState
        observableSlots hselector hNoWrap hdispatchGuardSafe)
      (simpleStorageNativeStoreHitMatchBridge_proved tx initialState
        observableSlots hselector hNoWrap hdispatchGuardSafe)
      (simpleStorageNativeSelectorMissMatchBridge_proved tx initialState
        observableSlots hselector hNoWrap))

/-! ## Universal Pure Arithmetic Bridge

The pure arithmetic bridge proofs (`pure_add_bridge`, etc.) were removed
after the `evalBuiltinCall` refactor (commit e5da6c7f) which added
`callvalue`/`calldatasize` support, making `evalBuiltinCall` too large
for the default heartbeat limit during type-checking. The proofs were
mathematically correct but need `evalBuiltinCall` to be factored into
smaller pieces before they can be re-stated without timeout.

See: `ArithmeticProfile.lean` and
`YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean` for the current
replacement coverage: universal bridge lemmas for all pure bridged builtins.
-/

/-! ## Phase 4: EVMYulLean as Semantic Target

The historical Yul execution semantics used throughout this file dispatch builtins via
`evalBuiltinCallWithBackendContext legacyBuiltinBackend`, where
`legacyBuiltinBackend = .verity`. The EVMYulLean bridge
(`EvmYulLeanBridgeLemmas.lean`) proves that for all 36 bridged builtins,
the `.verity` and `.evmYulLean` backends produce identical results.

This means the existing preservation theorems above are pointwise valid under
EVMYulLean semantics for any single bridged-builtin call site whose bridge
dependencies are fully proven. The retargeting module
(`EvmYulLeanRetarget.lean`) makes this explicit with
`backends_agree_on_bridged_builtins`, lifts it through `BridgedExpr`
expression evaluation, proves statement-fragment helpers for straight-line,
block, if, switch, and for cases, and now proves recursive
`BridgedTarget` execution equivalence. It also proves
`emitYul_runtimeCode_bridged`, the emitted-runtime closure witness conditional
on bridged IR function, entrypoint, and internal helper bodies, and
  `emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies`, the corresponding
  emitted-runtime equality between Verity `legacyExecYulFuel` and the EVMYulLean
  backend executor under those body witnesses. These theorems compose the
  fully proven builtin bridge equivalences. It also proves
  `yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle`, the
  lower-level Layer-3 theorem whose Yul side is the EVMYulLean backend runtime.
  This file now exposes
  EndToEnd wrappers
  `layer3_contract_preserves_semantics_evmYulLeanBackend_with_function_bridge`,
  `layer3_contract_preserves_semantics_evmYulLeanBackend`,
  `layers2_3_ir_matches_yul_evmYulLeanBackend`, and
  `simpleStorage_endToEnd_evmYulLeanBackend` over that target. The public
  `layers2_3_ir_matches_yul_evmYulLeanBackend` wrapper discharges raw external
  function-body bridge witnesses from `SupportedSpec`, static-parameter
  witnesses, and `BridgedSafeStmts` source-body witnesses.
  Body-closure increments also prove scalar and static-scalar calldata
  parameter prologues satisfy `BridgedStmts`, pure source-expression fragments
  compile to `BridgedExpr`, and universal `compileStmtList_always_bridged`
  coverage for source bodies admitted by `BridgedSafeStmts`.

**Trust boundary after Phase 4 (recursive statement-target fragment)**:
- For any single bridged-builtin call whose bridge dependencies are fully
  proven, the Yul semantics trust assumption shifts from "Verity's custom
  builtin implementations are correct" to "EVMYulLean's execution model
  matches the EVM" (backed by upstream Ethereum conformance tests).
- `BridgedTarget` statement and statement-list executions inherit that same
  backend equivalence when their nested statements satisfy `BridgedStmt`.
- The generated runtime dispatch wrapper is now known to satisfy `BridgedTarget`
  and execute equivalently under the EVMYulLean backend when the IR bodies it
  embeds satisfy `BridgedStmt`.
- Layer 3 now has a contract-level theorem targeting
  `interpretYulRuntimeWithBackend .evmYulLean`; the public safe-body wrapper
  derives its raw body witnesses from supported source bodies.
- This public EndToEnd module now has a safe-body wrapper targeting
  `interpretYulRuntimeWithBackend .evmYulLean` without raw `BridgedStmts`
  body hypotheses; the historical Verity-backed public `via_reference_oracle`
  EndToEnd wrappers have been removed.
- Scalar and static-scalar calldata parameter-loading prologues are now known
  to satisfy `BridgedStmts`.
- Scalar source expression leaves and the pure arithmetic/comparison/bit-operation
  `BridgedSourceExpr` fragment are now known to compile to `BridgedExpr`.
- Scalar-leaf and pure-expression `letVar`/`assignVar` statement lists are now
  known to compile to `BridgedStmts`.
- Pure-binding plus unpacked single-slot `setStorage` statement lists and
  external `stop`/`return` terminators are now known to compile to
  `BridgedStmts`.
- Internal `return` terminators are now known to compile to assignment-plus-
  `leave` `BridgedStmts`.
- Plain `Stmt.require` statement lists with bridged failure conditions are
  now known to compile to `BridgedStmts` (the generated revert-message body
  is hypothesis-free).
- 36 of 36 builtins are bridged, including `mappingSlot` via the shared
  keccak-faithful `abstractMappingSlot` derivation.
- 0 bridge lemmas use `sorry`; all builtin bridge equivalences are proven.
- The external-call/function-table family remains outside `BridgedSafeStmts`
  and needs separate simulation work before it can be admitted into the
  safe-body EndToEnd wrapper.

See `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean` for
the Phase 4 retargeting theorems.
-/

end Compiler.Proofs.EndToEnd
