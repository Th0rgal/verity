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

  **EVMYulLean note (Phase 4)**: This file now exposes both the historical
  Verity-backed Yul target (`interpretYulFromIR`) and safe-body public wrappers
  targeting `interpretYulRuntimeWithBackend .evmYulLean`.
  The default Yul execution semantics (`interpretYulFromIR`, `interpretYulRuntime`)
  are still defined in terms of `evalBuiltinCallWithBackend` which defaults to
  the Verity backend. The EVMYulLean bridge is established in
  `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean`, proving
  that for all 36 bridged builtins, the Verity backend agrees with EVMYulLean.
  The Phase 4 retargeting module (`EvmYulLeanRetarget.lean`) composes these
  per-builtin equivalences through expression evaluation and recursive
  `BridgedTarget` statement execution. It also proves that the emitted runtime
  wrapper satisfies that predicate, and executes equivalently under the
  EVMYulLean backend, when the IR bodies it contains do. It also exposes a
  lower-level Layer-3 theorem whose Yul side is
  `interpretYulRuntimeWithBackend .evmYulLean` and whose body witnesses are
  supplied by this file's public wrappers. Those wrappers derive raw external
  function-body bridge witnesses from source-level `SupportedSpec`,
  static-parameter, and `BridgedSafeStmts` witnesses where the public theorem
  applies.

  Run: lake build Compiler.Proofs.EndToEnd
-/

import Compiler.Proofs.YulGeneration.Preservation
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBodyClosure
import Compiler.Proofs.IRGeneration.Contract
import Compiler.Proofs.IRGeneration.Function
import Compiler.Proofs.IRGeneration.Expr

namespace Compiler.Proofs.EndToEnd

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration

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
    (stmts : List Yul.YulStmt) (tx : YulTransaction) (stor : Nat → Nat)
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
      CompilationModel.compileFunctionSpec fields events errors selector spec =
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
            entry.2 entry.1 = Except.ok irFn)
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

/-! ## Layer 3 Contract-Level: IR → Yul (via runtime dispatch) -/

/-- Layer 3 contract-level preservation: an IR contract execution produces
equivalent results under the Yul runtime dispatch. -/
theorem layer3_contract_preserves_semantics
    (contract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hvars : initialState.vars = [])
    (hmemory : initialState.memory = fun _ => 0)
    (htransient : initialState.transientStorage = fun _ => 0)
    (hreturn : initialState.returnValue = none)
    (hparamErase : ∀ fn, fn ∈ contract.functions →
      paramLoadErasure fn tx (initialState.withTx tx))
    (hdispatchGuardSafe : ∀ fn, fn ∈ contract.functions →
      DispatchGuardsSafe fn tx)
    (hNoHasSelector : ∀ fn, fn ∈ contract.functions →
      yulStmtsNoRef "__has_selector" fn.body)
    (hHasSelectorDead : ∀ fn, fn ∈ contract.functions →
      HasSelectorDeadBridge fn.body)
    (hLoopFree : ∀ fn, fn ∈ contract.functions →
      yulStmtsLoopFree fn.body = true)
    (hWF : ContractWF contract)
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR contract tx initialState)
      (interpretYulFromIR contract tx initialState) := by
  apply yulCodegen_preserves_semantics contract tx initialState
    hselector hNoWrap hWF hNoFallback hNoReceive hdispatchGuardSafe hNoHasSelector hHasSelectorDead
    hLoopFree
  · intro fn hmem
    exact (yulBody_from_state_eq_yulBody fn tx (initialState.withTx tx)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by simpa using hreturn)
      (by simpa using hmemory)
      (by simpa using htransient)
      (by simpa using hvars)
      (hparamErase fn hmem))

/-- Reference-oracle version: delegates directly to the historical
`execYulFuel`-backed `yulCodegen_preserves_semantics` theorem. -/
theorem layer3_contract_preserves_semantics_via_reference_oracle
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
        (interpretYulBody fn tx (initialState.withTx tx))) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR contract tx initialState)
      (interpretYulFromIR contract tx initialState) :=
  yulCodegen_preserves_semantics contract tx initialState
    hselector hNoWrap hWF hNoFallback hNoReceive hdispatchGuardSafe hNoHasSelector hHasSelectorDead
    hLoopFree hbody

/-! ## Layer 3 Contract-Level: IR → EVMYulLean-backed Yul -/

/-- Lower-level Layer 3 contract-level preservation targeting the
EVMYulLean-backed Yul runtime. This is the EndToEnd-facing wrapper around
`yulCodegen_preserves_semantics_evmYulLean`; callers supply the existing
function-body simulation hypotheses plus `BridgedStmts` witnesses for emitted
external function bodies. Fallback/receive witnesses are discharged from the
existing `none` hypotheses, and the internal-function table witness is derived
from `ContractWF`. -/
theorem layer3_contract_preserves_semantics_evmYulLean_with_function_bridge
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
      (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackend
        .evmYulLean (Compiler.emitYul contract).runtimeCode
        (YulTransaction.ofIR tx) initialState.storage initialState.events) :=
  Compiler.Proofs.YulGeneration.Backends.yulCodegen_preserves_semantics_evmYulLean
    contract tx initialState hselector hNoWrap hWF hNoFallback hNoReceive
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead hLoopFree hbody
    hFunctions
    (by intro fb hSome; rw [hNoFallback] at hSome; cases hSome)
    (by intro rc hSome; rw [hNoReceive] at hSome; cases hSome)
    (internalFunctions_bridged_of_contractWF contract hWF)

/-- Layer 3 contract-level preservation targeting EVMYulLean under explicit
function-body bridge witnesses, using the same entry-state normalization hypotheses as
`layer3_contract_preserves_semantics`. -/
theorem layer3_contract_preserves_semantics_evmYulLean
    (contract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hvars : initialState.vars = [])
    (hmemory : initialState.memory = fun _ => 0)
    (htransient : initialState.transientStorage = fun _ => 0)
    (hreturn : initialState.returnValue = none)
    (hparamErase : ∀ fn, fn ∈ contract.functions →
      paramLoadErasure fn tx (initialState.withTx tx))
    (hdispatchGuardSafe : ∀ fn, fn ∈ contract.functions →
      DispatchGuardsSafe fn tx)
    (hNoHasSelector : ∀ fn, fn ∈ contract.functions →
      yulStmtsNoRef "__has_selector" fn.body)
    (hHasSelectorDead : ∀ fn, fn ∈ contract.functions →
      HasSelectorDeadBridge fn.body)
    (hLoopFree : ∀ fn, fn ∈ contract.functions →
      yulStmtsLoopFree fn.body = true)
    (hWF : ContractWF contract)
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none)
    (hFunctions : ∀ fn, fn ∈ contract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR contract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackend
        .evmYulLean (Compiler.emitYul contract).runtimeCode
        (YulTransaction.ofIR tx) initialState.storage initialState.events) := by
  apply layer3_contract_preserves_semantics_evmYulLean_with_function_bridge contract tx initialState
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

/-! ## Layers 2+3 Composition -/

/-- End-to-end: given a successfully compiled contract, IR execution matches
Yul execution. -/
theorem layers2_3_ir_matches_yul
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
    (hNoReceive : irContract.receiveEntrypoint = none) :
    Compiler.Proofs.YulGeneration.resultsMatch
      (interpretIR irContract tx initialState)
      (interpretYulFromIR irContract tx initialState) :=
  layer3_contract_preserves_semantics irContract tx initialState
    hselector hNoWrap hvars hmemory htransient hreturn hparamErase hdispatchGuardSafe hNoHasSelector
    hHasSelectorDead hLoopFree hWF hNoFallback hNoReceive

/-- End-to-end bridge-witness variant: given a successfully compiled contract,
IR execution matches EVMYulLean-backed Yul execution under explicit
function-body closure hypotheses. Fallback/receive bridge witnesses are
vacuous under the public `none` hypotheses and are discharged internally, as is
the internal function table witness via `ContractWF`. -/
theorem layers2_3_ir_matches_yul_evmYulLean_with_function_bridge
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
      (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackend
        .evmYulLean (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) initialState.storage initialState.events) :=
  layer3_contract_preserves_semantics_evmYulLean irContract tx initialState
    hselector hNoWrap hvars hmemory htransient hreturn hparamErase
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead hLoopFree hWF hNoFallback
    hNoReceive hFunctions

/-- End-to-end: for a supported compiler-produced contract whose
selector-dispatched function bodies are in the EVMYulLean-safe source fragment
and whose ABI parameters compile through the static-scalar prologue bridge, IR
execution matches EVMYulLean-backed Yul execution without exposing a raw
`BridgedStmts fn.body` hypothesis to callers. -/
theorem layers2_3_ir_matches_yul_evmYulLean
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
      (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackend
        .evmYulLean (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) initialState.storage initialState.events) :=
  layers2_3_ir_matches_yul_evmYulLean_with_function_bridge
    spec selectors irContract tx initialState
    hCompile hselector hNoWrap hvars hmemory htransient hreturn hparamErase
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead hLoopFree hWF hNoFallback
    hNoReceive
    (compiledExternalFunctions_bridged_of_safe_static
      spec.fields spec.events spec.errors
      (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
        spec selectors hSupported irContract hCompile)
      hStaticParams hSafeBodies)

/-! ## Concrete Instantiation: SimpleStorage -/

/-- SimpleStorage end-to-end: compile → IR → Yul preserves semantics. -/
theorem simpleStorage_endToEnd
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
      (interpretYulFromIR simpleStorageIRContract tx initialState) :=
  layer3_contract_preserves_semantics simpleStorageIRContract tx initialState
    hselector hNoWrap hvars hmemory htransient hreturn hparamErase hdispatchGuardSafe hNoHasSelector
    hHasSelectorDead
    (by intro fn hmem; simp [simpleStorageIRContract] at hmem ⊢; rcases hmem with rfl | rfl <;> rfl)
    (by intro s hs; simp [simpleStorageIRContract] at hs) rfl rfl

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

/-- SimpleStorage end-to-end: compile → IR → EVMYulLean-backed Yul preserves
semantics. The concrete function-body bridge witnesses are discharged above. -/
theorem simpleStorage_endToEnd_evmYulLean
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
      (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackend
        .evmYulLean (Compiler.emitYul simpleStorageIRContract).runtimeCode
        (YulTransaction.ofIR tx) initialState.storage initialState.events) :=
  layer3_contract_preserves_semantics_evmYulLean simpleStorageIRContract tx initialState
    hselector hNoWrap hvars hmemory htransient hreturn hparamErase
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead
    (by intro fn hmem; simp [simpleStorageIRContract] at hmem ⊢; rcases hmem with rfl | rfl <;> rfl)
    (by intro s hs; simp [simpleStorageIRContract] at hs) rfl rfl
    simpleStorage_functions_bridged

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
`evalBuiltinCallWithBackendContext defaultBuiltinBackend`, where
`defaultBuiltinBackend = .verity`. The EVMYulLean bridge
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
  emitted-runtime equality between Verity `execYulFuel` and the EVMYulLean
  backend executor under those body witnesses. These theorems compose the
  fully proven builtin bridge equivalences. It also proves
  `yulCodegen_preserves_semantics_evmYulLean`, the lower-level Layer-3 theorem
  whose Yul side is the EVMYulLean backend runtime. This file now exposes
  EndToEnd wrappers
  `layer3_contract_preserves_semantics_evmYulLean_with_function_bridge`,
  `layer3_contract_preserves_semantics_evmYulLean`,
  `layers2_3_ir_matches_yul_evmYulLean`, and
  `simpleStorage_endToEnd_evmYulLean` over that target. The public
  `layers2_3_ir_matches_yul_evmYulLean` wrapper discharges raw external
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
  body hypotheses; the historical wrappers remain available for the
  Verity-backed `interpretYulFromIR` target.
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
