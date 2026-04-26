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

/-- Observable native result comparison for the current native bridge.

The native EVMYulLean state bridge materializes only the storage slots supplied
by the caller. Until the generated-fragment bridge proves a complete storage
projection, native-facing theorems compare success, return value, events, and
the explicitly observable final-storage slots. -/
def yulResultsAgreeOn
    (observableSlots : List Nat) (left right : YulResult) : Prop :=
  left.success = right.success ∧
  left.returnValue = right.returnValue ∧
  (∀ slot, slot ∈ observableSlots → left.finalStorage slot = right.finalStorage slot) ∧
  left.events = right.events

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
      (∀ slot, slot ∈ observableSlots → ir.finalStorage slot = yul.finalStorage slot) ∧
      ir.events = yul.events
  | .error _ => False

theorem nativeResultsMatchOn_ok_of_resultsMatch_of_yulResultsAgreeOn
    {observableSlots : List Nat} {ir : IRResult} {native oracle : YulResult}
    (hLayer : Compiler.Proofs.YulGeneration.resultsMatch ir oracle)
    (hNative : yulResultsAgreeOn observableSlots native oracle) :
    nativeResultsMatchOn observableSlots ir (.ok native) := by
  rcases hLayer with ⟨hsuccess, hreturnValue, hstorage, _hmappings, hevents⟩
  rcases hNative with ⟨hnativeSuccess, hnativeReturnValue, hnativeStorage, hnativeEvents⟩
  exact ⟨
    hsuccess.trans hnativeSuccess.symm,
    hreturnValue.trans hnativeReturnValue.symm,
    (by
      intro slot hslot
      exact (hstorage slot).trans (hnativeStorage slot hslot).symm),
    hevents.trans hnativeEvents.symm
  ⟩

theorem yulResultsAgreeOn_of_resultsMatch_of_nativeResultsMatchOn
    {observableSlots : List Nat} {ir : IRResult} {native oracle : YulResult}
    (hOracle : Compiler.Proofs.YulGeneration.resultsMatch ir oracle)
    (hNative : nativeResultsMatchOn observableSlots ir (.ok native)) :
    yulResultsAgreeOn observableSlots native oracle := by
  rcases hOracle with ⟨hsuccess, hreturnValue, hstorage, _hmappings, hevents⟩
  rcases hNative with ⟨hnativeSuccess, hnativeReturnValue, hnativeStorage, hnativeEvents⟩
  exact ⟨
    hnativeSuccess.symm.trans hsuccess,
    hnativeReturnValue.symm.trans hreturnValue,
    (by
      intro slot hslot
      exact (hnativeStorage slot hslot).symm.trans (hstorage slot)),
    hnativeEvents.symm.trans hevents
  ⟩

/-- The exact semantic bridge still needed before the public theorem can be
retargeted unconditionally to native EVMYulLean.

This predicate is intentionally concrete: it compares the current
fuel-aligned EVMYulLean-backed interpreter oracle with
`Native.interpretIRRuntimeNative` on the actual `Compiler.emitYul` runtime code
for an `IRContract`, under the same explicit fuel bound and observable
storage-slot set. -/
def nativeIRRuntimeAgreesWithInterpreter
    (fuel : Nat)
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat) :
    Prop :=
  match Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
      fuel contract tx state observableSlots with
  | .ok native =>
      yulResultsAgreeOn observableSlots native
        (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
          .evmYulLean fuel (Compiler.emitYul contract).runtimeCode
          (YulTransaction.ofIR tx) state.storage state.events)
  | .error _ => False

/-- Intro form for the native/interpreter bridge obligation.

Native-lowering proofs can stay at the harness level: prove that
`interpretIRRuntimeNative` succeeds and that its projected result agrees with
the current interpreter oracle on the requested observable slots. This packages
those two facts as the public `nativeIRRuntimeAgreesWithInterpreter`
obligation consumed by the native EndToEnd seam. -/
theorem nativeIRRuntimeAgreesWithInterpreter_of_ok_agree
    {fuel : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat} {native : YulResult}
    (hNative :
      Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        fuel contract tx state observableSlots = .ok native)
    (hAgree :
      yulResultsAgreeOn observableSlots native
        (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
          .evmYulLean fuel (Compiler.emitYul contract).runtimeCode
          (YulTransaction.ofIR tx) state.storage state.events)) :
    nativeIRRuntimeAgreesWithInterpreter fuel contract tx state observableSlots := by
  unfold nativeIRRuntimeAgreesWithInterpreter
  rw [hNative]
  exact hAgree

/-- Concrete native execution agreement target after Verity runtime Yul has
successfully lowered to an EVMYulLean contract.

This is the next proof obligation under the opaque
`nativeIRRuntimeAgreesWithInterpreter` seam: compare the projected native
`callDispatcher` result with the fuel-aligned interpreter oracle on the same
emitted runtime code and observable storage slots. -/
def nativeCallDispatcherAgreesWithInterpreter
    (fuel : Nat)
    (contract : IRContract)
    (tx : IRTransaction)
    (state : IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract) :
    Prop :=
  yulResultsAgreeOn observableSlots
    (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      (YulTransaction.ofIR tx) state.storage state.events
      (EvmYul.Yul.callDispatcher fuel (some nativeContract)
        (Compiler.Proofs.YulGeneration.Backends.Native.initialState
          nativeContract (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots))))
    (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
      .evmYulLean fuel (Compiler.emitYul contract).runtimeCode
      (YulTransaction.ofIR tx) state.storage state.events)

/-- Lower-level native dispatcher agreement target.

For positive fuel this compares the interpreter oracle with direct
`EvmYul.Yul.exec` execution of the lowered contract's dispatcher block, after
the same empty call-frame setup and result projection used by `callDispatcher`.
This is the statement-execution preservation obligation needed next for the
generated fragment. The zero-fuel case is kept explicit so the theorem below is
total in `fuel`. -/
def nativeDispatcherBlockAgreesWithInterpreter
    (fuel : Nat)
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
    match fuel with
    | 0 =>
        .error EvmYul.Yul.Exception.OutOfFuel
    | Nat.succ fuel' =>
        Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherBlockResult
          fuel' nativeContract initial
  yulResultsAgreeOn observableSlots
    (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      (YulTransaction.ofIR tx) state.storage state.events nativeResult)
    (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
      .evmYulLean fuel (Compiler.emitYul contract).runtimeCode
      (YulTransaction.ofIR tx) state.storage state.events)

/-- Raw native dispatcher-exec agreement target.

This peels off the `contractDispatcherBlockResult` wrapper too: the remaining
native preservation proof can target the exact `EvmYul.Yul.exec` result for the
lowered dispatcher block, with only the final `callDispatcher` restoration and
return-list projection left around that raw result. -/
def nativeDispatcherExecAgreesWithInterpreter
    (fuel : Nat)
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
    match fuel with
    | 0 =>
        .error EvmYul.Yul.Exception.OutOfFuel
    | Nat.succ fuel' =>
        match
          Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherExecResult
            fuel' nativeContract initial with
        | .error err => .error err
        | .ok finalState =>
            let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
            .ok (restored, [])
  yulResultsAgreeOn observableSlots
    (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      (YulTransaction.ofIR tx) state.storage state.events nativeResult)
    (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
      .evmYulLean fuel (Compiler.emitYul contract).runtimeCode
      (YulTransaction.ofIR tx) state.storage state.events)

/-- Positive-fuel raw native dispatcher-exec agreement target.

This is the same selected-dispatcher obligation as
`nativeDispatcherExecAgreesWithInterpreter (Nat.succ fuel')`, but without the
dead zero-fuel branch. Concrete generated dispatchers such as SimpleStorage use
the compiler-emitted runtime size plus one as fuel, so their remaining seam can
target this smaller positive-fuel shape directly. -/
def nativeDispatcherExecAgreesWithInterpreterPositive
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
  yulResultsAgreeOn observableSlots
    (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
      (YulTransaction.ofIR tx) state.storage state.events nativeResult)
    (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
      .evmYulLean (Nat.succ fuel') (Compiler.emitYul contract).runtimeCode
      (YulTransaction.ofIR tx) state.storage state.events)

/-- Intro form for the positive-fuel raw dispatcher-exec bridge when native
execution finishes normally.

This is the positive-fuel counterpart of
`nativeDispatcherExecAgreesWithInterpreter_of_exec_ok_agree`, avoiding the
generic zero-fuel branch for generated dispatcher proofs that already know their
fuel is `Nat.succ fuel'`. -/
theorem nativeDispatcherExecAgreesWithInterpreterPositive_of_exec_ok_agree
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
    (hAgree :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      yulResultsAgreeOn observableSlots
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events
          (.ok
            (finalState.reviveJump.overwrite? initial |>.setStore initial,
              [])))
        (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
          .evmYulLean (Nat.succ fuel') (Compiler.emitYul contract).runtimeCode
          (YulTransaction.ofIR tx) state.storage state.events)) :
    nativeDispatcherExecAgreesWithInterpreterPositive fuel' contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecAgreesWithInterpreterPositive
  simp [hExec]
  exact hAgree

/-- Intro form for the positive-fuel raw dispatcher-exec bridge when native
execution halts through EVMYulLean's Yul halt channel (`stop`/`return`). -/
theorem nativeDispatcherExecAgreesWithInterpreterPositive_of_exec_yulHalt_agree
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
    (hAgree :
      yulResultsAgreeOn observableSlots
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events
          (.error (.YulHalt haltState haltValue)))
        (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
          .evmYulLean (Nat.succ fuel') (Compiler.emitYul contract).runtimeCode
          (YulTransaction.ofIR tx) state.storage state.events)) :
    nativeDispatcherExecAgreesWithInterpreterPositive fuel' contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecAgreesWithInterpreterPositive
  simp [hExec]
  exact hAgree

/-- Intro form for a positive-fuel raw dispatcher Yul halt when a concrete
native execution lemma already packages the projected `YulResult`.

The SimpleStorage store/retrieve selector-hit lemmas expose both the exact
`YulHalt` and the exact native projection. This helper turns those facts plus
agreement for the named projection into the raw dispatcher bridge obligation. -/
theorem nativeDispatcherExecAgreesWithInterpreterPositive_of_exec_yulHalt_project_eq_agree
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
    (hAgree :
      yulResultsAgreeOn observableSlots nativeYul
        (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
          .evmYulLean (Nat.succ fuel') (Compiler.emitYul contract).runtimeCode
          (YulTransaction.ofIR tx) state.storage state.events)) :
    nativeDispatcherExecAgreesWithInterpreterPositive fuel' contract tx state
      observableSlots nativeContract := by
  apply nativeDispatcherExecAgreesWithInterpreterPositive_of_exec_yulHalt_agree
  · exact hExec
  · rw [hProject]
    exact hAgree

/-- Intro form for the positive-fuel raw dispatcher-exec bridge when native
execution fails through a non-halt EVMYulLean exception. -/
theorem nativeDispatcherExecAgreesWithInterpreterPositive_of_exec_error_agree
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
    (hAgree :
      yulResultsAgreeOn observableSlots
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events (.error err))
        (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
          .evmYulLean (Nat.succ fuel') (Compiler.emitYul contract).runtimeCode
          (YulTransaction.ofIR tx) state.storage state.events)) :
    nativeDispatcherExecAgreesWithInterpreterPositive fuel' contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecAgreesWithInterpreterPositive
  simp [hExec]
  exact hAgree

/-- Intro form for a positive-fuel raw dispatcher error when a concrete native
execution lemma already packages the projected `YulResult`.

Generated dispatcher proofs such as SimpleStorage's default/revert branch prove
two facts at the lowered-switch boundary: the raw EVMYulLean exception, and the
exact `projectResult` value. This helper consumes that pair directly, so the
remaining case proof only has to establish agreement for the named projected
result. -/
theorem nativeDispatcherExecAgreesWithInterpreterPositive_of_exec_error_project_eq_agree
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
    (hAgree :
      yulResultsAgreeOn observableSlots nativeYul
        (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
          .evmYulLean (Nat.succ fuel') (Compiler.emitYul contract).runtimeCode
          (YulTransaction.ofIR tx) state.storage state.events)) :
    nativeDispatcherExecAgreesWithInterpreterPositive fuel' contract tx state
      observableSlots nativeContract := by
  apply nativeDispatcherExecAgreesWithInterpreterPositive_of_exec_error_agree
  · exact hExec
  · rw [hProject]
    exact hAgree

/-- Lift the positive-fuel dispatcher-exec obligation back to the generic raw
dispatcher bridge shape consumed by the existing native theorem stack. -/
theorem nativeDispatcherExecAgreesWithInterpreter_of_positive
    {fuel' : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hAgree :
      nativeDispatcherExecAgreesWithInterpreterPositive fuel' contract tx state
        observableSlots nativeContract) :
    nativeDispatcherExecAgreesWithInterpreter (Nat.succ fuel') contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecAgreesWithInterpreterPositive at hAgree
  unfold nativeDispatcherExecAgreesWithInterpreter
  simpa using hAgree

/-- Intro form for the positive-fuel raw dispatcher-exec bridge when native
execution finishes normally.

The remaining generated-fragment simulation can prove a concrete
`contractDispatcherExecResult = .ok finalState` fact, then prove observable
agreement for the restored/projected call-dispatcher result. This theorem
packages that pair as the public raw-dispatcher agreement obligation. -/
theorem nativeDispatcherExecAgreesWithInterpreter_of_exec_ok_agree
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
    (hAgree :
      let initial :=
        Compiler.Proofs.YulGeneration.Backends.Native.initialState nativeContract
          (YulTransaction.ofIR tx) state.storage
          (Compiler.Proofs.YulGeneration.Backends.Native.materializedStorageSlots
            (Compiler.runtimeCode contract) observableSlots)
      yulResultsAgreeOn observableSlots
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events
          (.ok
            (finalState.reviveJump.overwrite? initial |>.setStore initial,
              [])))
        (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
          .evmYulLean (Nat.succ fuel') (Compiler.emitYul contract).runtimeCode
          (YulTransaction.ofIR tx) state.storage state.events)) :
    nativeDispatcherExecAgreesWithInterpreter (Nat.succ fuel') contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecAgreesWithInterpreter
  simp [hExec]
  exact hAgree

/-- Intro form for the positive-fuel raw dispatcher-exec bridge when native
execution halts through EVMYulLean's Yul halt channel (`stop`/`return`). -/
theorem nativeDispatcherExecAgreesWithInterpreter_of_exec_yulHalt_agree
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
    (hAgree :
      yulResultsAgreeOn observableSlots
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events
          (.error (.YulHalt haltState haltValue)))
        (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
          .evmYulLean (Nat.succ fuel') (Compiler.emitYul contract).runtimeCode
          (YulTransaction.ofIR tx) state.storage state.events)) :
    nativeDispatcherExecAgreesWithInterpreter (Nat.succ fuel') contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecAgreesWithInterpreter
  simp [hExec]
  exact hAgree

/-- Intro form for the positive-fuel raw dispatcher-exec bridge when native
execution fails through a non-halt EVMYulLean exception.

This is useful for revert/fail-closed generated-fragment cases: after proving
the raw native exception and the projected oracle agreement, callers can close
the same raw-dispatcher obligation consumed by the public native theorem seam. -/
theorem nativeDispatcherExecAgreesWithInterpreter_of_exec_error_agree
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
    (hAgree :
      yulResultsAgreeOn observableSlots
        (Compiler.Proofs.YulGeneration.Backends.Native.projectResult
          (YulTransaction.ofIR tx) state.storage state.events (.error err))
        (Compiler.Proofs.YulGeneration.Backends.interpretYulRuntimeWithBackendFuel
          .evmYulLean (Nat.succ fuel') (Compiler.emitYul contract).runtimeCode
          (YulTransaction.ofIR tx) state.storage state.events)) :
    nativeDispatcherExecAgreesWithInterpreter (Nat.succ fuel') contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecAgreesWithInterpreter
  simp [hExec]
  exact hAgree

/-- Lift raw lowered-dispatcher `EvmYul.Yul.exec` agreement to the
dispatcher-block bridge obligation. -/
theorem nativeDispatcherBlockAgreesWithInterpreter_of_exec_agree
    {fuel : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hAgree :
      nativeDispatcherExecAgreesWithInterpreter fuel contract tx state
        observableSlots nativeContract) :
    nativeDispatcherBlockAgreesWithInterpreter fuel contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherExecAgreesWithInterpreter at hAgree
  unfold nativeDispatcherBlockAgreesWithInterpreter
  cases fuel with
  | zero =>
      simpa using hAgree
  | succ fuel' =>
      simpa [Compiler.Proofs.YulGeneration.Backends.Native.contractDispatcherBlockResult_eq_execResult]
        using hAgree

/-- Lift dispatcher-block execution agreement to the existing
`callDispatcher`-level bridge obligation. -/
theorem nativeCallDispatcherAgreesWithInterpreter_of_dispatcherBlock_agree
    {fuel : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hAgree :
      nativeDispatcherBlockAgreesWithInterpreter fuel contract tx state
        observableSlots nativeContract) :
    nativeCallDispatcherAgreesWithInterpreter fuel contract tx state
      observableSlots nativeContract := by
  unfold nativeDispatcherBlockAgreesWithInterpreter at hAgree
  unfold nativeCallDispatcherAgreesWithInterpreter
  cases fuel with
  | zero =>
      simpa [Compiler.Proofs.YulGeneration.Backends.Native.callDispatcher_zero]
        using hAgree
  | succ fuel' =>
      rw [Compiler.Proofs.YulGeneration.Backends.Native.callDispatcher_succ_eq_callDispatcherBlockResult]
      rw [Compiler.Proofs.YulGeneration.Backends.Native.callDispatcherBlockResult_initialState_eq_contractDispatcherBlockResult]
      simpa using hAgree

/-- Discharge the public native/interpreter bridge from concrete native
lowering, selected-path environment validation, and projected
`callDispatcher` agreement.

After this theorem, generated-fragment work can focus on facts about
`lowerRuntimeContractNative`, `validateNativeRuntimeEnvironment`, and
`EvmYul.Yul.callDispatcher` rather than re-opening the public native harness
wrapper. -/
theorem nativeIRRuntimeAgreesWithInterpreter_of_lowered_callDispatcher_agree
    {fuel : Nat} {contract : IRContract} {tx : IRTransaction}
    {state : IRState} {observableSlots : List Nat}
    {nativeContract : EvmYul.Yul.Ast.YulContract}
    (hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul contract).runtimeCode = .ok nativeContract)
    (hEnv :
      Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
        (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx) = .ok ())
    (hAgree :
      nativeCallDispatcherAgreesWithInterpreter fuel contract tx state
        observableSlots nativeContract) :
    nativeIRRuntimeAgreesWithInterpreter fuel contract tx state observableSlots := by
  apply nativeIRRuntimeAgreesWithInterpreter_of_ok_agree
  · exact
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
        fuel contract tx state observableSlots nativeContract hLower hEnv)
  · exact hAgree

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

/-- Native Layer 3 bridge theorem under the named generated-fragment bridge obligation. -/
theorem layer3_contract_preserves_semantics_native_of_interpreter_bridge
    (fuel : Nat) (contract : IRContract) (tx : IRTransaction)
    (initialState : IRState) (observableSlots : List Nat)
    (hselector : tx.functionSelector < selectorModulus) (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hvars : initialState.vars = []) (hmemory : initialState.memory = fun _ => 0)
    (htransient : initialState.transientStorage = fun _ => 0) (hreturn : initialState.returnValue = none)
    (hparamErase : ∀ fn, fn ∈ contract.functions → paramLoadErasure fn tx (initialState.withTx tx))
    (hdispatchGuardSafe : ∀ fn, fn ∈ contract.functions → DispatchGuardsSafe fn tx)
    (hNoHasSelector : ∀ fn, fn ∈ contract.functions → yulStmtsNoRef "__has_selector" fn.body)
    (hHasSelectorDead : ∀ fn, fn ∈ contract.functions → HasSelectorDeadBridge fn.body)
    (hLoopFree : ∀ fn, fn ∈ contract.functions → yulStmtsLoopFree fn.body = true)
    (hWF : ContractWF contract) (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none)
    (hFunctions : ∀ fn, fn ∈ contract.functions → Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body)
    (hFuel : fuel = sizeOf (Compiler.emitYul contract).runtimeCode + 1)
    (hNativeBridge : nativeIRRuntimeAgreesWithInterpreter fuel contract tx initialState observableSlots) :
    nativeResultsMatchOn observableSlots (interpretIR contract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        fuel contract tx initialState observableSlots) := by
  subst fuel
  have hLayer :=
    layer3_contract_preserves_semantics_evmYulLean contract tx initialState
      hselector hNoWrap hvars hmemory htransient hreturn hparamErase
      hdispatchGuardSafe hNoHasSelector hHasSelectorDead hLoopFree hWF hNoFallback
      hNoReceive hFunctions
  unfold nativeIRRuntimeAgreesWithInterpreter at hNativeBridge
  cases hNative :
      Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        (sizeOf (Compiler.emitYul contract).runtimeCode + 1)
        contract tx initialState observableSlots with
  | error err =>
      rw [hNative] at hNativeBridge
      exact False.elim hNativeBridge
  | ok native =>
      rw [hNative] at hNativeBridge
      exact nativeResultsMatchOn_ok_of_resultsMatch_of_yulResultsAgreeOn hLayer
        hNativeBridge

/-- Native Layer 3 bridge theorem with the remaining obligation stated at the
concrete lowered EVMYulLean contract boundary.

This variant removes the opaque `nativeIRRuntimeAgreesWithInterpreter`
hypothesis from callers. They instead prove native lowering succeeds, the
selected native runtime path has representable environment reads, and projected
`callDispatcher` execution agrees with the interpreter oracle. -/
theorem layer3_contract_preserves_semantics_native_of_lowered_callDispatcher_bridge
    (fuel : Nat) (contract : IRContract) (tx : IRTransaction)
    (initialState : IRState) (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hvars : initialState.vars = []) (hmemory : initialState.memory = fun _ => 0)
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
    (hLoopFree : ∀ fn, fn ∈ contract.functions → yulStmtsLoopFree fn.body = true)
    (hWF : ContractWF contract) (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none)
    (hFunctions : ∀ fn, fn ∈ contract.functions →
      Compiler.Proofs.YulGeneration.Backends.BridgedStmts fn.body)
    (hFuel : fuel = sizeOf (Compiler.emitYul contract).runtimeCode + 1)
    (hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul contract).runtimeCode = .ok nativeContract)
    (hEnv :
      Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
        (Compiler.emitYul contract).runtimeCode (YulTransaction.ofIR tx) = .ok ())
    (hNativeCallDispatcher :
      nativeCallDispatcherAgreesWithInterpreter fuel contract tx initialState
        observableSlots nativeContract) :
    nativeResultsMatchOn observableSlots (interpretIR contract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        fuel contract tx initialState observableSlots) :=
  layer3_contract_preserves_semantics_native_of_interpreter_bridge
    fuel contract tx initialState observableSlots
    hselector hNoWrap hvars hmemory htransient hreturn hparamErase
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead hLoopFree hWF hNoFallback
    hNoReceive hFunctions hFuel
    (nativeIRRuntimeAgreesWithInterpreter_of_lowered_callDispatcher_agree
      hLower hEnv hNativeCallDispatcher)

/-! ## Layers 2+3 Composition -/

/-- Reference-oracle end-to-end wrapper: given a successfully compiled
contract, IR execution matches the historical Verity-backed Yul execution
target. The EVMYulLean-backed theorem below is the authoritative safe-body
target after the Phase 4 retarget. -/
theorem layers2_3_ir_matches_yul_via_reference_oracle
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

/-- Native end-to-end theorem seam for supported compiler-produced contracts.

The conclusion targets `Native.interpretIRRuntimeNative` directly. The remaining
generated-fragment proof obligation is exactly
`nativeIRRuntimeAgreesWithInterpreter`: native EVMYulLean execution of the
emitted runtime code must agree with the current EVMYulLean-backed interpreter
oracle for the same fuel, transaction, initial storage/events, and observable
storage-slot materialization. -/
theorem layers2_3_ir_matches_native_evmYulLean_of_interpreter_bridge
    (fuel : Nat)
    (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (irContract : IRContract) (tx : IRTransaction)
    (initialState : IRState) (observableSlots : List Nat)
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
      Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hSafeBodies :
      ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts spec.fields
          spec.errors .calldata [] false entry.1.body)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hvars : initialState.vars = [])
    (hmemory : initialState.memory = fun _ => 0)
    (htransient : initialState.transientStorage = fun _ => 0)
    (hreturn : initialState.returnValue = none)
    (hparamErase : ∀ fn, fn ∈ irContract.functions →
      paramLoadErasure fn tx (initialState.withTx tx))
    (hdispatchGuardSafe : ∀ fn, fn ∈ irContract.functions → DispatchGuardsSafe fn tx)
    (hNoHasSelector : ∀ fn, fn ∈ irContract.functions → yulStmtsNoRef "__has_selector" fn.body)
    (hHasSelectorDead : ∀ fn, fn ∈ irContract.functions → HasSelectorDeadBridge fn.body)
    (hLoopFree : ∀ fn, fn ∈ irContract.functions → yulStmtsLoopFree fn.body = true)
    (hWF : ContractWF irContract) (hNoFallback : irContract.fallbackEntrypoint = none)
    (hNoReceive : irContract.receiveEntrypoint = none)
    (hFuel : fuel = sizeOf (Compiler.emitYul irContract).runtimeCode + 1)
    (hNativeBridge : nativeIRRuntimeAgreesWithInterpreter fuel irContract tx
      initialState observableSlots) :
    nativeResultsMatchOn observableSlots
      (interpretIR irContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        fuel irContract tx initialState observableSlots) :=
  layer3_contract_preserves_semantics_native_of_interpreter_bridge
    fuel irContract tx initialState observableSlots
    hselector hNoWrap hvars hmemory htransient hreturn hparamErase
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead hLoopFree hWF hNoFallback
    hNoReceive
    (compiledExternalFunctions_bridged_of_safe_static
      spec.fields spec.events spec.errors
      (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
        spec selectors hSupported irContract hCompile)
      hStaticParams hSafeBodies)
    hFuel
    hNativeBridge

/-- Supported compiler-produced native theorem seam with the remaining native
obligation exposed at the concrete lowered `callDispatcher` boundary. -/
theorem layers2_3_ir_matches_native_evmYulLean_of_lowered_callDispatcher_bridge
    (fuel : Nat) (spec : CompilationModel.CompilationModel) (selectors : List Nat)
    (irContract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (observableSlots : List Nat) (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hCompile : CompilationModel.compile spec selectors = .ok irContract)
    (hSupported : SupportedSpec spec selectors)
    (hStaticParams : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors → Compiler.Proofs.YulGeneration.Backends.AllStaticScalarParams entry.1.params)
    (hSafeBodies : ∀ entry, entry ∈ SourceSemantics.selectorFunctionPairs spec selectors →
        Compiler.Proofs.YulGeneration.Backends.BridgedSafeStmts spec.fields spec.errors .calldata [] false entry.1.body)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hvars : initialState.vars = [])
    (hmemory : initialState.memory = fun _ => 0)
    (htransient : initialState.transientStorage = fun _ => 0)
    (hreturn : initialState.returnValue = none)
    (hparamErase : ∀ fn, fn ∈ irContract.functions → paramLoadErasure fn tx (initialState.withTx tx))
    (hdispatchGuardSafe : ∀ fn, fn ∈ irContract.functions → DispatchGuardsSafe fn tx)
    (hNoHasSelector : ∀ fn, fn ∈ irContract.functions → yulStmtsNoRef "__has_selector" fn.body)
    (hHasSelectorDead : ∀ fn, fn ∈ irContract.functions → HasSelectorDeadBridge fn.body)
    (hLoopFree : ∀ fn, fn ∈ irContract.functions → yulStmtsLoopFree fn.body = true)
    (hWF : ContractWF irContract) (hNoFallback : irContract.fallbackEntrypoint = none)
    (hNoReceive : irContract.receiveEntrypoint = none)
    (hFuel : fuel = sizeOf (Compiler.emitYul irContract).runtimeCode + 1)
    (hLower : Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul irContract).runtimeCode = .ok nativeContract)
    (hEnv : Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
      (Compiler.emitYul irContract).runtimeCode (YulTransaction.ofIR tx) = .ok ())
    (hNativeCallDispatcher : nativeCallDispatcherAgreesWithInterpreter fuel irContract tx initialState observableSlots nativeContract) :
    nativeResultsMatchOn observableSlots (interpretIR irContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        fuel irContract tx initialState observableSlots) :=
  layer3_contract_preserves_semantics_native_of_lowered_callDispatcher_bridge
    fuel irContract tx initialState observableSlots nativeContract
    hselector hNoWrap hvars hmemory htransient hreturn hparamErase
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead hLoopFree hWF hNoFallback
    hNoReceive
    (compiledExternalFunctions_bridged_of_safe_static
      spec.fields spec.events spec.errors
      (Compiler.Proofs.IRGeneration.Contract.compile_ok_yields_compiled_functions
        spec selectors hSupported irContract hCompile)
      hStaticParams hSafeBodies)
    hFuel hLower hEnv hNativeCallDispatcher

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
    (tx : YulTransaction) (storage : Nat → Nat) (observableSlots : List Nat) :
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
    (tx : YulTransaction) (storage : Nat → Nat) (observableSlots : List Nat) :
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
    (storage : Nat → Nat) (observableSlots : List Nat)
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
    (storage : Nat → Nat) (observableSlots : List Nat)
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
    (storage : Nat → Nat) (observableSlots : List Nat)
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
    (tx : YulTransaction) (storage : Nat → Nat) (observableSlots : List Nat)
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
    (tx : YulTransaction) (storage : Nat → Nat) (observableSlots : List Nat)
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
    (tx : YulTransaction) (storage : Nat → Nat) (observableSlots : List Nat)
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
    (tx : YulTransaction) (storage : Nat → Nat) (observableSlots : List Nat)
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
    (tx : YulTransaction) (storage : Nat → Nat) (observableSlots : List Nat)
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

noncomputable def simpleStorageNativeDispatcherFuel : Nat :=
  sizeOf [Compiler.CodegenCommon.buildSwitch
    simpleStorageIRContract.functions none none]

/-- Named SimpleStorage native dispatcher bridge obligation.

This keeps the remaining native proof seam explicit and sorry-free. The missing
work is to prove that the lowered native dispatcher block selects and executes
the three generated bodies (`store(uint256)`, `retrieve()`, and selector-miss
`revert`) and that the projected native result agrees with the
EVMYulLean-backed interpreter oracle on the caller's observable storage
projection. The generic `callDispatcher` wrapper has already been discharged by
`nativeCallDispatcherAgreesWithInterpreter_of_dispatcherBlock_agree`, and the
dispatcher-block result wrapper has already been discharged by
`nativeDispatcherBlockAgreesWithInterpreter_of_exec_agree`. -/
def simpleStorageNativeCallDispatcherBridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
    : Prop :=
  nativeDispatcherExecAgreesWithInterpreterPositive
    simpleStorageNativeDispatcherFuel
    simpleStorageIRContract tx initialState observableSlots
    Compiler.SimpleStorageNativeWitness.nativeContract

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

/-- Native SimpleStorage wrapper with the lowering seam discharged.

This reduces the remaining concrete native proof work for `simpleStorage` to
two facts:
- the emitted runtime passes native environment validation for the current tx;
- the lowered native `callDispatcher` agrees with the interpreter oracle.
The concrete lowering witness is computed outside `Compiler/Proofs` and consumed
here only through its exported equality. -/
theorem simpleStorage_endToEnd_native_evmYulLean_of_callDispatcher_bridge
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
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
      paramLoadErasure fn tx (initialState.withTx tx))
    (hEnv :
      Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
        (Compiler.emitYul simpleStorageIRContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ())
    (hNativeCallDispatcher :
      nativeCallDispatcherAgreesWithInterpreter
        (sizeOf (Compiler.emitYul simpleStorageIRContract).runtimeCode + 1)
        simpleStorageIRContract tx initialState observableSlots
        Compiler.SimpleStorageNativeWitness.nativeContract) :
    nativeResultsMatchOn observableSlots
      (interpretIR simpleStorageIRContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        (sizeOf (Compiler.emitYul simpleStorageIRContract).runtimeCode + 1)
        simpleStorageIRContract tx initialState observableSlots) :=
  layer3_contract_preserves_semantics_native_of_lowered_callDispatcher_bridge
    (sizeOf (Compiler.emitYul simpleStorageIRContract).runtimeCode + 1)
    simpleStorageIRContract tx initialState observableSlots
    Compiler.SimpleStorageNativeWitness.nativeContract
    hselector hNoWrap hvars hmemory htransient hreturn hparamErase
    hdispatchGuardSafe hNoHasSelector hHasSelectorDead
    (by
      intro fn hmem
      simp [simpleStorageIRContract] at hmem ⊢
      rcases hmem with rfl | rfl <;> rfl)
    (by intro s hs; simp [simpleStorageIRContract] at hs)
    rfl
    rfl
    simpleStorage_functions_bridged
    rfl
    Compiler.SimpleStorageNativeWitness.lowerRuntimeContractNative_eq
    hEnv
    hNativeCallDispatcher

/-- Native SimpleStorage end-to-end theorem with the concrete native dispatcher
witness supplied explicitly.

This theorem targets native EVMYulLean execution, but it does not pretend the
remaining selected-body native dispatcher proof is complete. Callers must supply
`simpleStorageNativeCallDispatcherBridge` until that proof is discharged. -/
theorem simpleStorage_endToEnd_native_evmYulLean
    (tx : IRTransaction) (initialState : IRState) (observableSlots : List Nat)
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
      paramLoadErasure fn tx (initialState.withTx tx))
    (hNativeCallDispatcher :
      simpleStorageNativeCallDispatcherBridge tx initialState observableSlots)
    (hEnv :
      Compiler.Proofs.YulGeneration.Backends.Native.validateNativeRuntimeEnvironment
        (Compiler.emitYul simpleStorageIRContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ()) :
    nativeResultsMatchOn observableSlots
      (interpretIR simpleStorageIRContract tx initialState)
      (Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
        (sizeOf (Compiler.emitYul simpleStorageIRContract).runtimeCode + 1)
        simpleStorageIRContract tx initialState observableSlots) :=
  simpleStorage_endToEnd_native_evmYulLean_of_callDispatcher_bridge
    tx initialState observableSlots hselector hNoWrap hvars hmemory htransient
    hreturn hdispatchGuardSafe hNoHasSelector hHasSelectorDead hparamErase hEnv
    (nativeCallDispatcherAgreesWithInterpreter_of_dispatcherBlock_agree
      (nativeDispatcherBlockAgreesWithInterpreter_of_exec_agree
        (nativeDispatcherExecAgreesWithInterpreter_of_positive
          (by
            rw [simpleStorage_runtimeCode_eq_single_dispatcher]
            exact hNativeCallDispatcher))))

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
  body hypotheses; the historical
  `layers2_3_ir_matches_yul_via_reference_oracle` wrapper remains available
  for the Verity-backed `interpretYulFromIR` target.
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
