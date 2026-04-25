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
    (sizeOf (Compiler.emitYul simpleStorageIRContract).runtimeCode)
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
          hNativeCallDispatcher)))

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
