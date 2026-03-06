/-
  Compiler.Proofs.SemanticBridge: Full EDSL ≡ Compiled IR theorem statements

  This file states the *target* theorem per contract function: that EDSL execution
  produces the same storage effects as compiling the CompilationModel spec and
  interpreting the resulting IR.

  Unlike the macro-generated `_semantic_preservation` theorems (which live in the
  contract namespace and cannot import IR types), these theorems import the full
  IR execution machinery and state the precise equivalence:

    ∀ slot, (edslFinalState.storage slot).val = irResult.finalStorage slot

  **Status (post-evalBuiltinCall refactor, e5da6c7f)**: All proofs in this file
  used `simp` to unfold the full IR execution chain including `evalBuiltinCall`.
  After the refactor added `callvalue`/`calldatasize` support, `evalBuiltinCall`
  became too large for `simp`/`isDefEq` to reduce within the heartbeat limit.
  The theorem *statements* are preserved; proofs use placeholders until
  `evalBuiltinCall` is factored into smaller pieces.

  **Why a separate file**: The macro-generated theorems cannot import
  `Compiler.Proofs.IRGeneration.IRInterpreter` (it would transitively pull
  in EVMYulLean and bloat every contract file). This file bridges the gap by
  importing both the EDSL types and the IR execution types, stating the
  theorems that directly reference `interpretIR`.

  Run: lake build Compiler.Proofs.SemanticBridge
-/

import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.EndToEnd
import Compiler.Specs
import Verity.Core
import Contracts.MacroContracts.Core
import Lean

namespace Compiler.Proofs.SemanticBridge

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Verity
open Verity.Core.Uint256
open Lean Parser Tactic

/-! ## Bridge Tactic Helpers -/

/-- Canonical `simp` bundle for SemanticBridge IR execution unfolding. -/
syntax (name := semantic_bridge_simp) "semantic_bridge_simp" : tactic

/-- `semantic_bridge_simp` with extra local unfold/simp terms. -/
syntax (name := semantic_bridge_simp_with)
  "semantic_bridge_simp [" term,* "]" : tactic

/-- `semantic_bridge_split h : cond with [...]` generates the common
    two-branch `by_cases` skeleton and runs `semantic_bridge_simp` in both
    branches with the same simp bundle plus the branch hypothesis. -/
syntax (name := semantic_bridge_split)
  "semantic_bridge_split " ident " : " term " with [" term,* "]" : tactic

/-- `semantic_bridge_owner h with [...]` discharges the common owner
    precondition by `subst`-ing the equality hypothesis, then runs
    `semantic_bridge_simp` with the provided simp bundle. -/
syntax (name := semantic_bridge_owner)
  "semantic_bridge_owner " ident " with [" term,* "]" : tactic

macro_rules
  | `(tactic| semantic_bridge_simp) =>
      `(tactic| simp [
        mkIRTransaction, mkIRState, interpretIR,
        execIRFunction, execIRStmts, execIRStmt,
        evalIRExpr, evalIRCall, evalIRExprs, IRState.getVar, IRState.setVar,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackend,
        Compiler.Proofs.YulGeneration.evalBuiltinCall, encodeEvents
      ])
  | `(tactic| semantic_bridge_simp [$[$extra:term],*]) =>
      `(tactic| simp [
        mkIRTransaction, mkIRState, interpretIR,
        execIRFunction, execIRStmts, execIRStmt,
        evalIRExpr, evalIRCall, evalIRExprs, IRState.getVar, IRState.setVar,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackend,
        Compiler.Proofs.YulGeneration.evalBuiltinCall, encodeEvents,
        $[$extra],*
      ])
  | `(tactic| semantic_bridge_split $h:ident : $cond:term with [$[$extra:term],*]) =>
      `(tactic|
        by_cases $h : $cond
        · semantic_bridge_simp [$[$extra],*, $h]
        · semantic_bridge_simp [$[$extra],*, $h])
  | `(tactic| semantic_bridge_owner $h:ident with [$[$extra:term],*]) =>
      `(tactic|
        subst $h
        semantic_bridge_simp [$[$extra],*])

/-! ## State Encoding

The canonical encoding from EDSL ContractState to IR-level Nat storage.
This must be consistent with the encoding used in PrimitiveBridge.lean.

Note: `slot` and `storage` are syntax keywords introduced by `Verity.Macro.Syntax`
(transitively imported via `Compiler.Specs`). French quotes `«»` are used to escape
these identifiers where they appear as variable names or struct field names.
-/

/-- Encode EDSL storage (Uint256 at each slot) as Nat storage for IR. -/
def encodeStorage (state : ContractState) : Nat → Nat :=
  fun «slot» => (state.storage «slot»).val

/-- Encode EDSL sender (Address) as Nat for IR. -/
def encodeSender (state : ContractState) : Nat :=
  state.sender.val

/-- Encode an EDSL event as an IR-level flat log payload. -/
def encodeEvent (ev : Event) : List Nat :=
  (ev.name.toList.map Char.toNat) ++
    (0 :: (ev.args.map (fun arg => arg.val))) ++
    (0 :: (ev.indexedArgs.map (fun arg => arg.val)))

/-- Encode the full append-only EDSL event log for IR-level comparison. -/
def encodeEvents (events : List Event) : List (List Nat) :=
  events.map encodeEvent

/-- Shared constructor for IR transactions used in semantic-bridge statements. -/
def mkIRTransaction (sender : Address) (selector : Nat) (args : List Nat) : IRTransaction := {
  sender := sender.val
  functionSelector := selector
  args := args
}

/-- Shared constructor for IR state fixtures used in semantic-bridge statements. -/
def mkIRState
    (state : ContractState)
    (sender : Address)
    (selector : Nat)
    (calldata : List Nat)
    (encodeStorageFn : ContractState → Nat → Nat) : IRState := {
  vars := []
  «storage» := encodeStorageFn state
  memory := fun _ => 0
  calldata := calldata
  returnValue := none
  sender := sender.val
  selector := selector
  events := encodeEvents state.events
}

/-! ## Layer 2 Generic Theorem Spine -/

/-- Generic Layer-2 bridge theorem: once a contract-specific postcondition is
established for the compiled IR contract, the same postcondition is available
through the `compile` entrypoint for all states and senders. This enforces the
universal quantification shape at Layer 2 and avoids fixed test fixtures. -/
theorem spec_to_ir_preserves_semantics
    {α : Type}
    (spec : CompilationModel.CompilationModel)
    (selectors : List Nat)
    (compiled : IRContract)
    (runSpec : ContractState → Address → α)
    (mkTx : Address → IRTransaction)
    (mkIRState : ContractState → Address → IRState)
    (post : α → IRResult → Prop)
    (hcompile : CompilationModel.compile spec selectors = Except.ok compiled)
    (hpost : ∀ (state : ContractState) (sender : Address),
      post (runSpec state sender)
        (interpretIR compiled (mkTx sender) (mkIRState state sender))) :
    ∀ (state : ContractState) (sender : Address),
      let compiledResult := CompilationModel.compile spec selectors
      match compiledResult with
      | Except.ok irContract =>
          post (runSpec state sender)
            (interpretIR irContract (mkTx sender) (mkIRState state sender))
      | Except.error _ => False := by
  intro state sender
  simpa [hcompile] using hpost state sender

/-! ## Target Theorems: SimpleStorage -/

set_option maxHeartbeats 1200000000 in
theorem simpleStorage_store_semantic_bridge
    (state : ContractState) (sender : Address) (value : Uint256) :
    let edslResult := Contract.run (Contracts.MacroContracts.SimpleStorage.store value)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0x6057361d [value.val]
    let irState := mkIRState state sender 0x6057361d [value.val] encodeStorage
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_simp [Contract.run, Contracts.MacroContracts.SimpleStorage.store,
    Contracts.MacroContracts.SimpleStorage.storedData, setStorage,
    simpleStorageIRContract, encodeStorage]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hmod : value.val % Compiler.Constants.evmModulus = value.val := by
      simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using
        (Nat.mod_eq_of_lt value.isLt)
    simpa [Contracts.MacroContracts.SimpleStorage.storedData] using hmod.symm
  · simp [Contracts.MacroContracts.SimpleStorage.storedData, hx]

set_option maxHeartbeats 1200000000 in
theorem simpleStorage_retrieve_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run Contracts.MacroContracts.SimpleStorage.retrieve
      { state with sender := sender }
    let tx := mkIRTransaction sender 0x2e64cec1 []
    let irState := mkIRState state sender 0x2e64cec1 [] encodeStorage
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_simp [Contract.run, Contracts.MacroContracts.SimpleStorage.retrieve,
    Contracts.MacroContracts.SimpleStorage.storedData, simpleStorageIRContract, encodeStorage]

/-! ## Target Theorems: Counter -/

theorem counter_increment_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.MacroContracts.Counter.increment) { state with sender := sender }
    let tx := mkIRTransaction sender 0xd09de08a []
    let irState := mkIRState state sender 0xd09de08a [] encodeStorage
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_simp [Contract.run, Contracts.MacroContracts.Counter.increment,
    Contracts.MacroContracts.Counter.count, getStorage, setStorage, add,
    counterIRContract, encodeStorage]

theorem counter_decrement_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.MacroContracts.Counter.decrement)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0x2baeceb7 []
    let irState := mkIRState state sender 0x2baeceb7 [] encodeStorage
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_simp [Contract.run, Contracts.MacroContracts.Counter.decrement,
    Contracts.MacroContracts.Counter.count, getStorage, setStorage, sub,
    counterIRContract, encodeStorage]

theorem counter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.MacroContracts.Counter.getCount)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0xa87d942c []
    let irState := mkIRState state sender 0xa87d942c [] encodeStorage
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_simp [Contract.run, Contracts.MacroContracts.Counter.getCount,
    Contracts.MacroContracts.Counter.count, getStorage, counterIRContract, encodeStorage]

/-! ## Target Theorems: Owned -/

/-- Encode EDSL Address storage as Nat storage for IR. -/
def encodeStorageAddr (state : ContractState) : Nat → Nat :=
  fun «slot» => (state.storageAddr «slot»).val

theorem owned_getOwner_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.MacroContracts.Owned.getOwner) { state with sender := sender }
    let tx := mkIRTransaction sender 0x893d20e8 []
    let irState := mkIRState state sender 0x893d20e8 [] encodeStorageAddr
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR ownedIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storageAddr «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_simp [Contract.run, Contracts.MacroContracts.Owned.getOwner,
    getStorageAddr, ownedIRContract, encodeStorageAddr]

theorem owned_transferOwnership_semantic_bridge
    (state : ContractState) (sender : Address) (newOwner : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Contracts.MacroContracts.Owned.transferOwnership newOwner)
        { state with sender := sender }
    let tx := mkIRTransaction sender 0xf2fde38b [newOwner.val]
    let irState := mkIRState state sender 0xf2fde38b [newOwner.val] encodeStorageAddr
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storageAddr «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_owner hOwner with [Contract.run, Contracts.MacroContracts.Owned.transferOwnership,
    Contracts.MacroContracts.Owned.owner, getStorageAddr, setStorageAddr,
    ownedIRContract, encodeStorageAddr]

/-! ## Target Theorems: SafeCounter -/

theorem safeCounter_increment_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.MacroContracts.SafeCounter.increment)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0xd09de08a []
    let irState := mkIRState state sender 0xd09de08a [] encodeStorage
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = false
    := by
  semantic_bridge_split hOverflow : state.storage 0 = (Uint256.max) with
    [Contract.run, Contracts.MacroContracts.SafeCounter.increment,
    Contracts.MacroContracts.SafeCounter.count, getStorage, setStorage,
    requireSomeUint, safeAdd, Uint256.max, safeCounterIRContract, encodeStorage]

theorem safeCounter_decrement_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.MacroContracts.SafeCounter.decrement)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0x2baeceb7 []
    let irState := mkIRState state sender 0x2baeceb7 [] encodeStorage
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = false
    := by
  semantic_bridge_split hUnderflow : state.storage 0 = 0 with
    [Contract.run, Contracts.MacroContracts.SafeCounter.decrement,
    Contracts.MacroContracts.SafeCounter.count, getStorage, setStorage,
    requireSomeUint, safeSub, safeCounterIRContract, encodeStorage]

theorem safeCounter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.MacroContracts.SafeCounter.getCount)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0xa87d942c []
    let irState := mkIRState state sender 0xa87d942c [] encodeStorage
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_simp [Contract.run, Contracts.MacroContracts.SafeCounter.getCount,
    Contracts.MacroContracts.SafeCounter.count, getStorage,
    safeCounterIRContract, encodeStorage]

/-! ## Target Theorems: OwnedCounter -/

/-- Encode OwnedCounter storage: slot 0 = owner (Address), slot 1 = count (Uint256). -/
def encodeOwnedCounterStorage (state : ContractState) : Nat → Nat :=
  fun «slot» =>
    if «slot» = 0 then (state.storageAddr 0).val
    else (state.storage «slot»).val

theorem ownedCounter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.MacroContracts.OwnedCounter.getCount)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0xa87d942c []
    let irState := mkIRState state sender 0xa87d942c [] encodeOwnedCounterStorage
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_simp [Contract.run, Contracts.MacroContracts.OwnedCounter.getCount,
    Contracts.MacroContracts.OwnedCounter.count, getStorage,
    ownedCounterIRContract, encodeOwnedCounterStorage]

theorem ownedCounter_getOwner_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.MacroContracts.OwnedCounter.getOwner)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0x893d20e8 []
    let irState := mkIRState state sender 0x893d20e8 [] encodeOwnedCounterStorage
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_simp [Contract.run, Contracts.MacroContracts.OwnedCounter.getOwner,
    Contracts.MacroContracts.OwnedCounter.owner, getStorageAddr,
    ownedCounterIRContract, encodeOwnedCounterStorage]

theorem ownedCounter_increment_semantic_bridge
    (state : ContractState) (sender : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Contracts.MacroContracts.OwnedCounter.increment)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0xd09de08a []
    let irState := mkIRState state sender 0xd09de08a [] encodeOwnedCounterStorage
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_owner hOwner with [Contract.run, Contracts.MacroContracts.OwnedCounter.increment,
    Contracts.MacroContracts.OwnedCounter.owner, Contracts.MacroContracts.OwnedCounter.count,
    getStorageAddr, getStorage, setStorage,
    ownedCounterIRContract, encodeOwnedCounterStorage]

theorem ownedCounter_decrement_semantic_bridge
    (state : ContractState) (sender : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Contracts.MacroContracts.OwnedCounter.decrement)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0x2baeceb7 []
    let irState := mkIRState state sender 0x2baeceb7 [] encodeOwnedCounterStorage
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_owner hOwner with [Contract.run, Contracts.MacroContracts.OwnedCounter.decrement,
    Contracts.MacroContracts.OwnedCounter.owner, Contracts.MacroContracts.OwnedCounter.count,
    getStorageAddr, getStorage, setStorage,
    ownedCounterIRContract, encodeOwnedCounterStorage]

theorem ownedCounter_transferOwnership_semantic_bridge
    (state : ContractState) (sender : Address) (newOwner : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Contracts.MacroContracts.OwnedCounter.transferOwnership newOwner)
        { state with sender := sender }
    let tx := mkIRTransaction sender 0xf2fde38b [newOwner.val]
    let irState := mkIRState state sender 0xf2fde38b [newOwner.val] encodeOwnedCounterStorage
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by
  semantic_bridge_owner hOwner with [Contract.run, Contracts.MacroContracts.OwnedCounter.transferOwnership,
    Contracts.MacroContracts.OwnedCounter.owner, getStorageAddr, setStorageAddr,
    ownedCounterIRContract, encodeOwnedCounterStorage]

/-! ## Composed End-to-End: EDSL → IR → Yul -/

theorem simpleStorage_store_edsl_to_yul
    (state : ContractState) (sender : Address) (value : Uint256) :
    let edslResult := Contract.run (Contracts.MacroContracts.SimpleStorage.store value)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0x6057361d [value.val]
    let irState := mkIRState state sender 0x6057361d [value.val] encodeStorage
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        (∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot») ∧
        encodeEvents s'.events = irResult.events ∧
        Compiler.Proofs.YulGeneration.resultsMatch (interpretIR simpleStorageIRContract tx irState)
          (interpretYulFromIR simpleStorageIRContract tx irState)
    | .revert _ _ => True
    := by
  let tx := mkIRTransaction sender 0x6057361d [value.val]
  let irState := mkIRState state sender 0x6057361d [value.val] encodeStorage
  have hBridge := simpleStorage_store_semantic_bridge state sender value
  have hYul : resultsMatch (interpretIR simpleStorageIRContract tx irState) (interpretYulFromIR simpleStorageIRContract tx irState) := by
    refine Compiler.Proofs.EndToEnd.layer3_contract_preserves_semantics_general
      simpleStorageIRContract tx irState ?_ ?_ rfl rfl ?_
    · simp [tx, mkIRTransaction, selectorModulus]
    · intro s hs; simp [simpleStorageIRContract] at hs
    · intro fn hfn
      simp [simpleStorageIRContract] at hfn
      rcases hfn with hfn | hfn
      all_goals
        subst hfn
        simpa [Compiler.Proofs.EndToEnd.layer3_function_preserves_semantics,
          tx, irState, mkIRTransaction, mkIRState, encodeStorage,
          interpretYulBodyFromState, interpretYulBody, yulStateOfIR,
          yulResultOfExecWithRollback, interpretYulRuntime, execYulStmts]
  cases hrun : Contract.run (Contracts.MacroContracts.SimpleStorage.store value)
      { state with sender := sender } with
  | success _ s' =>
      have hA : (let tx := mkIRTransaction sender 0x6057361d [value.val]
          let irState := mkIRState state sender 0x6057361d [value.val] encodeStorage
          let irResult := interpretIR simpleStorageIRContract tx irState
          irResult.success = true ∧
          (∀ slot, (s'.storage slot).val = irResult.finalStorage slot) ∧
          encodeEvents s'.events = irResult.events) := by
        simpa [hrun] using hBridge
      rcases hA with ⟨hs, hst, he⟩
      simpa [tx, irState, hrun] using And.intro hs (And.intro hst (And.intro he hYul))
  | revert _ _ => simp [hrun]

theorem simpleStorage_retrieve_edsl_to_yul
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run Contracts.MacroContracts.SimpleStorage.retrieve
      { state with sender := sender }
    let tx := mkIRTransaction sender 0x2e64cec1 []
    let irState := mkIRState state sender 0x2e64cec1 [] encodeStorage
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        (∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot») ∧
        encodeEvents s'.events = irResult.events ∧
        Compiler.Proofs.YulGeneration.resultsMatch
          (interpretIR simpleStorageIRContract tx irState)
          (interpretYulFromIR simpleStorageIRContract tx irState)
    | .revert _ _ => True
    := by
  let tx := mkIRTransaction sender 0x2e64cec1 []
  let irState := mkIRState state sender 0x2e64cec1 [] encodeStorage
  have hBridge := simpleStorage_retrieve_semantic_bridge state sender
  have hYul : resultsMatch (interpretIR simpleStorageIRContract tx irState)
      (interpretYulFromIR simpleStorageIRContract tx irState) := by
    refine Compiler.Proofs.EndToEnd.layer3_contract_preserves_semantics_general
      simpleStorageIRContract tx irState ?_ ?_ rfl rfl ?_
    · simp [tx, mkIRTransaction, selectorModulus]
    · intro s hs; simp [simpleStorageIRContract] at hs
    · intro fn hfn
      simp [simpleStorageIRContract] at hfn
      rcases hfn with hfn | hfn
      all_goals
        subst hfn
        simpa [Compiler.Proofs.EndToEnd.layer3_function_preserves_semantics,
          tx, irState, mkIRTransaction, mkIRState, encodeStorage,
          interpretYulBodyFromState, interpretYulBody, yulStateOfIR,
          yulResultOfExecWithRollback, interpretYulRuntime, execYulStmts]
  cases hrun : Contract.run Contracts.MacroContracts.SimpleStorage.retrieve { state with sender := sender } with
  | success val s' =>
      have hA : (let tx := mkIRTransaction sender 0x2e64cec1 []
          let irState := mkIRState state sender 0x2e64cec1 [] encodeStorage
          let irResult := interpretIR simpleStorageIRContract tx irState
          irResult.success = true ∧
          irResult.returnValue = some val.val ∧
          (∀ slot, (s'.storage slot).val = irResult.finalStorage slot) ∧
          encodeEvents s'.events = irResult.events) := by
        simpa [hrun] using hBridge
      rcases hA with ⟨hs, hret, hst, he⟩
      simpa [tx, irState, hrun] using And.intro hs (And.intro hret (And.intro hst (And.intro he hYul)))
  | revert _ _ =>
      simp [hrun]

theorem counter_increment_edsl_to_yul
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.MacroContracts.Counter.increment)
      { state with sender := sender }
    let tx := mkIRTransaction sender 0xd09de08a []
    let irState := mkIRState state sender 0xd09de08a [] encodeStorage
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        (∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot») ∧
        encodeEvents s'.events = irResult.events ∧
        Compiler.Proofs.YulGeneration.resultsMatch
          (interpretIR counterIRContract tx irState)
          (interpretYulFromIR counterIRContract tx irState)
    | .revert _ _ => True
    := by
  let tx := mkIRTransaction sender 0xd09de08a []
  let irState := mkIRState state sender 0xd09de08a [] encodeStorage
  have hBridge := counter_increment_semantic_bridge state sender
  have hYul : resultsMatch (interpretIR counterIRContract tx irState)
      (interpretYulFromIR counterIRContract tx irState) := by
    refine Compiler.Proofs.EndToEnd.layer3_contract_preserves_semantics_general
      counterIRContract tx irState ?_ ?_ rfl rfl ?_
    · simp [tx, mkIRTransaction, selectorModulus]
    · intro s hs; simp [counterIRContract] at hs
    · intro fn hfn
      simp [counterIRContract] at hfn
      rcases hfn with hfn | hfn | hfn
      all_goals
        subst hfn
        simpa [Compiler.Proofs.EndToEnd.layer3_function_preserves_semantics,
          tx, irState, mkIRTransaction, mkIRState, encodeStorage,
          interpretYulBodyFromState, interpretYulBody, yulStateOfIR,
          yulResultOfExecWithRollback, interpretYulRuntime, execYulStmts]
  cases hrun : Contract.run (Contracts.MacroContracts.Counter.increment)
      { state with sender := sender } with
  | success _ s' =>
      have hA : (let tx := mkIRTransaction sender 0xd09de08a []
          let irState := mkIRState state sender 0xd09de08a [] encodeStorage
          let irResult := interpretIR counterIRContract tx irState
          irResult.success = true ∧
          (∀ slot, (s'.storage slot).val = irResult.finalStorage slot) ∧
          encodeEvents s'.events = irResult.events) := by
        simpa [hrun] using hBridge
      rcases hA with ⟨hs, hst, he⟩
      simpa [tx, irState, hrun] using And.intro hs (And.intro hst (And.intro he hYul))
  | revert _ _ =>
      simp [hrun]

end Compiler.Proofs.SemanticBridge
