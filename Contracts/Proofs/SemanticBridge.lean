/- 
  Contracts.Proofs.SemanticBridge: Full EDSL ≡ Compiled IR theorem statements

  This file states the *target* theorem per contract function: that EDSL execution
  produces the same storage effects as compiling the CompilationModel spec and
  interpreting the resulting IR.

  Unlike the macro-generated `_semantic_preservation` theorems (which live in the
  contract namespace and cannot import IR types), these theorems import the full
  IR execution machinery and state the precise equivalence:

    ∀ slot, (edslFinalState.storage slot).val = irResult.finalStorage slot

  **Status**: This file is the contract-specific Layer 2 client/example layer.
  The bridge theorems below are intentionally concrete per contract function:
  they demonstrate how to connect EDSL execution, compiled IR execution, and
  Layer 3 preservation. This is not the source of generic compiler correctness
  for `CompilationModel.compile`. The generic Layer 2 theorem now lives under
  `Compiler/Proofs/IRGeneration/Contract.lean`.

  **Why a separate file**: The macro-generated theorems cannot import
  `Compiler.Proofs.IRGeneration.IRInterpreter` (it would transitively pull
  in EVMYulLean and bloat every contract file). This file bridges the gap by
  importing both the EDSL types and the IR execution types, stating the
  theorems that directly reference `interpretIR`.

  Run: lake build Contracts.Proofs.SemanticBridge
-/

import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.EndToEnd
import Contracts.Specs
import Verity.Core
import Contracts
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

/-- `semantic_bridge_layer3 contract tx irState` opens the standard Layer-3
    contract-preservation scaffold used by composed EDSL->IR->Yul bridge proofs. -/
syntax (name := semantic_bridge_layer3)
  "semantic_bridge_layer3 " term " " term " " term : tactic

/-- `semantic_bridge_fn_cases [h1, ...] with [...]` discharges the per-function
    case split after `simp [contract] at hfn`, using the canonical Layer-3 body
    equivalence rewrite bundle plus local extras. -/
syntax (name := semantic_bridge_fn_cases)
  "semantic_bridge_fn_cases [" ident,* "] with [" term,* "]" : tactic

/-- `semantic_bridge_layer3_cases contract tx irState [h1, ...] with [...]`
    composes the standard Layer-3 scaffold and per-function case discharge. -/
syntax (name := semantic_bridge_layer3_cases)
  "semantic_bridge_layer3_cases " term " " term " " term
    " [" ident,* "] with [" term,* "]" : tactic

/-- `semantic_bridge_have h := t with [...]` introduces `h` by normalizing
    `t` with a local simp bundle (used to rewrite bridge theorems to local
    `let`-bound fixtures). -/
syntax (name := semantic_bridge_have)
  "semantic_bridge_have " ident " := " term " with [" term,* "]" : tactic

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
  | `(tactic| semantic_bridge_layer3 $contract:term $tx:term $irState:term) =>
      `(tactic|
        refine Compiler.Proofs.EndToEnd.layer3_contract_preserves_semantics_general
          $contract $tx $irState ?_ ?_ rfl rfl ?_
        · simp [$tx, mkIRTransaction, selectorModulus]
        · intro s hs
          simp [$contract] at hs
        · intro fn hfn
          simp [$contract] at hfn)
  | `(tactic| semantic_bridge_fn_cases [$[$h:ident],*] with [$[$extra:term],*]) =>
      `(tactic|
        rcases hfn with $[$h]|*
        all_goals
          subst hfn
          simpa [Compiler.Proofs.EndToEnd.layer3_function_preserves_semantics,
            tx, irState, mkIRTransaction, mkIRState,
            interpretYulBodyFromState, interpretYulBody, yulStateOfIR,
            yulResultOfExecWithRollback, interpretYulRuntime, execYulStmts,
            $[$extra],*])
  | `(tactic| semantic_bridge_layer3_cases $contract:term $tx:term $irState:term
      [$[$h:ident],*] with [$[$extra:term],*]) =>
      `(tactic|
        semantic_bridge_layer3 $contract $tx $irState
        semantic_bridge_fn_cases [$[$h],*] with [$[$extra],*])
  | `(tactic| semantic_bridge_have $hnew:ident := $hsrc:term with [$[$extra:term],*]) =>
      `(tactic|
        have $hnew := by
          simpa [$[$extra],*] using $hsrc)

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

/-! ## Layer 2 Wrapper Theorem -/

/-- Wrapper theorem for the current contract-specific Layer 2 bridge style.

This is a legacy/example wrapper theorem around the generic compiler proof
surface. It only says that once a caller already has a contract-specific
postcondition for the compiled IR contract, that same postcondition can be
transported through the `compile` entrypoint for all states and senders. -/
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
    let edslResult := Contract.run (Contracts.SimpleStorage.store value)
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
  semantic_bridge_simp [Contract.run, Contracts.SimpleStorage.store,
    Contracts.SimpleStorage.storedData, setStorage,
    simpleStorageIRContract, encodeStorage]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hmod : value.val % Compiler.Constants.evmModulus = value.val := by
      simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using
        (Nat.mod_eq_of_lt value.isLt)
    simpa [Contracts.SimpleStorage.storedData] using hmod.symm
  · simp [Contracts.SimpleStorage.storedData, hx]

set_option maxHeartbeats 1200000000 in
theorem simpleStorage_retrieve_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run Contracts.SimpleStorage.retrieve
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
  semantic_bridge_simp [Contract.run, Contracts.SimpleStorage.retrieve,
    Contracts.SimpleStorage.storedData, simpleStorageIRContract, encodeStorage]

/-! ## Target Theorems: Counter -/

theorem counter_increment_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.Counter.increment) { state with sender := sender }
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
  semantic_bridge_simp [Contract.run, Contracts.Counter.increment,
    Contracts.Counter.count, getStorage, setStorage, add,
    counterIRContract, encodeStorage]

theorem counter_decrement_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.Counter.decrement)
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
  semantic_bridge_simp [Contract.run, Contracts.Counter.decrement,
    Contracts.Counter.count, getStorage, setStorage, sub,
    counterIRContract, encodeStorage]

theorem counter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.Counter.getCount)
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
  semantic_bridge_simp [Contract.run, Contracts.Counter.getCount,
    Contracts.Counter.count, getStorage, counterIRContract, encodeStorage]

/-! ## Target Theorems: Owned -/

/-- Encode EDSL Address storage as Nat storage for IR. -/
def encodeStorageAddr (state : ContractState) : Nat → Nat :=
  fun «slot» => (state.storageAddr «slot»).val

theorem owned_getOwner_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.Owned.getOwner) { state with sender := sender }
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
  semantic_bridge_simp [Contract.run, Contracts.Owned.getOwner,
    getStorageAddr, ownedIRContract, encodeStorageAddr]

theorem owned_transferOwnership_semantic_bridge
    (state : ContractState) (sender : Address) (newOwner : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Contracts.Owned.transferOwnership newOwner)
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
  semantic_bridge_owner hOwner with [Contract.run, Contracts.Owned.transferOwnership,
    Contracts.Owned.owner, getStorageAddr, setStorageAddr,
    ownedIRContract, encodeStorageAddr]

/-! ## Target Theorems: SafeCounter -/

theorem safeCounter_increment_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.SafeCounter.increment)
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
    [Contract.run, Contracts.SafeCounter.increment,
    Contracts.SafeCounter.count, getStorage, setStorage,
    requireSomeUint, safeAdd, Uint256.max, safeCounterIRContract, encodeStorage]

theorem safeCounter_decrement_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.SafeCounter.decrement)
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
    [Contract.run, Contracts.SafeCounter.decrement,
    Contracts.SafeCounter.count, getStorage, setStorage,
    requireSomeUint, safeSub, safeCounterIRContract, encodeStorage]

theorem safeCounter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.SafeCounter.getCount)
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
  semantic_bridge_simp [Contract.run, Contracts.SafeCounter.getCount,
    Contracts.SafeCounter.count, getStorage,
    safeCounterIRContract, encodeStorage]

/-! ## Target Theorems: OwnedCounter -/

/-- Encode OwnedCounter storage: slot 0 = owner (Address), slot 1 = count (Uint256). -/
def encodeOwnedCounterStorage (state : ContractState) : Nat → Nat :=
  fun «slot» =>
    if «slot» = 0 then (state.storageAddr 0).val
    else (state.storage «slot»).val

theorem ownedCounter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.OwnedCounter.getCount)
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
  semantic_bridge_simp [Contract.run, Contracts.OwnedCounter.getCount,
    Contracts.OwnedCounter.count, getStorage,
    ownedCounterIRContract, encodeOwnedCounterStorage]

theorem ownedCounter_getOwner_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.OwnedCounter.getOwner)
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
  semantic_bridge_simp [Contract.run, Contracts.OwnedCounter.getOwner,
    Contracts.OwnedCounter.owner, getStorageAddr,
    ownedCounterIRContract, encodeOwnedCounterStorage]

theorem ownedCounter_increment_semantic_bridge
    (state : ContractState) (sender : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Contracts.OwnedCounter.increment)
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
  semantic_bridge_owner hOwner with [Contract.run, Contracts.OwnedCounter.increment,
    Contracts.OwnedCounter.owner, Contracts.OwnedCounter.count,
    getStorageAddr, getStorage, setStorage,
    ownedCounterIRContract, encodeOwnedCounterStorage]

theorem ownedCounter_decrement_semantic_bridge
    (state : ContractState) (sender : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Contracts.OwnedCounter.decrement)
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
  semantic_bridge_owner hOwner with [Contract.run, Contracts.OwnedCounter.decrement,
    Contracts.OwnedCounter.owner, Contracts.OwnedCounter.count,
    getStorageAddr, getStorage, setStorage,
    ownedCounterIRContract, encodeOwnedCounterStorage]

theorem ownedCounter_transferOwnership_semantic_bridge
    (state : ContractState) (sender : Address) (newOwner : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Contracts.OwnedCounter.transferOwnership newOwner)
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
  semantic_bridge_owner hOwner with [Contract.run, Contracts.OwnedCounter.transferOwnership,
    Contracts.OwnedCounter.owner, getStorageAddr, setStorageAddr,
    ownedCounterIRContract, encodeOwnedCounterStorage]

/-! ## Composed End-to-End: EDSL → IR → Yul -/

private theorem compose_semantic_bridge_with_yul
    {α : Type}
    (edslResult : ContractResult α)
    (P : α → ContractState → Prop)
    (hBridge : match edslResult with
      | .success val s' => P val s'
      | .revert _ _ => True)
    (hYul : Prop) :
    match edslResult with
    | .success val s' => P val s' ∧ hYul
    | .revert _ _ => True := by
  cases edslResult with
  | success val s' =>
      exact And.intro hBridge hYul
  | revert _ _ =>
      trivial

theorem simpleStorage_store_edsl_to_yul
    (state : ContractState) (sender : Address) (value : Uint256) :
    let edslResult := Contract.run (Contracts.SimpleStorage.store value)
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
  let edslResult := Contract.run (Contracts.SimpleStorage.store value)
    { state with sender := sender }
  have hBridge := simpleStorage_store_semantic_bridge state sender value
  have hYul : resultsMatch (interpretIR simpleStorageIRContract tx irState) (interpretYulFromIR simpleStorageIRContract tx irState) := by
    semantic_bridge_layer3_cases simpleStorageIRContract tx irState [hfn, hfn] with [encodeStorage]
  semantic_bridge_have hBridge' := hBridge with [edslResult, tx, irState]
  simpa [edslResult, tx, irState] using
    (compose_semantic_bridge_with_yul
      (edslResult := edslResult)
      (P := fun _ s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        (∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot») ∧
        encodeEvents s'.events = irResult.events)
      hBridge' hYul)

theorem simpleStorage_retrieve_edsl_to_yul
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run Contracts.SimpleStorage.retrieve
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
  let edslResult := Contract.run Contracts.SimpleStorage.retrieve
    { state with sender := sender }
  have hBridge := simpleStorage_retrieve_semantic_bridge state sender
  have hYul : resultsMatch (interpretIR simpleStorageIRContract tx irState)
      (interpretYulFromIR simpleStorageIRContract tx irState) := by
    semantic_bridge_layer3_cases simpleStorageIRContract tx irState [hfn, hfn] with [encodeStorage]
  semantic_bridge_have hBridge' := hBridge with [edslResult, tx, irState]
  simpa [edslResult, tx, irState] using
    (compose_semantic_bridge_with_yul
      (edslResult := edslResult)
      (P := fun val s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        (∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot») ∧
        encodeEvents s'.events = irResult.events)
      hBridge' hYul)

theorem counter_increment_edsl_to_yul
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Contracts.Counter.increment)
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
  let edslResult := Contract.run (Contracts.Counter.increment)
    { state with sender := sender }
  have hBridge := counter_increment_semantic_bridge state sender
  have hYul : resultsMatch (interpretIR counterIRContract tx irState)
      (interpretYulFromIR counterIRContract tx irState) := by
    semantic_bridge_layer3_cases counterIRContract tx irState [hfn, hfn, hfn] with [encodeStorage]
  semantic_bridge_have hBridge' := hBridge with [edslResult, tx, irState]
  simpa [edslResult, tx, irState] using
    (compose_semantic_bridge_with_yul
      (edslResult := edslResult)
      (P := fun _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        (∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot») ∧
        encodeEvents s'.events = irResult.events)
      hBridge' hYul)

end Compiler.Proofs.SemanticBridge
