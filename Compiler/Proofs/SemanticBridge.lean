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
import Verity.Examples.SimpleStorage
import Verity.Examples.Counter
import Verity.Examples.Owned
import Verity.Examples.SafeCounter
import Verity.Examples.OwnedCounter

namespace Compiler.Proofs.SemanticBridge

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Verity
open Verity.Core.Uint256

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

theorem simpleStorage_store_semantic_bridge
    (state : ContractState) (sender : Address) (value : Uint256) :
    let edslResult := Contract.run (Verity.Examples.store value) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x6057361d
      args := [value.val]
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := [value.val]
      returnValue := none
      sender := sender.val
      selector := 0x6057361d
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by sorry

theorem simpleStorage_retrieve_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.retrieve) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2e64cec1
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2e64cec1
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by sorry

/-! ## Target Theorems: Counter -/

theorem counter_increment_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by sorry

theorem counter_decrement_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.decrement) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2baeceb7
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2baeceb7
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by sorry

theorem counter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.getCount) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xa87d942c
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xa87d942c
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by sorry

/-! ## Target Theorems: Owned -/

/-- Encode EDSL Address storage as Nat storage for IR. -/
def encodeStorageAddr (state : ContractState) : Nat → Nat :=
  fun «slot» => (state.storageAddr «slot»).val

theorem owned_getOwner_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Owned.getOwner) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x893d20e8
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorageAddr state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x893d20e8
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR ownedIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storageAddr «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by sorry

theorem owned_transferOwnership_semantic_bridge
    (state : ContractState) (sender : Address) (newOwner : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.Owned.transferOwnership newOwner)
        { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xf2fde38b
      args := [newOwner.val]
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorageAddr state
      memory := fun _ => 0
      calldata := [newOwner.val]
      returnValue := none
      sender := sender.val
      selector := 0xf2fde38b
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storageAddr «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by sorry

/-! ## Target Theorems: SafeCounter -/

theorem safeCounter_increment_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.SafeCounter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
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
    := by sorry

theorem safeCounter_decrement_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.SafeCounter.decrement) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2baeceb7
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2baeceb7
    }
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
    := by sorry

theorem safeCounter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.SafeCounter.getCount) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xa87d942c
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xa87d942c
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by sorry

/-! ## Target Theorems: OwnedCounter -/

/-- Encode OwnedCounter storage: slot 0 = owner (Address), slot 1 = count (Uint256). -/
def encodeOwnedCounterStorage (state : ContractState) : Nat → Nat :=
  fun «slot» =>
    if «slot» = 0 then (state.storageAddr 0).val
    else (state.storage «slot»).val

theorem ownedCounter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.getCount) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xa87d942c
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xa87d942c
    }
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
    := by sorry

theorem ownedCounter_getOwner_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.getOwner) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x893d20e8
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x893d20e8
    }
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
    := by sorry

theorem ownedCounter_increment_semantic_bridge
    (state : ContractState) (sender : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by sorry

theorem ownedCounter_decrement_semantic_bridge
    (state : ContractState) (sender : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.decrement) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2baeceb7
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2baeceb7
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by sorry

theorem ownedCounter_transferOwnership_semantic_bridge
    (state : ContractState) (sender : Address) (newOwner : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.transferOwnership newOwner)
        { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xf2fde38b
      args := [newOwner.val]
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := [newOwner.val]
      returnValue := none
      sender := sender.val
      selector := 0xf2fde38b
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
        ∧
        encodeEvents s'.events = irResult.events
    | .revert _ _ => True
    := by sorry

/-! ## Composed End-to-End: EDSL → IR → Yul -/

theorem simpleStorage_store_edsl_to_yul
    (state : ContractState) (sender : Address) (value : Uint256) :
    let edslResult := Contract.run (Verity.Examples.store value) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x6057361d
      args := [value.val]
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := [value.val]
      returnValue := none
      sender := sender.val
      selector := 0x6057361d
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        (∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot») ∧
        encodeEvents s'.events = irResult.events ∧
        Compiler.Proofs.YulGeneration.resultsMatch
          (interpretIR simpleStorageIRContract tx irState)
          (interpretYulFromIR simpleStorageIRContract tx irState)
    | .revert _ _ => True
    := by sorry

theorem simpleStorage_retrieve_edsl_to_yul
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.retrieve) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2e64cec1
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2e64cec1
    }
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
    := by sorry

theorem counter_increment_edsl_to_yul
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
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
    := by sorry

end Compiler.Proofs.SemanticBridge
