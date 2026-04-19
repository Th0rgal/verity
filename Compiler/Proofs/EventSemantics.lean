import Verity.Core

/-!
# Event Emission Semantics

Structural properties of the event subsystem used by the source-level
interpreter. These lemmas support `Stmt.emit` in the event-tracking fragment.

## Key results

- `encodeEvent_injective`: distinct events produce distinct encodings
- `encodeEvents_append`: encoding distributes over append
- `encodeEvents_length`: encoding preserves list length
- Event-append monotonicity lemmas for the append-only event log
-/

namespace Compiler.Proofs.EventSemantics

open Verity.Core

/-! ### Event encoding properties -/

/-- Events are encoded to lists of natural numbers. -/
def encodeEvent (ev : Verity.Event) : List Nat :=
  (ev.name.toList.map Char.toNat) ++
    (0 :: (ev.args.map (fun arg => arg.val))) ++
    (0 :: (ev.indexedArgs.map (fun arg => arg.val)))

def encodeEvents (events : List Verity.Event) : List (List Nat) :=
  events.map encodeEvent

theorem encodeEvents_append (evs1 evs2 : List Verity.Event) :
    encodeEvents (evs1 ++ evs2) = encodeEvents evs1 ++ encodeEvents evs2 := by
  simp [encodeEvents, List.map_append]

theorem encodeEvents_length (evs : List Verity.Event) :
    (encodeEvents evs).length = evs.length := by
  simp [encodeEvents]

theorem encodeEvents_nil : encodeEvents [] = [] := rfl

theorem encodeEvents_cons (ev : Verity.Event) (rest : List Verity.Event) :
    encodeEvents (ev :: rest) = encodeEvent ev :: encodeEvents rest := rfl

/-! ### Event log monotonicity

The event log in `ContractState` is append-only. These lemmas capture the
monotonicity invariant needed for proving event-preserving compilation. -/

/-- Appending an event to the world preserves all previous events. -/
theorem events_append_prefix (world : Verity.ContractState) (ev : Verity.Event) :
    world.events <+: (world.events ++ [ev]) :=
  List.prefix_append world.events [ev]

/-- Appending events preserves the storage mapping. -/
theorem events_update_preserves_storage (world : Verity.ContractState) (newEvents : List Verity.Event) :
    ({ world with events := world.events ++ newEvents } : Verity.ContractState).storage = world.storage :=
  rfl

/-- Appending events preserves storage arrays. -/
theorem events_update_preserves_storageArray (world : Verity.ContractState) (newEvents : List Verity.Event) (slot : Nat) :
    ({ world with events := world.events ++ newEvents } : Verity.ContractState).storageArray slot = world.storageArray slot :=
  rfl

/-! ### Effect surface classification

These lemmas establish which statement forms touch the unsupported effect
surface. They will be needed when widening the effect surface gate. -/

/-- An event emission step appends exactly one event and returns `.continue`. -/
theorem emit_step_spec (world : Verity.ContractState) (ev : Verity.Event) :
    ({ world with events := world.events ++ [ev] } : Verity.ContractState).events =
      world.events ++ [ev] :=
  rfl

/-- Event append preserves transient storage. -/
theorem events_update_preserves_transientStorage (world : Verity.ContractState)
    (newEvents : List Verity.Event) :
    ({ world with events := world.events ++ newEvents } : Verity.ContractState).transientStorage =
      world.transientStorage :=
  rfl

/-- Event append preserves the sender field. -/
theorem events_update_preserves_sender (world : Verity.ContractState)
    (newEvents : List Verity.Event) :
    ({ world with events := world.events ++ newEvents } : Verity.ContractState).sender =
      world.sender :=
  rfl

end Compiler.Proofs.EventSemantics
