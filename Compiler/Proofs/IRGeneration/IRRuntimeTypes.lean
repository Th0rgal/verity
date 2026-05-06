import Compiler.Proofs.IRGeneration.IRStorageWord

namespace Compiler.Proofs.IRGeneration

/-- Proof-side execution state shared by IR semantics and native-runtime harnesses. -/
structure IRState where
  /-- Variable bindings (name -> value). -/
  vars : List (String × Nat)
  /-- Storage slots (slot -> value).

      Typed via `IRStorageWord` so the proof surface tracks the bounded EVM
      storage carrier. -/
  storage : IRStorageSlot → IRStorageWord
  /-- Transient storage slots (slot -> value). -/
  transientStorage : Nat → Nat := fun _ => 0
  /-- Memory words (offset -> value). -/
  memory : Nat → Nat
  /-- Calldata words. -/
  calldata : List Nat
  /-- Return value, if any. -/
  returnValue : Option Nat
  /-- Sender address. -/
  sender : Nat
  /-- Msg.value seen by `callvalue()`. -/
  msgValue : Nat := 0
  /-- Contract address seen by `address()`. -/
  thisAddress : Nat := 0
  /-- Block timestamp seen by `timestamp()`. -/
  blockTimestamp : Nat := 0
  /-- Block number seen by `number()`. -/
  blockNumber : Nat := 0
  /-- Chain id seen by `chainid()`. -/
  chainId : Nat := 0
  /-- Blob base fee seen by `blobbasefee()`. -/
  blobBaseFee : Nat := 0
  /-- Function selector. -/
  selector : Nat
  /-- Emitted log records for this execution. -/
  events : List (List Nat) := []
  deriving Nonempty

/-- Initial state for IR execution. -/
def IRState.initial (sender : Nat) : IRState :=
  { vars := []
    storage := fun _ => 0
    transientStorage := fun _ => 0
    memory := fun _ => 0
    calldata := []
    returnValue := none
    sender := sender
    msgValue := 0
    thisAddress := 0
    blockTimestamp := 0
    blockNumber := 0
    chainId := 0
    blobBaseFee := 0
    selector := 0
    events := [] }

/-- Lookup variable in state. -/
def IRState.getVar (s : IRState) (name : String) : Option Nat :=
  s.vars.find? (·.1 == name) |>.map (·.2)

/-- Set variable in state. -/
def IRState.setVar (s : IRState) (name : String) (value : Nat) : IRState :=
  { s with vars := (name, value) :: s.vars.filter (·.1 != name) }

/-- Set several variables in order, matching left-to-right binding behavior. -/
def IRState.setVars (s : IRState) (bindings : List (String × Nat)) : IRState :=
  bindings.foldl (fun st (name, value) => st.setVar name value) s

/-- Proof-side transaction context shared by IR and native-runtime harnesses. -/
structure IRTransaction where
  sender : Nat
  msgValue : Nat := 0
  thisAddress : Nat := 0
  blockTimestamp : Nat := 0
  blockNumber : Nat := 0
  chainId : Nat := 0
  blobBaseFee : Nat := 0
  functionSelector : Nat
  args : List Nat
  deriving Repr

/-- Proof-side observable execution result shared by IR and native-runtime harnesses. -/
structure IRResult where
  success : Bool
  returnValue : Option Nat
  finalStorage : IRStorageSlot → IRStorageWord
  finalMappings : Nat → Nat → IRStorageWord
  events : List (List Nat)

end Compiler.Proofs.IRGeneration
