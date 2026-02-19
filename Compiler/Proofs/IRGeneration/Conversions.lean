/-
  Type Conversions: Bridge between Spec and IR representations

  This module defines conversions between:
  - Spec side: Rich types (Address, Uint256, ContractState, Transaction)
  - IR side: Uniform Nat (IRState, IRTransaction)

  These conversions enable proving that compilation preserves semantics.
-/

import Compiler.Proofs.IRGeneration.IRInterpreter
import Verity.Proofs.Stdlib.Automation

namespace Compiler.Proofs.IRGeneration

open Compiler
open Verity
open DiffTestTypes
open Verity.Proofs.Stdlib.SpecInterpreter

/-! ## Address Encoding -/

/-- Convert Address to Nat for IR execution.

    Address is a bounded Nat structure (val < 2^160), so conversion is trivial.
-/
def addressToNat (addr : Address) : Nat := addr.val

/-! ## Address Domain for Mapping Keys -/

/-- Build a lookup table from Nat keys back to Addresses.

    This gives us a *partial* inverse for addressToNat on a finite address set.
    For any address in `addrs`, we can recover it from its Nat key.
-/
def addressKeyMap (addrs : List Address) : List (Nat × Address) :=
  addrs.map (fun addr => (addressToNat addr, addr))

/-- Partial inverse for addressToNat on a finite address set. -/
def addressFromNat (addrs : List Address) (key : Nat) : Option Address :=
  (addressKeyMap addrs).lookup key

/-! ## Uint256 Conversion -/

/-- Extract Nat value from Uint256 -/
def uint256ToNat (u : Uint256) : Nat := u.val

/-! ## State Conversion -/

/-- Convert ContractState to IRState for IR execution

    Maps:
    - Storage slots: Uint256 values → Nat values
    - Storage mappings: Address keys → Nat keys, Uint256 values → Nat values
    - Sender: Address → Nat

    Mapping conversion is only sound for a finite set of addresses `addrs`:
    we decode Nat keys using the address table derived from `addrs`.
    For keys outside this table, we return 0 (default mapping value).
-/
def contractStateToIRState (addrs : List Address) (state : ContractState) : IRState :=
  { vars := []  -- IR starts with empty variable bindings
    storage := fun slot => uint256ToNat (state.storage slot)
    mappings := fun base key =>
      match addressFromNat addrs key with
      | some addr => uint256ToNat (state.storageMap base addr)
      | none => 0
    memory := fun _ => 0
    calldata := []
    returnValue := none
    sender := addressToNat state.sender }

/-! ## SpecStorage → IRState

    This conversion supports Layer 2 proofs that compare `interpretSpec` and
    `interpretIR` directly, without routing through EDSL `ContractState`.
-/

def specStorageToIRState (storage : SpecStorage) (sender : Address) : IRState :=
  { vars := []
    storage := fun slot => storage.getSlot slot
    mappings := fun base key => storage.getMapping base key
    memory := fun _ => 0
    calldata := []
    returnValue := none
    sender := addressToNat sender
    selector := 0 }

@[simp] theorem specStorageToIRState_storage (storage : SpecStorage) (sender : Address) (slot : Nat) :
    (specStorageToIRState storage sender).storage slot = storage.getSlot slot := by
  rfl

@[simp] theorem specStorageToIRState_mappings (storage : SpecStorage) (sender : Address) (base key : Nat) :
    (specStorageToIRState storage sender).mappings base key = storage.getMapping base key := by
  rfl

@[simp] theorem specStorageToIRState_memory (storage : SpecStorage) (sender : Address) (offset : Nat) :
    (specStorageToIRState storage sender).memory offset = 0 := by
  rfl

@[simp] theorem contractStateToIRState_memory (addrs : List Address) (state : ContractState) (offset : Nat) :
    (contractStateToIRState addrs state).memory offset = 0 := by
  unfold contractStateToIRState
  rfl

/-! ## Transaction Conversion -/

/-- Convert Spec Transaction to IR Transaction

    Requires:
    - Function name → selector mapping (provided externally)
    - Address → Nat conversion
    - Arguments are already Nat in both representations
-/
def transactionToIRTransaction (tx : Transaction) (selector : Nat) : IRTransaction :=
  { sender := addressToNat tx.sender
    functionSelector := selector
    args := tx.args }

/-! ## Result Equivalence -/

/-- Define when IRResult matches SpecResult

    Two results match if:
    1. Success status is the same
    2. Return values match (if present)
    3. Storage states match (after conversion)
    4. Mapping storage matches when the contract uses mappings
-/
def resultsMatch (usesMapping : Bool) (addrs : List Address) (irResult : IRResult)
    (specResult : SpecResult) : Prop :=
  irResult.success = specResult.success ∧
  irResult.returnValue = specResult.returnValue ∧
  (∀ slot, irResult.finalStorage slot = specResult.finalStorage.getSlot slot) ∧
  (usesMapping = true → ∀ baseSlot addr, addr ∈ addrs →
    irResult.finalMappings baseSlot (addressToNat addr) =
      specResult.finalStorage.getMapping baseSlot (addressToNat addr))

/-! ## Notes on Conversion Soundness

The conversion layer makes several simplifying assumptions:

1. **Address encoding**: Address is a bounded Nat (val < 2^160), so conversion
   is trivial identity. Injectivity is provable from the structure definition.

2. **Uint256 conversion**: Direct value extraction is sound because:
   - Uint256.val already represents the mathematical value
   - IR arithmetic uses mod 2^256, matching Uint256 semantics

3. **Mapping conversion**: We decode Nat keys using an explicit address table, which is sufficient because:
   - IR only stores/loads using Nat keys
   - We restrict proofs to a finite list of addresses used by the transaction(s)
   - For those addresses, addressToNat is invertible via `addressFromNat`

4. **Result matching**: We compare component-wise, which is sound because:
   - Success/failure must match exactly
   - Return values must match exactly
   - Storage must match slot-by-slot (after conversion)
   - Mapping equivalence is checked for each address in the address table

These conversions enable the preservation theorem:

  ∀ spec selectors tx state,
    let ir := compile spec selectors
    let irTx := transactionToIRTransaction tx (selectorfromName tx.functionName)
    let irState := contractStateToIRState addrs state
    let irResult := interpretIR ir irTx irState
    let specResult := interpretSpec spec (contractStateToSpecStorage state) tx
    resultsMatch ir.usesMapping addrs irResult specResult

-/

end Compiler.Proofs.IRGeneration
