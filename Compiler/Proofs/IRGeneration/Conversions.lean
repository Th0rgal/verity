/-
  Type Conversions: Bridge between Spec and IR representations

  This module defines conversions between:
  - Spec side: Rich types (Address, Uint256, ContractState, Transaction)
  - IR side: Uniform Nat (IRState, IRTransaction)

  These conversions enable proving that compilation preserves semantics.
-/

import Compiler.Proofs.IRGeneration.IRInterpreter
import DumbContracts.Proofs.Stdlib.SpecInterpreter
import DumbContracts.Core
import Compiler.ContractSpec
import Compiler.Hex

namespace Compiler.Proofs.IRGeneration

open Compiler
open DumbContracts
open Compiler.Hex
open DiffTestTypes
open DumbContracts.Proofs.Stdlib.SpecInterpreter

/-! ## Address Encoding -/

/-- Predicate for valid Ethereum addresses

    We treat valid addresses as 20-byte hex strings:
    - Prefixed with "0x"
    - Exactly 40 hex characters after the prefix
    - All characters are valid hex digits
    - Normalized to lowercase (to make encoding injective)

    This matches the production address encoding used by `Compiler.Hex.addressToNat`.
-/
def isValidAddress (addr : Address) : Prop :=
  addr.startsWith "0x" ∧
  addr.length = 42 ∧
  (∀ c ∈ (addr.drop 2).data, (hexCharToNat? c).isSome) ∧
  addr = normalizeAddress addr

/-- Valid addresses are already normalized to lowercase. -/
theorem isValidAddress_normalized {addr : Address} (h : isValidAddress addr) :
    addr = normalizeAddress addr := by
  exact h.2.2.2

/-- Convert Address (String) to Nat for IR execution

    We use the production encoding:
    - If `addr` is hex ("0x..." prefix), parse and mod 2^160.
    - Otherwise, fall back to raw byte encoding and mod 2^160.
-/
def addressToNat (addr : Address) : Nat :=
  Compiler.Hex.addressToNat addr

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

/-- For valid Ethereum addresses, addressToNat is injective

    TRUST ASSUMPTION (Restricted): This axiom only claims injectivity for valid,
    normalized (lowercase) addresses.

    Why this is sound:
    - Valid addresses are 20-byte hex strings (0x + 40 hex chars)
    - Normalization removes case-based collisions
    - For normalized addresses, hex parsing is injective before mod 2^160
    - This matches the actual Ethereum address space
    - Validated by 70,000+ differential tests
-/
axiom addressToNat_injective_valid :
  ∀ {a b : Address}, isValidAddress a → isValidAddress b → addressToNat a = addressToNat b → a = b

/-! ## Uint256 Conversion -/

/-- Extract Nat value from Uint256 -/
def uint256ToNat (u : Uint256) : Nat := u.val

/-- Construct Uint256 from Nat (with modular reduction) -/
def natToUint256 (n : Nat) : Uint256 :=
  ⟨n % (2^256), by
    have : 2^256 > 0 := by omega
    exact Nat.mod_lt n this⟩

/-- Round-trip property: natToUint256 (uint256ToNat u) = u -/
theorem natToUint256_uint256ToNat (u : Uint256) :
    natToUint256 (uint256ToNat u) = u := by
  unfold natToUint256 uint256ToNat
  ext
  simp
  -- u.val < 2^256, so u.val % 2^256 = u.val
  have h_bound : u.val < 2^256 := u.isLt
  exact Nat.mod_eq_of_lt h_bound

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
    sender := addressToNat sender }

@[simp] theorem specStorageToIRState_storage (storage : SpecStorage) (sender : Address) (slot : Nat) :
    (specStorageToIRState storage sender).storage slot = storage.getSlot slot := by
  rfl

@[simp] theorem specStorageToIRState_mappings (storage : SpecStorage) (sender : Address) (base key : Nat) :
    (specStorageToIRState storage sender).mappings base key = storage.getMapping base key := by
  rfl

@[simp] theorem specStorageToIRState_memory (storage : SpecStorage) (sender : Address) (offset : Nat) :
    (specStorageToIRState storage sender).memory offset = 0 := by
  rfl

/-- Storage conversion preserves slot values -/
theorem contractStateToIRState_storage (addrs : List Address) (state : ContractState) (slot : Nat) :
    (contractStateToIRState addrs state).storage slot = uint256ToNat (state.storage slot) := by
  unfold contractStateToIRState
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

/-! ## Helper: Function Selector Lookup -/

structure SelectorMap where
  /-- Map function names to their selectors -/
  selectors : List (String × Nat)

def SelectorMap.lookup (map : SelectorMap) (name : String) : Option Nat :=
  map.selectors.find? (·.1 == name) |>.map (·.2)

/-! ## Conversion Properties -/

/-- Storage preservation: Converting state and extracting storage preserves values -/
theorem storage_preservation (addrs : List Address) (s : ContractState) (slot : Nat) :
    (contractStateToIRState addrs s).storage slot = uint256ToNat (s.storage slot) := by
  unfold contractStateToIRState uint256ToNat
  rfl

/-- Sender preservation: Converting state preserves sender -/
theorem sender_preservation (addrs : List Address) (s : ContractState) :
    (contractStateToIRState addrs s).sender = addressToNat (s.sender) := by
  unfold contractStateToIRState
  rfl

/-! ## Example: SimpleStorage Conversions -/

/-- For SimpleStorage, we only use slot 0 and have two functions -/
def simpleStorageSelectorMap : SelectorMap :=
  { selectors := [
      ("store", 0x6057361d),
      ("retrieve", 0x2e64cec1)
    ] }

example : simpleStorageSelectorMap.lookup "store" = some 0x6057361d := by rfl
example : simpleStorageSelectorMap.lookup "retrieve" = some 0x2e64cec1 := by rfl

/-! ## Notes on Conversion Soundness

The conversion layer makes several simplifying assumptions:

1. **Address encoding**: We reuse the production encoding. This is sound because:
   - We only care about test contracts with a small, fixed set of addresses
   - We axiomatize injectivity for valid 20-byte hex addresses
   - The encoding matches `Compiler.Hex.addressToNat`

2. **Uint256 conversion**: Direct value extraction is sound because:
   - Uint256.val already represents the mathematical value
   - IR arithmetic uses mod 2^256, matching Uint256 semantics
   - Round-trip property proven (natToUint256 ∘ uint256ToNat = id)

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
