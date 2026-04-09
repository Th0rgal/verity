import EvmYul
import Compiler.Constants
import Compiler.Proofs.KeccakBound

namespace Compiler.Proofs

/-!
Mapping slot abstraction used by proof interpreters.

The active backend is keccak-faithful (`solidityMappingSlot`).

## Axiom elimination (zero-axiom target)

The mapping-slot definition now uses the kernel-computable `KeccakEngine.keccak256`
so that the output-length bound is structurally provable. The FFI version (`ffi.KEC`)
may optionally be registered via `@[implemented_by]` for runtime performance if
build-time benchmarks show a regression.
-/

/-- Mapping-slot backend chosen for proof semantics. -/
inductive MappingSlotBackend where
  | keccak
  deriving DecidableEq, Repr

/--
Active proof-model backend.

`keccak` is the active, EVM-faithful mapping-slot model.
-/
def activeMappingSlotBackend : MappingSlotBackend := .keccak

/-- Whether the active backend matches EVM keccak-derived slot layout exactly. -/
def activeMappingSlotBackendIsEvmFaithful : Bool := true

/-- ABI-encode `(key, baseSlot)` as two 32-byte words (Solidity mapping convention). -/
def abiEncodeMappingSlot (baseSlot key : Nat) : ByteArray :=
  let keyWord : EvmYul.UInt256 := .ofNat key
  let baseSlotWord : EvmYul.UInt256 := .ofNat baseSlot
  keyWord.toByteArray ++ baseSlotWord.toByteArray

/-- FFI-based mapping slot computation (fast, used at runtime via @[implemented_by]).
    Not used in proofs — proofs reason about `solidityMappingSlot` which uses the
    kernel-computable Keccak. -/
private def solidityMappingSlot_ffi (baseSlot key : Nat) : Nat :=
  EvmYul.fromByteArrayBigEndian (ffi.KEC (abiEncodeMappingSlot baseSlot key))

/-- Solidity mapping storage slot derivation: `keccak256(abi.encode(key, baseSlot))`.

    Uses the kernel-computable Keccak engine so proofs can reason about the output
    size (always 32 bytes → result < 2^256). The FFI version is registered via
    `@[implemented_by]` for runtime performance.

    TODO: Once proofs are complete, uncomment `@[implemented_by solidityMappingSlot_ffi]`
    and benchmark. If build time is acceptable without it, remove `_ffi` entirely. -/
-- @[implemented_by solidityMappingSlot_ffi]
def solidityMappingSlot (baseSlot key : Nat) : Nat :=
  EvmYul.fromByteArrayBigEndian (KeccakEngine.keccak256 (abiEncodeMappingSlot baseSlot key))

/-- Active proof-model mapping slot encoding backend. -/
def abstractMappingSlot (baseSlot key : Nat) : Nat := solidityMappingSlot baseSlot key

/-- Active proof-model mapping slot tag sentinel (backend-specific). -/
def abstractMappingTag : Nat := 0

/-- Active proof-model mapping slot decoder backend. -/
def abstractDecodeMappingSlot (_slot : Nat) : Option (Nat × Nat) := none

/-- Active proof-model nested mapping slot helper. -/
def abstractNestedMappingSlot (baseSlot key1 key2 : Nat) : Nat :=
  abstractMappingSlot (abstractMappingSlot baseSlot key1) key2

/-- Derived mapping-table view from flat storage. -/
def storageAsMappings (storage : Nat → Nat) : Nat → Nat → Nat :=
  fun baseSlot key => storage (solidityMappingSlot baseSlot key)

/-- Read a mapping entry directly from base slot and key. -/
def abstractLoadMappingEntry
    (storage : Nat → Nat)
    (baseSlot key : Nat) : Nat :=
  storage (solidityMappingSlot baseSlot key)

/-- Write a mapping entry directly from base slot and key. -/
def abstractStoreMappingEntry
    (storage : Nat → Nat)
    (baseSlot key value : Nat) : Nat → Nat :=
  fun s => if s = solidityMappingSlot baseSlot key then value else storage s

/-- Read through the active mapping-slot backend from flat storage. -/
def abstractLoadStorageOrMapping
    (storage : Nat → Nat)
    (slot : Nat) : Nat :=
  storage slot

/-- Write through the active mapping-slot backend to flat storage. -/
def abstractStoreStorageOrMapping
    (storage : Nat → Nat)
    (slot value : Nat) : Nat → Nat :=
  fun s => if s = slot then value else storage s

@[simp] theorem abstractMappingSlot_eq_solidity (baseSlot key : Nat) :
    abstractMappingSlot baseSlot key = solidityMappingSlot baseSlot key := rfl

@[simp] theorem abstractMappingTag_eq_zero :
    abstractMappingTag = 0 := rfl

@[simp] theorem abstractDecodeMappingSlot_eq_none (slot : Nat) :
    abstractDecodeMappingSlot slot = none := rfl

@[simp] theorem activeMappingSlotBackend_eq_keccak :
    activeMappingSlotBackend = .keccak := rfl

@[simp] theorem activeMappingSlotBackendIsEvmFaithful_eq_true :
    activeMappingSlotBackendIsEvmFaithful = true := rfl

@[simp] theorem abstractNestedMappingSlot_eq_solidityNested (baseSlot key1 key2 : Nat) :
    abstractNestedMappingSlot baseSlot key1 key2 =
      solidityMappingSlot (solidityMappingSlot baseSlot key1) key2 := by
  simp [abstractNestedMappingSlot]

@[simp] theorem abstractLoadMappingEntry_eq
    (storage : Nat → Nat)
    (baseSlot key : Nat) :
    abstractLoadMappingEntry storage baseSlot key = storage (solidityMappingSlot baseSlot key) := rfl

@[simp] theorem abstractStoreMappingEntry_eq
    (storage : Nat → Nat)
    (baseSlot key value : Nat) :
    abstractStoreMappingEntry storage baseSlot key value =
      (fun s => if s = solidityMappingSlot baseSlot key then value else storage s) := rfl

@[simp] theorem abstractLoadStorageOrMapping_eq
    (storage : Nat → Nat)
    (slot : Nat) :
    abstractLoadStorageOrMapping storage slot = storage slot := rfl

@[simp] theorem abstractStoreStorageOrMapping_eq
    (storage : Nat → Nat)
    (slot value : Nat) :
    abstractStoreStorageOrMapping storage slot value =
      (fun s => if s = slot then value else storage s) := rfl

/-- Keccak256 output interpreted as a big-endian 256-bit natural is less than 2^256.
    This is mathematically true because keccak produces exactly 32 bytes, so
    `fromByteArrayBigEndian` gives a value < 2^(8*32) = 2^256 = evmModulus.

    Previously an axiom — now a theorem thanks to the kernel-computable Keccak engine
    which exposes the output length to the proof system. -/
theorem solidityMappingSlot_lt_evmModulus (baseSlot key : Nat) :
    solidityMappingSlot baseSlot key < Compiler.Constants.evmModulus := by
  unfold solidityMappingSlot
  exact fromByteArrayBigEndian_lt_of_size _ (by
    rw [KeccakEngine.keccak256_size])

theorem abstractMappingSlot_lt_evmModulus (baseSlot key : Nat) :
    abstractMappingSlot baseSlot key < Compiler.Constants.evmModulus :=
  solidityMappingSlot_lt_evmModulus baseSlot key

theorem solidityMappingSlot_add_lt_evmModulus (baseSlot key wordOffset : Nat)
    (h : wordOffset < Compiler.Constants.evmModulus - solidityMappingSlot baseSlot key) :
    solidityMappingSlot baseSlot key + wordOffset < Compiler.Constants.evmModulus := by
  omega

/-- The sum of a mapping slot and a word offset fits in 256 bits.
    This holds because keccak256 output < 2^256 and word offsets are
    bounded explicitly by the available headroom under `2^256`. -/
theorem solidityMappingSlot_add_wordOffset_lt_evmModulus
    (baseSlot key wordOffset : Nat)
    (h : wordOffset < Compiler.Constants.evmModulus - solidityMappingSlot baseSlot key) :
    solidityMappingSlot baseSlot key + wordOffset < Compiler.Constants.evmModulus := by
  exact solidityMappingSlot_add_lt_evmModulus baseSlot key wordOffset h

end Compiler.Proofs
