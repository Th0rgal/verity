/-
  EvmYulLeanStateBridge: Type-level scaffolding for the Phase 2 state bridge
  between Verity's `YulState` and EVMYulLean's `SharedState .Yul`.

  This module defines the conversion functions needed to translate between
  Verity's flat execution state and EVMYulLean's account-map–based state.
  The conversion covers:

  1. **Variable bindings**: `List (String × Nat)` ↔ `VarStore` (Finmap)
  2. **Storage**: `Nat → Nat` ↔ `Storage` (RBMap UInt256 UInt256)
  3. **Execution environment**: flat fields ↔ `ExecutionEnv .Yul`
  4. **Block information**: flat fields ↔ `BlockHeader`

  Phase 2 proof obligations (tracked in issue #1722):
  - Round-trip lemma: `fromSharedState (toSharedState s) = s` for observable fields
  - Storage read commutation: `sload` in EVMYulLean = Verity's storage lookup
  - Storage write commutation: `sstore` in EVMYulLean = Verity's storage update
  - Environment field extraction: `caller`/`address`/`timestamp`/etc. agree

  Design constraints:
  - Verity's `storage : Nat → Nat` is infinite-domain; EVMYulLean's `Storage`
    is finite (RBMap). The bridge only observes slots that were written.
  - Verity has no account model; EVMYulLean has `AccountMap`. The bridge
    creates a minimal single-account state.
  - Verity's calldata is `List Nat` (32-byte words); EVMYulLean's is `ByteArray`.
    The bridge converts between word-level and byte-level representations.
-/

import Compiler.Proofs.YulGeneration.Semantics
import EvmYul.Yul.State
import EvmYul.SharedState
import EvmYul.State.Account
import EvmYul.UInt256
import EvmYul.Maps.StorageMap
import Batteries.Data.RBMap.Lemmas

namespace Compiler.Proofs.YulGeneration.Backends.StateBridge

open Compiler.Proofs.YulGeneration
open EvmYul

/-! ## Nat ↔ UInt256 Conversions -/

/-- Convert a Verity Nat value to an EVMYulLean UInt256. -/
abbrev natToUInt256 (n : Nat) : UInt256 := UInt256.ofNat n

/-- Convert an EVMYulLean UInt256 to a Verity Nat value. -/
abbrev uint256ToNat (u : UInt256) : Nat := u.toNat

/-! ## Variable Store Bridge

Verity uses `List (String × Nat)` for variable bindings (most recent first).
EVMYulLean uses `VarStore` which is `Finmap (λ _ : String ↦ UInt256)`.

Key semantic difference: Verity's list-based store allows shadowing (duplicate
keys); `getVar` returns the *first* match. EVMYulLean's Finmap is a map
(unique keys). The bridge takes the most recent binding for each variable. -/

/-- Convert Verity variable bindings to EVMYulLean VarStore.
    Uses foldl so that the first (most recent) binding for each variable wins,
    matching Verity's `getVar` shadowing semantics.

    Note: We use the expanded Finmap type rather than the VarStore abbrev
    throughout this definition because Lean 4's unifier does not always
    unfold abbrevs when matching against Finmap's universe-polymorphic
    structure.  The result is still VarStore-compatible since VarStore is
    a transparent abbreviation. -/
noncomputable def varsToVarStore (vars : List (String × Nat)) :
    Finmap (fun _ : Identifier => Literal) :=
  vars.foldl (init := (∅ : Finmap (fun _ : Identifier => Literal)))
    fun store (name, val) =>
      let id : Identifier := name
      if (Finmap.lookup id store).isSome then store
      else Finmap.insert id (natToUInt256 val) store

/-- Convert EVMYulLean VarStore back to Verity variable bindings.
    Order is not preserved (Finmap has no canonical ordering). -/
noncomputable def varStoreToVars (store : Finmap (fun _ : Identifier => Literal)) :
    List (String × Nat) :=
  store.entries.toList.map fun ⟨name, val⟩ => ((name : String), uint256ToNat val)

/-! ## Storage Bridge

Verity uses `Nat → Nat` (total function, default 0 for unwritten slots).
EVMYulLean uses `Storage` = `RBMap UInt256 UInt256` (finite map, default 0).

The round-trip requires knowing which slots are "observable" — the bridge
can only reconstruct slots that are in the EVMYulLean RBMap. For the
forward direction (Verity → EVMYulLean), we need to know which slots to
project. In practice, this is the set of slots written during execution. -/

/-- Look up a storage slot in EVMYulLean's Storage map, returning 0 for
    unwritten slots (matching Verity's `Nat → Nat` semantics). -/
def storageLookup (s : EvmYul.Storage) (slot : UInt256) : UInt256 :=
  match s.find? slot with
  | some val => val
  | none => ⟨0⟩

/-- Write a storage slot in EVMYulLean's Storage map. -/
def storageWrite (s : EvmYul.Storage) (slot val : UInt256) : EvmYul.Storage :=
  s.insert slot val

/-- Project a finite set of Verity storage slots into an EVMYulLean Storage map. -/
def projectStorage (storage : Nat → Nat) (slots : List Nat) : EvmYul.Storage :=
  slots.foldl (init := Batteries.RBMap.empty) fun acc slot =>
    let key := natToUInt256 slot
    let val := natToUInt256 (storage slot)
    acc.insert key val

/-! ## Execution Environment Bridge

Maps Verity's flat YulState fields to EVMYulLean's `ExecutionEnv .Yul`. -/

/-- Convert a Verity address (Nat) to an EVMYulLean AccountAddress.
    EVMYulLean's AccountAddress is `Fin (2^160)`. -/
def natToAddress (n : Nat) : AccountAddress :=
  ⟨n % (2 ^ 160), Nat.mod_lt _ (by decide)⟩

/-- Create a minimal EVMYulLean BlockHeader from Verity's block fields.
    Fields not modeled by Verity (e.g. baseFeePerGas, gasLimit) are set to
    default zero values. Note: Verity's `blobBaseFee` is the blob gas price,
    which in EVMYulLean is derived from `excessBlobGas` via `getBlobGasprice`;
    the reverse mapping is not straightforward, so it is left as 0 here. -/
def mkBlockHeader (state : YulState) : BlockHeader :=
  { parentHash := ⟨0⟩
    ommersHash := ⟨0⟩
    beneficiary := ⟨0, by decide⟩
    stateRoot := ⟨0⟩
    transRoot := ByteArray.empty
    receiptRoot := ByteArray.empty
    logsBloom := ByteArray.empty
    difficulty := 0
    number := state.blockNumber
    gasLimit := 0
    gasUsed := 0
    timestamp := state.blockTimestamp
    extraData := ByteArray.empty
    nonce := ⟨0, by decide⟩
    prevRandao := ⟨0⟩
    baseFeePerGas := 0
    parentBeaconBlockRoot := ByteArray.empty
    withdrawalsRoot := ByteArray.empty
    blobGasUsed := ⟨0, by decide⟩
    excessBlobGas := ⟨0, by decide⟩ }

/-- Convert Verity calldata (List of 32-byte words) to EVMYulLean calldata
    (ByteArray). Each word is encoded as a big-endian 32-byte chunk.
    Prepends the 4-byte function selector. -/
def calldataToByteArray (selector : Nat) (calldata : List Nat) : ByteArray :=
  -- 4 bytes for selector + 32 bytes per word
  let selectorBytes : ByteArray := Id.run do
    let mut arr := ByteArray.emptyWithCapacity 4
    arr := arr.push (UInt8.ofNat (selector / 2^24 % 256))
    arr := arr.push (UInt8.ofNat (selector / 2^16 % 256))
    arr := arr.push (UInt8.ofNat (selector / 2^8 % 256))
    arr := arr.push (UInt8.ofNat (selector % 256))
    arr
  let wordBytes (w : Nat) : ByteArray := Id.run do
    let mut arr := ByteArray.emptyWithCapacity 32
    for i in List.range 32 do
      arr := arr.push (UInt8.ofNat (w / 2^((31 - i) * 8) % 256))
    arr
  calldata.foldl (init := selectorBytes) fun acc w => acc ++ wordBytes w

/-! ## Full State Conversion

The main bridge functions that convert between Verity's YulState and
EVMYulLean's Yul execution state. -/

/-- Convert Verity's YulState to an EVMYulLean SharedState.
    Requires the set of observable storage slots for projection. -/
def toSharedState (state : YulState) (observableSlots : List Nat) :
    SharedState .Yul :=
  let addr := natToAddress state.thisAddress
  let storage := projectStorage state.storage observableSlots
  let emptyCode : Yul.Ast.contractCode .Yul := Inhabited.default
  let account : Account .Yul :=
    { nonce := ⟨0⟩
      balance := ⟨0⟩
      storage := storage
      code := emptyCode
      tstorage := Batteries.RBMap.empty }
  let accountMap : AccountMap .Yul :=
    (Batteries.RBMap.empty).insert addr account
  let execEnv : ExecutionEnv .Yul :=
    { codeOwner := addr
      sender := natToAddress state.sender
      source := natToAddress state.sender
      weiValue := natToUInt256 state.msgValue
      calldata := calldataToByteArray state.selector state.calldata
      code := emptyCode
      gasPrice := 0
      header := mkBlockHeader state
      depth := 0
      perm := false
      blobVersionedHashes := [] }
  { -- State τ fields
    accountMap := accountMap
    σ₀ := Batteries.RBMap.empty
    totalGasUsedInBlock := 0
    transactionReceipts := #[]
    substate := Inhabited.default
    executionEnv := execEnv
    blocks := #[]
    genesisBlockHeader := mkBlockHeader state
    createdAccounts := Batteries.RBSet.empty
    -- MachineState fields
    gasAvailable := ⟨0⟩
    activeWords := ⟨0⟩
    memory := ByteArray.empty
    returnData := ByteArray.empty
    H_return := ByteArray.empty }

/-- Extract observable storage from an EVMYulLean state for the contract
    at the given address. Returns the Verity-style storage function. -/
def extractStorage (sharedState : SharedState .Yul) (addr : AccountAddress) :
    Nat → Nat :=
  fun slot =>
    match sharedState.accountMap.find? addr with
    | some account =>
      match account.storage.find? (natToUInt256 slot) with
      | some val => uint256ToNat val
      | none => 0
    | none => 0

/-! ## Environment Field Bridge Proofs

These theorems prove that Verity's `evalBuiltinCallWithContext` agrees with the
corresponding field extraction from the EVMYulLean state constructed by
`toSharedState`. Each theorem connects a stateful builtin's Verity semantics
to the state bridge.

The proof pattern is uniform:
1. Unfold the Verity builtin to `some (field % evmModulus)`
2. Unfold the bridge to `natToUInt256 field`
3. Show `uint256ToNat (natToUInt256 field) = field % UInt256.size = field % evmModulus`
   since `UInt256.size = evmModulus`. -/

/-- The `callvalue` builtin reads `msgValue` from Verity's state.
    The state bridge stores `natToUInt256 state.msgValue` in `execEnv.weiValue`.
    These agree modulo `evmModulus`. -/
theorem callvalue_bridge (state : YulState) (observableSlots : List Nat) :
    evalBuiltinCallWithContext state.storage state.sender state.msgValue
      state.thisAddress state.blockTimestamp state.blockNumber state.chainId
      state.blobBaseFee state.selector state.calldata "callvalue" [] =
    some (uint256ToNat (toSharedState state observableSlots).executionEnv.weiValue) := by
  simp [evalBuiltinCallWithContext, toSharedState, uint256ToNat, natToUInt256,
    UInt256.toNat, UInt256.ofNat, Id.run, evmModulus, UInt256.size]

/-- The `timestamp` builtin reads `blockTimestamp` from Verity's state.
    The state bridge stores `state.blockTimestamp` in the block header's
    `timestamp` field. EVMYulLean converts this to `UInt256.ofNat`. -/
theorem timestamp_bridge (state : YulState) (observableSlots : List Nat) :
    evalBuiltinCallWithContext state.storage state.sender state.msgValue
      state.thisAddress state.blockTimestamp state.blockNumber state.chainId
      state.blobBaseFee state.selector state.calldata "timestamp" [] =
    some (uint256ToNat (UInt256.ofNat
      (toSharedState state observableSlots).executionEnv.header.timestamp)) := by
  simp [evalBuiltinCallWithContext, toSharedState, mkBlockHeader, uint256ToNat,
    UInt256.toNat, UInt256.ofNat, Id.run, evmModulus, UInt256.size]

/-- The `number` builtin reads `blockNumber` from Verity's state.
    The state bridge stores `state.blockNumber` in the block header's
    `number` field. EVMYulLean converts this to `UInt256.ofNat`. -/
theorem number_bridge (state : YulState) (observableSlots : List Nat) :
    evalBuiltinCallWithContext state.storage state.sender state.msgValue
      state.thisAddress state.blockTimestamp state.blockNumber state.chainId
      state.blobBaseFee state.selector state.calldata "number" [] =
    some (uint256ToNat (UInt256.ofNat
      (toSharedState state observableSlots).executionEnv.header.number)) := by
  simp [evalBuiltinCallWithContext, toSharedState, mkBlockHeader, uint256ToNat,
    UInt256.toNat, UInt256.ofNat, Id.run, evmModulus, UInt256.size]

/-- The `caller` builtin reads `sender` from Verity's state.
    The state bridge stores `natToAddress state.sender` in `execEnv.source`.
    EVMYulLean's CALLER extracts `source` as `UInt256.ofNat (Fin.val source)`.

    Since `natToAddress n = ⟨n % 2^160, _⟩`, the EVMYulLean side returns
    `UInt256.ofNat (n % 2^160)`. Verity returns `sender` (no modular reduction
    in `evalBuiltinCallWithContext`). Agreement requires the hypothesis that
    `sender < evmModulus` (it's an Ethereum address, so `< 2^160 < 2^256`). -/
theorem caller_bridge (state : YulState) (observableSlots : List Nat)
    (hSender : state.sender < 2 ^ 160) :
    evalBuiltinCallWithContext state.storage state.sender state.msgValue
      state.thisAddress state.blockTimestamp state.blockNumber state.chainId
      state.blobBaseFee state.selector state.calldata "caller" [] =
    some (uint256ToNat (UInt256.ofNat
      (toSharedState state observableSlots).executionEnv.source.val)) := by
  simp only [evalBuiltinCallWithContext, toSharedState, natToAddress,
    uint256ToNat, UInt256.toNat, UInt256.ofNat, Id.run]
  congr 1
  rw [Nat.mod_eq_of_lt hSender]
  exact (Nat.mod_eq_of_lt (by unfold UInt256.size; omega : state.sender < UInt256.size)).symm

/-- The `address` builtin reads `thisAddress` from Verity's state.
    The state bridge stores `natToAddress state.thisAddress` in `execEnv.codeOwner`.
    EVMYulLean's ADDRESS extracts `codeOwner` as `UInt256.ofNat (Fin.val codeOwner)`.

    Agreement requires `thisAddress < 2^160` (valid Ethereum address). -/
theorem address_bridge (state : YulState) (observableSlots : List Nat)
    (hAddr : state.thisAddress < 2 ^ 160) :
    evalBuiltinCallWithContext state.storage state.sender state.msgValue
      state.thisAddress state.blockTimestamp state.blockNumber state.chainId
      state.blobBaseFee state.selector state.calldata "address" [] =
    some (uint256ToNat (UInt256.ofNat
      (toSharedState state observableSlots).executionEnv.codeOwner.val)) := by
  simp only [evalBuiltinCallWithContext, toSharedState, natToAddress,
    uint256ToNat, UInt256.toNat, UInt256.ofNat, Id.run, evmModulus, UInt256.size]
  congr 1
  rw [Nat.mod_eq_of_lt hAddr]
  exact Nat.mod_eq_of_lt (by omega : state.thisAddress < 2 ^ 256)

/-! ## Storage Bridge Proofs -/

/-- `TransCmp` instance for `UInt256`'s derived `compare`.
    `UInt256` derives `Ord` which compares via the `Fin` field.
    `Fin n` has `TransOrd` and `LawfulEqOrd` in Lean 4's Std library.

    We prove this by destructuring `UInt256` to its `Fin` field and
    delegating to `Fin`'s `TransCmp` instance. -/
instance instTransCmpUInt256 : Std.TransCmp (α := UInt256) compare where
  eq_swap {a b} := by
    cases a; cases b; exact Std.OrientedCmp.eq_swap (α := Fin UInt256.size)
  isLE_trans {a b c} hab hbc := by
    cases a; cases b; cases c
    exact Std.TransCmp.isLE_trans (α := Fin UInt256.size) hab hbc

/-- `compare` on `UInt256` returning `.eq` implies equality.
    Proved by destructuring to `Fin` and using `Fin`'s `LawfulEqOrd`. -/
theorem UInt256_eq_of_compare_eq {u v : UInt256}
    (h : compare u v = Ordering.eq) : u = v := by
  -- Derived Ord on single-field structures like UInt256 compares the field
  -- directly: compare (mk a) (mk b) = compare a b (on Fin UInt256.size).
  -- This is a definitional reduction in Lean 4.
  cases u with | mk uv =>
  cases v with | mk vv =>
  -- After cases, h : compare (UInt256.mk uv) (UInt256.mk vv) = .eq
  -- which definitionally reduces to compare uv vv = .eq
  -- Use Fin's LawfulEqOrd to get uv = vv, then wrap in mk
  have heq : uv = vv := Std.LawfulEqCmp.eq_of_compare h
  subst heq
  rfl

/-- `natToUInt256` is injective on values below `UInt256.size`.
    Since `UInt256.ofNat n = ⟨⟨n % size, _⟩⟩`, when `n < size` we have
    `n % size = n`, so the Fin value is exactly `n`. -/
theorem natToUInt256_injective {a b : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size)
    (h : natToUInt256 a = natToUInt256 b) : a = b := by
  simp only [natToUInt256, UInt256.ofNat, Id.run] at h
  have : a % UInt256.size = b % UInt256.size :=
    congrArg (fun u => u.val.val) h
  omega

/-- Distinct in-range Nats map to UInt256s with `compare ≠ .eq`. -/
theorem compare_natToUInt256_ne {a b : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size) (hab : a ≠ b) :
    compare (natToUInt256 a) (natToUInt256 b) ≠ Ordering.eq := by
  intro heq
  exact hab (natToUInt256_injective ha hb (UInt256_eq_of_compare_eq heq))

/-- Helper: folding inserts over a list of slots that does NOT contain `slot`
    preserves whatever `find?` value the accumulator had for `natToUInt256 slot`. -/
theorem foldl_insert_find_not_mem (storage : Nat → Nat)
    (slots : List Nat) (slot : Nat) (hNotMem : slot ∉ slots)
    (hRange : ∀ s ∈ slots, s < UInt256.size)
    (hSlotRange : slot < UInt256.size)
    (acc : EvmYul.Storage) :
    (slots.foldl (fun m s => m.insert (natToUInt256 s) (natToUInt256 (storage s))) acc).find?
      (natToUInt256 slot) = acc.find? (natToUInt256 slot) := by
  induction slots generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hNotMemTl : slot ∉ tl := fun h => hNotMem (List.mem_cons_of_mem _ h)
    have hne : hd ≠ slot := fun h => hNotMem (h ▸ List.mem_cons_self _ _)
    have hd_range : hd < UInt256.size := hRange hd (List.mem_cons_self _ _)
    rw [ih hNotMemTl (fun s hs => hRange s (List.mem_cons_of_mem _ hs))]
    exact Batteries.RBMap.find?_insert_of_ne _
      (compare_natToUInt256_ne hSlotRange hd_range (Ne.symm hne))

/-- Helper: after folding a suffix of slots into an accumulator, if `slot`
    is in that suffix, then the accumulated map contains the right value.

    This generalizes `storageLookup_projectStorage` to work with any
    accumulator (not just `empty`), which is needed for the induction. -/
theorem foldl_insert_find (storage : Nat → Nat)
    (slots : List Nat) (slot : Nat) (hSlot : slot ∈ slots)
    (hRange : ∀ s ∈ slots, s < UInt256.size)
    (acc : EvmYul.Storage) :
    (slots.foldl (fun m s => m.insert (natToUInt256 s) (natToUInt256 (storage s))) acc).find?
      (natToUInt256 slot) = some (natToUInt256 (storage slot)) := by
  induction slots generalizing acc with
  | nil => exact absurd hSlot List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hSlot with
    | inl heq =>
      subst heq
      by_cases hmem : slot ∈ tl
      · -- slot also appears later in tl; the last insert wins with same value
        exact ih hmem (fun s hs => hRange s (List.mem_cons_of_mem _ hs)) _
      · -- slot not in tl: the fold over tl preserves the inserted value
        have hSlotRange : slot < UInt256.size := hRange slot (List.mem_cons_self _ _)
        rw [foldl_insert_find_not_mem storage tl slot hmem
          (fun s hs => hRange s (List.mem_cons_of_mem _ hs)) hSlotRange]
        exact Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self
    | inr hmem =>
      exact ih hmem (fun s hs => hRange s (List.mem_cons_of_mem _ hs)) _

/-- Storage lookup commutes: reading a slot from the projected storage
    yields the same value as reading it from Verity's storage function.

    The `hRange` hypothesis ensures `natToUInt256` is injective on the
    slot list (EVM storage slots are always < 2^256). Without it, two
    distinct Nat slots could collide under modular reduction and the
    last-write-wins semantics of `foldl` would make the theorem false. -/
theorem storageLookup_projectStorage (storage : Nat → Nat)
    (slots : List Nat) (slot : Nat) (hSlot : slot ∈ slots)
    (hRange : ∀ s ∈ slots, s < UInt256.size) :
    uint256ToNat (storageLookup (projectStorage storage slots) (natToUInt256 slot)) =
      storage slot % UInt256.size := by
  simp only [storageLookup, projectStorage]
  rw [foldl_insert_find storage slots slot hSlot hRange]
  simp only [uint256ToNat, natToUInt256, UInt256.toNat, UInt256.ofNat, Id.run, Fin.val_ofNat]

/-- Nat→UInt256→Nat round-trip for values in range.
    Proof: `ofNat n = ⟨Fin.ofNat _ n⟩ = ⟨⟨n % size, _⟩⟩`, and
    `toNat` extracts `.val.val`, so the goal reduces to `n % size = n`
    which follows from `Nat.mod_eq_of_lt h`. -/
theorem uint256_roundtrip (n : Nat) (h : n < UInt256.size) :
    uint256ToNat (natToUInt256 n) = n := by
  simp only [uint256ToNat, natToUInt256, UInt256.toNat, UInt256.ofNat, Id.run]
  exact Nat.mod_eq_of_lt h

end Compiler.Proofs.YulGeneration.Backends.StateBridge
