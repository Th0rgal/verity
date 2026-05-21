import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeState
import Lean

namespace Compiler.Proofs.YulGeneration.Backends.Native

open Compiler.Yul
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends.StateBridge
open Lean Elab Tactic Meta
open Compiler.Proofs.IRGeneration
  (IRResult IRState IRStorageSlot IRStorageWord IRTransaction)

private theorem byteArray_get?_append_left
    {a b : ByteArray} {i : Nat} (h : i < a.size) :
    (a ++ b).get? i = a.get? i := by
  unfold ByteArray.get?
  split
  · apply congrArg some
    have hEq : (a ++ b)[i] = a[i] := ByteArray.get_append_left h
    convert hEq using 1
  · exact False.elim (by
      rename_i hAppend
      exact hAppend (by
        rw [ByteArray.size_append]
        exact Nat.lt_of_lt_of_le h (Nat.le_add_right a.size b.size)))

/-- Reading the first ABI word from offset zero preserves every source byte
    already present in the first 32-byte window. This isolates the non-opaque
    part of EVMYulLean's `ByteArray.readBytes`; padding may still come from
    `ffi.ByteArray.zeroes`, but the dispatcher selector only depends on bytes
    0 through 3. -/
theorem readBytes_zero_get?_of_lt_source
    (source : ByteArray)
    (i : Nat)
    (hi : i < source.size)
    (hi32 : i < 32) :
    (ByteArray.readBytes source 0 32).get? i = source.get? i := by
  unfold ByteArray.readBytes
  have hsmall : (decide (0 < 2 ^ 64) && decide (32 < 2 ^ 64)) = true := by
    norm_num
  simp only [hsmall, ↓reduceIte]
  have hiData : i < source.data.size := by
    simpa using hi
  have hCopySize : i < (source.copySlice 0 ByteArray.empty 0 32).size := by
    simp [ByteArray.size, ByteArray.data_copySlice]
    exact ⟨hi32, hiData⟩
  calc
    (source.copySlice 0 ByteArray.empty 0 32 ++
          ffi.ByteArray.zeroes
            { toBitVec := ↑32 -
              ↑(source.copySlice 0 ByteArray.empty 0 32).size }).get? i
        = (source.copySlice 0 ByteArray.empty 0 32).get? i :=
          byteArray_get?_append_left hCopySize
    _ = source.get? i := by
      unfold ByteArray.get?
      split
      · simp [ByteArray.get]
      · contradiction

/-- Reading a 32-byte window preserves every byte that is already present in the
    source window, for offsets accepted by EVMYulLean's optimized
    `ByteArray.readBytes` branch. -/
theorem readBytes_get?_of_lt_source
    (source : ByteArray)
    (offset i : Nat)
    (hoffset : offset < 2 ^ 64)
    (hi : offset + i < source.size)
    (hi32 : i < 32) :
    (ByteArray.readBytes source offset 32).get? i =
      source.get? (offset + i) := by
  unfold ByteArray.readBytes
  have hoffset' : offset < 18446744073709551616 := by
    simpa using hoffset
  have hsmall : (decide (offset < 2 ^ 64) && decide (32 < 2 ^ 64)) = true := by
    simp [hoffset']
  simp only [hsmall, ↓reduceIte]
  have hiData : offset + i < source.data.size := by
    simpa using hi
  have hCopySize : i < (source.copySlice offset ByteArray.empty 0 32).size := by
    simp [ByteArray.size, ByteArray.data_copySlice]
    omega
  calc
    (source.copySlice offset ByteArray.empty 0 32 ++
          ffi.ByteArray.zeroes
            { toBitVec := ↑32 -
              ↑(source.copySlice offset ByteArray.empty 0 32).size }).get? i
        = (source.copySlice offset ByteArray.empty 0 32).get? i :=
          byteArray_get?_append_left hCopySize
    _ = source.get? (offset + i) := by
      unfold ByteArray.get?
      split
      · simp [ByteArray.get]
      · contradiction

/-- Reading the ABI word at calldata offset four preserves each source byte
    already present in that 32-byte argument window. This is the native
    `calldataload(4)` byte-level counterpart of
    `readBytes_zero_get?_of_lt_source`. -/
theorem readBytes_offset4_get?_of_lt_source
    (source : ByteArray)
    (i : Nat)
    (hi : 4 + i < source.size)
    (hi32 : i < 32) :
    (ByteArray.readBytes source 4 32).get? i = source.get? (4 + i) := by
  exact readBytes_get?_of_lt_source source 4 i (by norm_num) hi hi32

@[simp] theorem initialState_calldataReadWord_selectorByte0
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        0 32).get? 0 =
      some (UInt8.ofNat (tx.functionSelector / 2^24 % 256)) := by
  rw [readBytes_zero_get?_of_lt_source]
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp [calldataToByteArray_size]
  · norm_num

@[simp] theorem initialState_calldataReadWord_selectorByte1
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        0 32).get? 1 =
      some (UInt8.ofNat (tx.functionSelector / 2^16 % 256)) := by
  rw [readBytes_zero_get?_of_lt_source]
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp [calldataToByteArray_size]
    omega
  · norm_num

@[simp] theorem initialState_calldataReadWord_selectorByte2
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        0 32).get? 2 =
      some (UInt8.ofNat (tx.functionSelector / 2^8 % 256)) := by
  rw [readBytes_zero_get?_of_lt_source]
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp [calldataToByteArray_size]
    omega
  · norm_num

@[simp] theorem initialState_calldataReadWord_selectorByte3
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        0 32).get? 3 =
      some (UInt8.ofNat (tx.functionSelector % 256)) := by
  rw [readBytes_zero_get?_of_lt_source]
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp [calldataToByteArray_size]
    omega
  · norm_num

/-- Native initial calldata exposes the first ABI argument word at offset four,
    byte-for-byte, before EVMYulLean recomposes it into a `UInt256`. -/
theorem initialState_calldataReadWord_arg0Byte
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (i : Nat)
    (hi : i < 32) :
    (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        4 32).get? i =
      some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
  rw [readBytes_offset4_get?_of_lt_source]
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    rw [hArgs]
    exact calldataToByteArray_arg0Byte tx.functionSelector arg rest i hi
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    rw [hArgs]
    simp [calldataToByteArray_size]
    omega
  · exact hi

/-- Native initial calldata exposes any aligned ABI argument word byte-for-byte
    when the argument is present and the read offset stays in the optimized
    `ByteArray.readBytes` range. -/
theorem initialState_calldataReadWord_argByte_of_drop_eq_cons
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (idx arg : Nat)
    (rest : List Nat)
    (hdrop : tx.args.drop idx = arg :: rest)
    (hoffset : 4 + 32 * idx < 2 ^ 64)
    (i : Nat)
    (hi : i < 32) :
    (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        (4 + 32 * idx) 32).get? i =
      some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
  rw [readBytes_get?_of_lt_source]
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    exact calldataToByteArray_argByte_of_drop_eq_cons tx.functionSelector
      tx.args idx arg rest hdrop i hi
  · exact hoffset
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp [calldataToByteArray_size]
    have hlen := congrArg List.length hdrop
    simp [List.length_drop] at hlen
    omega
  · exact hi

private theorem byteArray_data_toList_get?_of_get?
    (ba : ByteArray)
    (i : Nat)
    (b : UInt8)
    (h : ba.get? i = some b) :
    ba.data.toList[i]? = some b := by
  unfold ByteArray.get? at h
  split at h
  · cases h
    rw [Array.getElem?_toList]
    simp [ByteArray.get]
  · contradiction

private theorem list_reverse_eq_drop4_reverse_append_four
    {α : Type}
    (xs : List α)
    (b0 b1 b2 b3 : α)
    (h0 : xs[0]? = some b0)
    (h1 : xs[1]? = some b1)
    (h2 : xs[2]? = some b2)
    (h3 : xs[3]? = some b3) :
    xs.reverse = (xs.drop 4).reverse ++ [b3, b2, b1, b0] := by
  cases xs with
  | nil => simp at h0
  | cons x0 xs =>
      simp at h0
      subst x0
      cases xs with
      | nil => simp at h1
      | cons x1 xs =>
          simp at h1
          subst x1
          cases xs with
          | nil => simp at h2
          | cons x2 xs =>
              simp at h2
              subst x2
              cases xs with
              | nil => simp at h3
              | cons x3 xs =>
                  simp at h3
                  subst x3
                  simp

/-- The decoded native calldata word has the four ABI selector bytes at the
    high end of EVMYulLean's little-endian `fromBytes'` input. Proving the
    selector value itself still needs the opaque `readBytes` result length. -/
theorem initialState_calldataReadWord_selectorPrefix
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    let bytes := ByteArray.readBytes
      (initialState contract tx storage observableSlots).toState.executionEnv.calldata 0 32
    bytes.data.toList.reverse =
      (bytes.data.toList.drop 4).reverse ++
        [UInt8.ofNat (tx.functionSelector % 256),
         UInt8.ofNat (tx.functionSelector / 2^8 % 256),
         UInt8.ofNat (tx.functionSelector / 2^16 % 256),
         UInt8.ofNat (tx.functionSelector / 2^24 % 256)] := by
  intro bytes
  apply list_reverse_eq_drop4_reverse_append_four
  · exact byteArray_data_toList_get?_of_get? bytes 0 _
      (initialState_calldataReadWord_selectorByte0 contract tx storage observableSlots)
  · exact byteArray_data_toList_get?_of_get? bytes 1 _
      (initialState_calldataReadWord_selectorByte1 contract tx storage observableSlots)
  · exact byteArray_data_toList_get?_of_get? bytes 2 _
      (initialState_calldataReadWord_selectorByte2 contract tx storage observableSlots)
  · exact byteArray_data_toList_get?_of_get? bytes 3 _
      (initialState_calldataReadWord_selectorByte3 contract tx storage observableSlots)

/-- Recompose the four ABI selector bytes into the normalized 32-bit
    dispatcher selector. This isolates the remaining native byte-decoding proof:
    once `calldataload(0) >>> 224` is reduced to the four high calldata bytes,
    this theorem closes the arithmetic side against the EVMYulLean fuel wrapper. -/
theorem selectorBytesAsNat (selector : Nat) :
    (selector / 2^24 % 256) * 2^24 +
      (selector / 2^16 % 256) * 2^16 +
      (selector / 2^8 % 256) * 2^8 +
      (selector % 256) =
    selector % Compiler.Constants.selectorModulus := by
  have hb0 : selector / 2^24 % 256 =
      (selector % 2^32) / 2^24 := by
    omega
  have hb1 : selector / 2^16 % 256 =
      ((selector % 2^32) % 2^24) / 2^16 := by
    omega
  have hb2 : selector / 2^8 % 256 =
      (((selector % 2^32) % 2^24) % 2^16) / 2^8 := by
    omega
  have hb3 : selector % 256 =
      ((((selector % 2^32) % 2^24) % 2^16) % 2^8) := by
    omega
  rw [hb0, hb1, hb2, hb3]
  have h1 := Nat.div_add_mod (selector % 2^32) (2^24)
  have h2 := Nat.div_add_mod ((selector % 2^32) % 2^24) (2^16)
  have h3 := Nat.div_add_mod (((selector % 2^32) % 2^24) % 2^16) (2^8)
  simp [Compiler.Constants.selectorModulus]
  omega

theorem fromBytes'_append (xs ys : List UInt8) :
    EvmYul.fromBytes' (xs ++ ys) =
      EvmYul.fromBytes' xs + 2^(8 * xs.length) * EvmYul.fromBytes' ys := by
  induction xs with
  | nil =>
      simp [EvmYul.fromBytes']
  | cons x xs ih =>
      simp only [List.cons_append, EvmYul.fromBytes']
      rw [ih]
      rw [show 8 * (x :: xs).length = 8 + 8 * xs.length by
        simp [Nat.mul_add, Nat.add_comm]]
      rw [Nat.pow_add]
      ring

theorem fromBytes'_lt (xs : List UInt8) :
    EvmYul.fromBytes' xs < 2^(8 * xs.length) := by
  induction xs with
  | nil =>
      simp [EvmYul.fromBytes']
  | cons x xs ih =>
      unfold EvmYul.fromBytes'
      have hx : x.toFin.val < 2^8 := by
        have := x.toFin.isLt
        norm_num at this ⊢
        exact this
      simp only [List.length_cons, Nat.mul_succ, Nat.add_comm, Nat.pow_add]
      have _ :=
        Nat.add_le_of_le_sub
          (Nat.one_le_pow _ _ (by decide))
          (Nat.le_sub_one_of_lt ih)
      linarith

private theorem uint256_ofNat_eq_mk
    (value : Nat)
    (hvalue : value < EvmYul.UInt256.size) :
    EvmYul.UInt256.ofNat value = ⟨⟨value, hvalue⟩⟩ := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  simp [Nat.mod_eq_of_lt hvalue]

private theorem uint256_eq_of_toNat_eq
    (a b : EvmYul.UInt256)
    (h : a.toNat = b.toNat) :
    a = b := by
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  simpa [EvmYul.UInt256.toNat] using h

theorem uint256_ofNat_toNat_of_lt
    (value : Nat)
    (hvalue : value < EvmYul.UInt256.size) :
    (EvmYul.UInt256.ofNat value).toNat = value := by
  change (Fin.ofNat EvmYul.UInt256.size value).val = value
  simp [Fin.ofNat]
  exact Nat.mod_eq_of_lt hvalue

private theorem uint256_shiftRight_224_mk_toNat
    (value : Nat)
    (hvalue : value < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight ⟨⟨value, hvalue⟩⟩
        ⟨⟨Compiler.Constants.selectorShift,
          by norm_num [Compiler.Constants.selectorShift, EvmYul.UInt256.size]⟩⟩) =
      value / 2^Compiler.Constants.selectorShift := by
  have hshift : Compiler.Constants.selectorShift < 256 := by
    norm_num [Compiler.Constants.selectorShift]
  have hg : ¬ 256 ≤
      (⟨⟨Compiler.Constants.selectorShift,
        by norm_num [Compiler.Constants.selectorShift, EvmYul.UInt256.size]⟩⟩ :
          EvmYul.UInt256).val := by
    change ¬ 256 ≤ Compiler.Constants.selectorShift
    exact Nat.not_le_of_lt hshift
  simp [EvmYul.UInt256.shiftRight, EvmYul.UInt256.toNat, hg,
    Nat.shiftRight_eq_div_pow]

theorem uint256_shiftRight_224_ofNat_toNat
    (value : Nat)
    (hvalue : value < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight
        (EvmYul.UInt256.ofNat value)
        (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift)) =
      value / 2^Compiler.Constants.selectorShift := by
  rw [uint256_ofNat_eq_mk value hvalue]
  rw [uint256_ofNat_eq_mk Compiler.Constants.selectorShift
    (by norm_num [Compiler.Constants.selectorShift, EvmYul.UInt256.size])]
  exact uint256_shiftRight_224_mk_toNat value hvalue

private theorem fromBytes'_four
    (b0 b1 b2 b3 : UInt8) :
    EvmYul.fromBytes' [b3, b2, b1, b0] =
      b3.toFin.val + 2^8 * b2.toFin.val +
        2^16 * b1.toFin.val + 2^24 * b0.toFin.val := by
  simp [EvmYul.fromBytes']
  omega

private theorem fromBytes'_tail4_shift
    (b0 b1 b2 b3 : UInt8)
    (tail : List UInt8)
    (hlen : tail.length = 28) :
    EvmYul.fromBytes' (tail.reverse ++ [b3, b2, b1, b0]) / 2^224 =
      b0.toFin.val * 2^24 +
        b1.toFin.val * 2^16 +
        b2.toFin.val * 2^8 +
        b3.toFin.val := by
  rw [fromBytes'_append]
  have htailLen : tail.reverse.length = 28 := by
    simp [hlen]
  have htailBound : EvmYul.fromBytes' tail.reverse < 2^224 := by
    have h := fromBytes'_lt tail.reverse
    simpa [htailLen] using h
  rw [fromBytes'_four]
  rw [htailLen]
  norm_num
  omega

private theorem div_pow_succ_byte (arg i : Nat) :
    arg / 2 ^ (8 * (i + 1)) = arg / 256 / 2 ^ (8 * i) := by
  rw [Nat.mul_add, Nat.pow_add]
  norm_num
  rw [Nat.div_div_eq_div_mul]
  ring_nf

private theorem mod_byte_decomp (arg m : Nat) (hm : 0 < m) :
    arg % (256 * m) = arg % 256 + 256 * ((arg / 256) % m) := by
  have hdecomp : arg = 256 * (arg / 256) + arg % 256 := by
    exact (Nat.div_add_mod arg 256).symm
  have hr : arg % 256 < 256 := Nat.mod_lt arg (by norm_num)
  have hsmall : arg % 256 < 256 * m := by nlinarith
  have hqm : (arg / 256) % m < m := Nat.mod_lt _ hm
  have hlt : 256 * ((arg / 256) % m) + arg % 256 < 256 * m := by nlinarith
  conv_lhs => rw [hdecomp]
  rw [Nat.add_mod]
  rw [Nat.mul_mod_mul_left]
  rw [Nat.mod_eq_of_lt hsmall]
  rw [Nat.mod_eq_of_lt hlt]
  ring

private theorem fromBytes'_of_le_bytes (n arg : Nat) :
    EvmYul.fromBytes'
      (List.ofFn fun i : Fin n => UInt8.ofNat (arg / 2 ^ (8 * i.1) % 256)) =
      arg % 2 ^ (8 * n) := by
  induction n generalizing arg with
  | zero =>
      simp [EvmYul.fromBytes']
      omega
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [EvmYul.fromBytes']
      have htail :
          (List.ofFn fun i : Fin n =>
              UInt8.ofNat (arg / 2 ^ (8 * (i.succ.1)) % 256)) =
          (List.ofFn fun i : Fin n =>
              UInt8.ofNat (arg / 256 / 2 ^ (8 * i.1) % 256)) := by
        apply List.ext_getElem <;> simp [div_pow_succ_byte]
      rw [htail]
      rw [ih (arg / 256)]
      simp [UInt8.ofNat, UInt8.size]
      have hpow : 2 ^ (8 * (n + 1)) = 256 * 2 ^ (8 * n) := by
        rw [Nat.mul_add, Nat.pow_add]
        norm_num
        ring
      rw [hpow]
      have hbyte : OfNat.ofNat (arg % 256) % 256 = arg % 256 := by
        change (arg % 256) % 256 = arg % 256
        exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
      rw [mod_byte_decomp arg (2 ^ (8 * n)) (by positivity)]
      rw [hbyte]

private theorem fromBytes'_argWordBytes (arg : Nat) :
    EvmYul.fromBytes'
      ((List.ofFn fun i : Fin 32 =>
        UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)).reverse) =
      arg % EvmYul.UInt256.size := by
  simpa [List.ofFn_succ, EvmYul.UInt256.size] using fromBytes'_of_le_bytes 32 arg

/-- Once the EVMYulLean calldata word has been reduced to a 32-byte big-endian
    list whose first four bytes are the ABI selector, shifting the corresponding
    `fromBytes'` value right by 224 yields the normalized dispatcher selector.
    The remaining native selector proof only has to connect
    `ByteArray.readBytes`/`State.calldataload` to this list shape. -/
theorem fromBytes'_selectorPrefix_shift
    (selector : Nat)
    (tail : List UInt8)
    (hlen : tail.length = 28) :
    EvmYul.fromBytes'
        (tail.reverse ++
          [UInt8.ofNat (selector % 256),
           UInt8.ofNat (selector / 2^8 % 256),
           UInt8.ofNat (selector / 2^16 % 256),
           UInt8.ofNat (selector / 2^24 % 256)]) / 2^224 =
      selector % Compiler.Constants.selectorModulus := by
  rw [fromBytes'_tail4_shift
    (UInt8.ofNat (selector / 2^24 % 256))
    (UInt8.ofNat (selector / 2^16 % 256))
    (UInt8.ofNat (selector / 2^8 % 256))
    (UInt8.ofNat (selector % 256))
    tail hlen]
  norm_num [UInt8.ofNat, UInt8.size]
  have h0 : OfNat.ofNat (selector / 16777216 % 256) % 256 =
      selector / 16777216 % 256 := by
    change (selector / 16777216 % 256) % 256 = selector / 16777216 % 256
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
  have h1 : OfNat.ofNat (selector / 65536 % 256) % 256 =
      selector / 65536 % 256 := by
    change (selector / 65536 % 256) % 256 = selector / 65536 % 256
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
  have h2 : OfNat.ofNat (selector / 256 % 256) % 256 =
      selector / 256 % 256 := by
    change (selector / 256 % 256) % 256 = selector / 256 % 256
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
  have h3 : OfNat.ofNat (selector % 256) % 256 =
      selector % 256 := by
    change (selector % 256) % 256 = selector % 256
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
  rw [h0, h1, h2, h3]
  simpa [Compiler.Constants.selectorModulus] using selectorBytesAsNat selector

private theorem usize_sub_toNat_of_le_32 (n : Nat) (hn : n ≤ 32) :
    ((OfNat.ofNat 32 : USize) - (OfNat.ofNat n : USize)).toNat = 32 - n := by
  rw [USize.toNat_sub]
  rw [USize.toNat_ofNat, USize.toNat_ofNat]
  rcases System.Platform.numBits_eq with hbits | hbits
  · rw [hbits]
    have hnMod : n % 4294967296 = n := by
      apply Nat.mod_eq_of_lt
      omega
    rw [hnMod]
    omega
  · rw [hbits]
    have hnMod : n % 18446744073709551616 = n := by
      apply Nat.mod_eq_of_lt
      omega
    rw [hnMod]
    omega

theorem readBytes_zero_32_size (source : ByteArray) :
    (ByteArray.readBytes source 0 32).size = 32 := by
  unfold ByteArray.readBytes
  have hsmall : (decide (0 < 2 ^ 64) && decide (32 < 2 ^ 64)) = true := by
    norm_num
  simp only [hsmall, ↓reduceIte]
  rw [ByteArray.size_append]
  simp [ffi.ByteArray.zeroes, ByteArray.size]
  rw [usize_sub_toNat_of_le_32]
  · omega
  · omega

theorem readBytes_32_size (source : ByteArray) (offset : Nat)
    (hoffset : offset < 2 ^ 64) :
    (ByteArray.readBytes source offset 32).size = 32 := by
  unfold ByteArray.readBytes
  have hoffset' : offset < 18446744073709551616 := by
    simpa using hoffset
  have hsmall : (decide (offset < 2 ^ 64) && decide (32 < 2 ^ 64)) = true := by
    simp [hoffset']
  simp only [hsmall, ↓reduceIte]
  rw [ByteArray.size_append]
  simp [ffi.ByteArray.zeroes, ByteArray.size]
  rw [usize_sub_toNat_of_le_32]
  · omega
  · omega

theorem readBytes_offset4_32_size (source : ByteArray) :
    (ByteArray.readBytes source 4 32).size = 32 := by
  exact readBytes_32_size source 4 (by norm_num)

theorem readWithPadding_32_size (source : ByteArray) (addr : Nat) :
    (source.readWithPadding addr 32).size = 32 := by
  unfold ByteArray.readWithPadding
  have hsmall : ¬ 32 ≥ 2 ^ 64 := by norm_num
  simp only [hsmall, ↓reduceIte]
  rw [ByteArray.size_append]
  have hReadLe :
      (source.readWithoutPadding addr 32).size ≤ 32 := by
    unfold ByteArray.readWithoutPadding
    split
    · simp
    · simp [ByteArray.size_extract]
      omega
  have hReadLeData :
      (source.readWithoutPadding addr 32).data.size ≤ 32 := by
    simpa [ByteArray.size] using hReadLe
  simp [ffi.ByteArray.zeroes, ByteArray.size]
  rw [usize_sub_toNat_of_le_32]
  · omega
  · exact hReadLeData

private theorem byteArray_append_zeroes0 (source : ByteArray) :
    source ++ ffi.ByteArray.zeroes (OfNat.ofNat 0) = source := by
  apply ByteArray.ext
  simp [ByteArray.data_append, ffi.ByteArray.zeroes]

private theorem byteArray_extract_zero_32_eq_of_size
    (source : ByteArray)
    (hSize : source.size = 32) :
    source.extract 0 32 = source := by
  apply ByteArray.ext
  simp [ByteArray.data_extract, ByteArray.size] at hSize ⊢
  rw [hSize]
  simp

private theorem byteArray_readWithPadding_zero_32_eq_of_size
    (source : ByteArray)
    (hSize : source.size = 32) :
    source.readWithPadding 0 32 = source := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  have hsmall : ¬ 32 ≥ 2 ^ 64 := by norm_num
  simp only [hsmall, ↓reduceIte]
  have haddr : ¬ 0 ≥ source.size := by omega
  simp only [haddr, ↓reduceIte]
  have hmin : min 32 source.size = 32 := by omega
  simp only [hmin]
  rw [byteArray_extract_zero_32_eq_of_size source hSize]
  apply ByteArray.ext
  have hDataSize : source.data.size = 32 := by
    simpa [ByteArray.size] using hSize
  simp [ByteArray.data_append, ByteArray.size, ffi.ByteArray.zeroes]
  rw [usize_sub_toNat_of_le_32]
  · omega
  · omega

private theorem byteArray_write_empty_zero_32_eq_of_size
    (source : ByteArray)
    (hSize : source.size = 32) :
    source.write 0 ByteArray.empty 0 32 = source := by
  unfold ByteArray.write
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  have hSourceAddr : ¬ 0 ≥ source.size := by omega
  simp only [hSourceAddr, ↓reduceIte]
  have hPractical : min 32 (source.size - 0) = 32 := by omega
  have hEnd : min ByteArray.empty.size (0 + 32) = 0 := by simp
  have hDestPadding : 0 - ByteArray.empty.size = 0 := by simp
  simp only [hPractical, hEnd, hDestPadding]
  apply ByteArray.ext
  simp [ByteArray.data_copySlice, ByteArray.size, ffi.ByteArray.zeroes] at hSize ⊢
  exact Or.inr (by omega)

/-- A full-word memory write to empty memory at offset zero is returned
    byte-for-byte by `readWithPadding 0 32`. This is the byte-array core of the
    native `mstore(0, x); return(0, 32)` exact-return proof. -/
theorem byteArray_write_empty_zero_32_readWithPadding_eq_of_size
    (source : ByteArray)
    (hSize : source.size = 32) :
    (source.write 0 ByteArray.empty 0 32).readWithPadding 0 32 = source := by
  rw [byteArray_write_empty_zero_32_eq_of_size source hSize]
  exact byteArray_readWithPadding_zero_32_eq_of_size source hSize

elab "apply_evmyul_toBytes_uint256_length_le" : tactic => do
  let theoremName :=
    Name.str
      (Name.str
        (Name.num
          (Name.str (Name.str (Name.str .anonymous "_private") "EvmYul") "UInt256")
          0)
        "EvmYul")
      "toBytes'_UInt256_le"
  let goals ← (← getMainGoal).apply (mkConst theoremName)
  replaceMainGoal goals

private theorem toBytesBigEndian_uint256_length_le
    {n : Nat} (h : n < EvmYul.UInt256.size) :
    (EvmYul.toBytesBigEndian n).length ≤ 32 := by
  unfold EvmYul.toBytesBigEndian
  simp
  apply_evmyul_toBytes_uint256_length_le
  exact h

private theorem list_toByteArray_loop_size (bytes : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop bytes acc).size = acc.size + bytes.length := by
  induction bytes generalizing acc with
  | nil =>
      simp [List.toByteArray.loop]
  | cons _ bytes ih =>
      simp [List.toByteArray.loop, ih, Nat.add_assoc]
      omega

private theorem list_toByteArray_loop_data_toList (bytes : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop bytes acc).data.toList = acc.data.toList ++ bytes := by
  induction bytes generalizing acc with
  | nil =>
      simp [List.toByteArray.loop]
  | cons _ bytes ih =>
      simp [List.toByteArray.loop, ih, List.append_assoc]

private theorem list_toByteArray_size (bytes : List UInt8) :
    bytes.toByteArray.size = bytes.length := by
  unfold List.toByteArray
  rw [list_toByteArray_loop_size]
  simp

theorem list_toByteArray_data_toList (bytes : List UInt8) :
    bytes.toByteArray.data.toList = bytes := by
  unfold List.toByteArray
  rw [list_toByteArray_loop_data_toList]
  simp

theorem uint256_toByteArray_size (value : EvmYul.UInt256) :
    value.toByteArray.size = 32 := by
  have hBytesSize :
      (EvmYul.toBytesBigEndian value.toNat).toByteArray.data.size =
        (EvmYul.toBytesBigEndian value.toNat).length := by
    simpa [ByteArray.size] using
      list_toByteArray_size (EvmYul.toBytesBigEndian value.toNat)
  have hLen : (EvmYul.toBytesBigEndian value.toNat).length ≤ 32 :=
    toBytesBigEndian_uint256_length_le (n := value.toNat) value.val.isLt
  unfold EvmYul.UInt256.toByteArray BE
  rw [ByteArray.size_append]
  simp [ffi.ByteArray.zeroes, ByteArray.size]
  rw [hBytesSize]
  rw [usize_sub_toNat_of_le_32]
  · omega
  · exact hLen

theorem initialState_calldataReadWord_arg0Bytes
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    let bytes := ByteArray.readBytes
      (initialState contract tx storage observableSlots).toState.executionEnv.calldata 4 32
    bytes.data.toList =
      List.ofFn (fun i : Fin 32 =>
        UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)) := by
  intro bytes
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 32
  · have hleft : bytes.data.toList[i]? =
        some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
      exact byteArray_data_toList_get?_of_get? bytes i _
        (by
          dsimp [bytes]
          exact initialState_calldataReadWord_arg0Byte contract tx storage
            observableSlots arg rest hArgs i hi)
    have hright :
        (List.ofFn (fun i : Fin 32 =>
          UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)))[i]? =
        some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
      rw [List.getElem?_ofFn]
      simp only [hi, ↓reduceDIte]
    rw [hleft, hright]
  · have hleft : bytes.data.toList[i]? = none := by
      have hlen : bytes.data.toList.length = 32 := by
        have hsize := readBytes_offset4_32_size
          (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        simpa [bytes, ByteArray.size] using hsize
      exact List.getElem?_eq_none (by omega)
    have hright :
        (List.ofFn (fun i : Fin 32 =>
          UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)))[i]? = none := by
      exact List.getElem?_eq_none (by simp; omega)
    rw [hleft, hright]

/-- Native `readBytes` returns the exact 32-byte big-endian representation of
    any present aligned ABI argument word. -/
theorem initialState_calldataReadWord_argBytes_of_drop_eq_cons
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (idx arg : Nat)
    (rest : List Nat)
    (hdrop : tx.args.drop idx = arg :: rest)
    (hoffset : 4 + 32 * idx < 2 ^ 64) :
    let bytes := ByteArray.readBytes
      (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        (4 + 32 * idx) 32
    bytes.data.toList =
      List.ofFn (fun i : Fin 32 =>
        UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)) := by
  intro bytes
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 32
  · have hleft : bytes.data.toList[i]? =
        some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
      exact byteArray_data_toList_get?_of_get? bytes i _
        (by
          dsimp [bytes]
          exact initialState_calldataReadWord_argByte_of_drop_eq_cons
            contract tx storage observableSlots idx arg rest hdrop hoffset i hi)
    have hright :
        (List.ofFn (fun i : Fin 32 =>
          UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)))[i]? =
        some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
      rw [List.getElem?_ofFn]
      simp only [hi, ↓reduceDIte]
    rw [hleft, hright]
  · have hleft : bytes.data.toList[i]? = none := by
      have hlen : bytes.data.toList.length = 32 := by
        have hsize := readBytes_32_size
          (initialState contract tx storage observableSlots).toState.executionEnv.calldata
          (4 + 32 * idx) hoffset
        simpa [bytes, ByteArray.size] using hsize
      exact List.getElem?_eq_none (by omega)
    have hright :
        (List.ofFn (fun i : Fin 32 =>
          UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)))[i]? = none := by
      exact List.getElem?_eq_none (by simp; omega)
    rw [hleft, hright]

/-- Native `calldataload(4)` decodes the first aligned ABI argument word from
    the bridged calldata exactly as a `UInt256`, i.e. modulo the EVM word size. -/
theorem initialState_calldataload4_arg0_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    EvmYul.UInt256.toNat
      (EvmYul.State.calldataload
        (initialState contract tx storage observableSlots).toState
        (EvmYul.UInt256.ofNat 4)) =
      arg % EvmYul.UInt256.size := by
  let bytes := ByteArray.readBytes
    (initialState contract tx storage observableSlots).toState.executionEnv.calldata 4 32
  have hbytes :=
    initialState_calldataReadWord_arg0Bytes contract tx storage observableSlots
      arg rest hArgs
  unfold EvmYul.State.calldataload EvmYul.uInt256OfByteArray
  rw [show (EvmYul.UInt256.ofNat 4).toNat = 4 by
    change (Fin.ofNat EvmYul.UInt256.size 4).val = 4
    simp [Fin.ofNat]
    norm_num [EvmYul.UInt256.size]]
  rw [show
      (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        4 32).data.toList =
        bytes.data.toList by rfl]
  rw [hbytes]
  change EvmYul.UInt256.toNat
      (EvmYul.UInt256.ofNat
        (EvmYul.fromBytes'
          ((List.ofFn fun i : Fin 32 =>
            UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)).reverse))) =
    arg % EvmYul.UInt256.size
  rw [fromBytes'_argWordBytes arg]
  exact uint256_ofNat_toNat_of_lt (arg % EvmYul.UInt256.size)
    (Nat.mod_lt _ (by norm_num [EvmYul.UInt256.size]))

/-- Native `calldataload(4)` decodes the first aligned ABI argument as the
    exact EVM word used by the state bridge. -/
theorem initialState_calldataload4_arg0_word
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    EvmYul.State.calldataload
        (initialState contract tx storage observableSlots).toState
        (EvmYul.UInt256.ofNat 4) =
      natToUInt256 arg := by
  apply uint256_eq_of_toNat_eq
  rw [initialState_calldataload4_arg0_value contract tx storage
    observableSlots arg rest hArgs]
  change arg % EvmYul.UInt256.size =
    (Fin.ofNat EvmYul.UInt256.size arg).val
  simp [Fin.ofNat]

/-- Native `calldataload(4 + 32*idx)` decodes a present aligned ABI argument
    word from bridged calldata exactly as a `UInt256`, modulo the EVM word
    size. -/
theorem initialState_calldataload_aligned_arg_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (idx arg : Nat)
    (rest : List Nat)
    (hdrop : tx.args.drop idx = arg :: rest)
    (hoffset : 4 + 32 * idx < 2 ^ 64) :
    EvmYul.UInt256.toNat
      (EvmYul.State.calldataload
        (initialState contract tx storage observableSlots).toState
        (EvmYul.UInt256.ofNat (4 + 32 * idx))) =
      arg % EvmYul.UInt256.size := by
  let bytes := ByteArray.readBytes
    (initialState contract tx storage observableSlots).toState.executionEnv.calldata
      (4 + 32 * idx) 32
  have hbytes :=
    initialState_calldataReadWord_argBytes_of_drop_eq_cons contract tx storage
      observableSlots idx arg rest hdrop hoffset
  have hoffset256 : 4 + 32 * idx < EvmYul.UInt256.size := by
    have h64 : 2 ^ 64 < EvmYul.UInt256.size := by
      norm_num [EvmYul.UInt256.size]
    exact Nat.lt_trans hoffset h64
  unfold EvmYul.State.calldataload EvmYul.uInt256OfByteArray
  rw [uint256_ofNat_toNat_of_lt (4 + 32 * idx) hoffset256]
  rw [show
      (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        (4 + 32 * idx) 32).data.toList =
        bytes.data.toList by rfl]
  rw [hbytes]
  change EvmYul.UInt256.toNat
      (EvmYul.UInt256.ofNat
        (EvmYul.fromBytes'
          ((List.ofFn fun i : Fin 32 =>
            UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)).reverse))) =
    arg % EvmYul.UInt256.size
  rw [fromBytes'_argWordBytes arg]
  exact uint256_ofNat_toNat_of_lt (arg % EvmYul.UInt256.size)
    (Nat.mod_lt _ (by norm_num [EvmYul.UInt256.size]))

/-- Native `calldataload(4 + 32*idx)` decodes a present aligned ABI argument
    as the exact EVM word used by the state bridge. -/
theorem initialState_calldataload_aligned_arg_word
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (idx arg : Nat)
    (rest : List Nat)
    (hdrop : tx.args.drop idx = arg :: rest)
    (hoffset : 4 + 32 * idx < 2 ^ 64) :
    EvmYul.State.calldataload
        (initialState contract tx storage observableSlots).toState
        (EvmYul.UInt256.ofNat (4 + 32 * idx)) =
      natToUInt256 arg := by
  apply uint256_eq_of_toNat_eq
  rw [initialState_calldataload_aligned_arg_value contract tx storage
    observableSlots idx arg rest hdrop hoffset]
  change arg % EvmYul.UInt256.size =
    (Fin.ofNat EvmYul.UInt256.size arg).val
  simp [Fin.ofNat]

/-- Native selector decoding agrees with the interpreter selector by reducing
    EVMYulLean `calldataload(0) >>> 224` to the four ABI selector bytes in
    the initial bridged calldata. -/
theorem initialState_selectorExpr_native_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (initialState contract tx storage observableSlots).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift)) =
      tx.functionSelector % Compiler.Constants.selectorModulus := by
  let bytes := ByteArray.readBytes
    (initialState contract tx storage observableSlots).toState.executionEnv.calldata 0 32
  have hprefix :=
    initialState_calldataReadWord_selectorPrefix contract tx storage observableSlots
  have hlen : bytes.data.toList.length = 32 := by
    have hsize := readBytes_zero_32_size
      (initialState contract tx storage observableSlots).toState.executionEnv.calldata
    simpa [bytes, ByteArray.size] using hsize
  have htailLen : (bytes.data.toList.drop 4).length = 28 := by
    simp [hlen]
  unfold EvmYul.State.calldataload EvmYul.uInt256OfByteArray
  rw [show (EvmYul.UInt256.ofNat 0).toNat = 0 by
    change (Fin.ofNat EvmYul.UInt256.size 0).val = 0
    simp]
  rw [uint256_shiftRight_224_ofNat_toNat]
  · rw [show (ByteArray.readBytes
          (initialState contract tx storage observableSlots).toState.executionEnv.calldata
          0 32).data.toList.reverse =
        bytes.data.toList.reverse by rfl]
    rw [hprefix]
    exact fromBytes'_selectorPrefix_shift tx.functionSelector
      (bytes.data.toList.drop 4) htailLen
  · have hlt := fromBytes'_lt bytes.data.toList.reverse
    have hrevLen : bytes.data.toList.reverse.length = 32 := by
      simp [hlen]
    simpa [hrevLen, EvmYul.UInt256.size] using hlt

theorem initialState_selectorExpr_native_value_of_readBytes_size
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (_hReadBytesSize :
      ∀ source : ByteArray, (ByteArray.readBytes source 0 32).size = 32) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (initialState contract tx storage observableSlots).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift)) =
      tx.functionSelector % Compiler.Constants.selectorModulus :=
  initialState_selectorExpr_native_value contract tx storage observableSlots

theorem initialState_selectorExpr_native_uint256
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.SharedState.toState
            (initialState contract tx storage observableSlots).sharedState)
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift) =
      EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus) := by
  apply uint256_eq_of_toNat_eq
  rw [show EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.SharedState.toState
            (initialState contract tx storage observableSlots).sharedState)
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift)) =
      tx.functionSelector % Compiler.Constants.selectorModulus by
    simpa [EvmYul.Yul.State.toState] using
      initialState_selectorExpr_native_value contract tx storage observableSlots]
  rw [uint256_ofNat_toNat_of_lt]
  have hmod :
      tx.functionSelector % Compiler.Constants.selectorModulus <
        Compiler.Constants.selectorModulus := by
    exact Nat.mod_lt _ (by norm_num [Compiler.Constants.selectorModulus])
  have hsel :
      Compiler.Constants.selectorModulus < EvmYul.UInt256.size := by
    norm_num [Compiler.Constants.selectorModulus, EvmYul.UInt256.size]
  exact Nat.lt_trans hmod hsel

/-- The native lowerer maps the generated dispatcher selector expression to
    EVMYulLean's primitive `SHR(CALLDATALOAD(0), 224)` shape. -/
theorem lowerExprNative_selectorExpr :
    Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr =
      .Call (.inl (EvmYul.Operation.SHR : EvmYul.Operation .Yul))
        [.Lit (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift),
         .Call (.inl (EvmYul.Operation.CALLDATALOAD : EvmYul.Operation .Yul))
          [.Lit (EvmYul.UInt256.ofNat 0)]] := by
  rw [show Compiler.Proofs.YulGeneration.selectorExpr =
      YulExpr.call "shr"
        [YulExpr.lit Compiler.Constants.selectorShift,
         YulExpr.call "calldataload" [YulExpr.lit 0]] by rfl]
  rw [Backends.lowerExprNative_call_runtimePrimOp "shr" _
    (EvmYul.Operation.SHR : EvmYul.Operation .Yul) (by rfl)]
  change EvmYul.Yul.Ast.Expr.Call (Sum.inl EvmYul.Operation.SHR)
      [Backends.lowerExprNative (YulExpr.lit Compiler.Constants.selectorShift),
       Backends.lowerExprNative (YulExpr.call "calldataload" [YulExpr.lit 0])] = _
  rw [Backends.lowerExprNative_call_runtimePrimOp "calldataload" _
    (EvmYul.Operation.CALLDATALOAD : EvmYul.Operation .Yul) (by rfl)]
  simp [Backends.lowerExprNative]

end Compiler.Proofs.YulGeneration.Backends.Native
