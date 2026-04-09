import EvmYul
import Compiler.Constants
import Compiler.Keccak.SpongeProperties

/-!
# Keccak Output Bound

Proves that `fromByteArrayBigEndian` applied to any ≤32-byte array
produces a value < 2^256 (= `evmModulus`).

Combined with `KeccakEngine.keccak256_size`, this eliminates the need for
the `solidityMappingSlot_lt_evmModulus` axiom.

## Proof architecture

```
keccak256_size : (keccak256 data).size = 32
  +
fromByteArrayBigEndian_lt_of_size : ba.size ≤ 32 → fromByteArrayBigEndian ba < 2^256
  =
solidityMappingSlot_lt_evmModulus : solidityMappingSlot baseSlot key < evmModulus
```
-/

namespace Compiler.Proofs

/-! ### ByteArray.toList length -/

set_option maxHeartbeats 400000 in
private theorem ByteArray.toList.loop_length (ba : ByteArray) (i : Nat) (acc : List UInt8)
    (hi : i ≤ ba.size) :
    (ByteArray.toList.loop ba i acc).length = (ba.size - i) + acc.length := by
  induction i, acc using ByteArray.toList.loop.induct ba with
  | case1 i acc hlt ih =>
    unfold ByteArray.toList.loop
    simp [hlt]
    rw [ih (Nat.le_of_lt_succ (by omega))]
    simp [List.length_cons]
    omega
  | case2 i acc hge =>
    unfold ByteArray.toList.loop
    simp [show ¬(i < ba.size) from hge]
    omega

private theorem ByteArray.toList_length (ba : ByteArray) : ba.toList.length = ba.size := by
  unfold ByteArray.toList
  rw [ByteArray.toList.loop_length ba 0 [] (Nat.zero_le _)]
  simp

/-! ### ByteArray big-endian bound -/

private theorem fromBytes'_lt (bs : List UInt8) :
    EvmYul.fromBytes' bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => simp [EvmYul.fromBytes']
  | cons b bs ih =>
    unfold EvmYul.fromBytes'
    have hb := b.toFin.isLt
    simp only [List.length_cons, Nat.mul_succ, Nat.add_comm, Nat.pow_add]
    have hsub :=
      Nat.add_le_of_le_sub
        (Nat.one_le_pow _ _ (by decide))
        (Nat.le_sub_one_of_lt ih)
    linarith

private theorem fromBytes'_lt_of_length_le (bs : List UInt8) (n : Nat)
    (h : bs.length ≤ n) :
    EvmYul.fromBytes' bs < 2 ^ (8 * n) := by
  calc EvmYul.fromBytes' bs
      < 2 ^ (8 * bs.length) := fromBytes'_lt bs
    _ ≤ 2 ^ (8 * n) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 8 h)

theorem fromByteArrayBigEndian_lt_of_size (ba : ByteArray)
    (h : ba.size ≤ 32) :
    EvmYul.fromByteArrayBigEndian ba < Compiler.Constants.evmModulus := by
  unfold EvmYul.fromByteArrayBigEndian EvmYul.fromBytesBigEndian Compiler.Constants.evmModulus
  simp only [Function.comp]
  show EvmYul.fromBytes' ba.toList.reverse < 2 ^ (8 * 32)
  apply fromBytes'_lt_of_length_le
  simp only [List.length_reverse]
  rw [ByteArray.toList_length]
  exact h

end Compiler.Proofs
