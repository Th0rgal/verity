import Init.Data.BitVec
import Compiler.Keccak.Circuit
import Compiler.Keccak.CircuitData

/-!
# SHA-3 Sponge Construction (Unrolled Engine)

This module implements the Keccak sponge construction. It relies on a pre-generated,
unrolled static circuit (`CircuitData.lean`) to perform the Keccak-f[1600] permutation.
This architectural choice bypasses Lean's elaborator memory limits, allowing for fully
computable Keccak hashes (and EVM selectors) at compile-time without axioms.
-/

namespace KeccakEngine

/--
Safely reads 1 byte from a `ByteArray`.
Returns 0 if out of bounds, avoiding runtime `panic!` during kernel evaluation.
-/
@[always_inline, inline]
def safeGetByte (bytes : ByteArray) (idx : Nat) : BitVec 64 :=
  let b := bytes[idx]? |>.getD 0
  BitVec.ofNat 64 b.toNat

/--
Reads 8 bytes from `ByteArray` starting at `offset` into a 64-bit word
using Little-Endian encoding.
-/
@[always_inline, inline]
def bytesToWordLE (bytes : ByteArray) (offset : Nat) : BitVec 64 :=
  let b0 := safeGetByte bytes (offset + 0)
  let b1 := safeGetByte bytes (offset + 1)
  let b2 := safeGetByte bytes (offset + 2)
  let b3 := safeGetByte bytes (offset + 3)
  let b4 := safeGetByte bytes (offset + 4)
  let b5 := safeGetByte bytes (offset + 5)
  let b6 := safeGetByte bytes (offset + 6)
  let b7 := safeGetByte bytes (offset + 7)

  b0 ||| (b1 <<< 8)  ||| (b2 <<< 16) ||| (b3 <<< 24) |||
  (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

/-- Safely sets a value in the state array. -/
@[always_inline, inline]
def safeSet (arr : Array (BitVec 64)) (idx : Nat) (val : BitVec 64) : Array (BitVec 64) :=
  arr.set! idx val

/-- Absorbs exactly 136 bytes (17 words) into the Keccak state. -/
def absorbBlock (state : Array (BitVec 64)) (bytes : ByteArray) (offset : Nat) : Array (BitVec 64) :=
  let absorbWord (s : Array (BitVec 64)) (i : Nat) :=
    let word := bytesToWordLE bytes (offset + i * 8)
    let oldWord := s.getD i 0#64
    safeSet s i (oldWord ^^^ word)

  let indices := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  indices.foldl absorbWord state

/-- Domain separation suffixes for Keccak variants. -/
inductive HashVariant where
  | ethereum
  | nist
  deriving Repr, Inhabited, DecidableEq

/-- Returns the starting padding byte: `0x01` for Ethereum, `0x06` for NIST. -/
@[always_inline, inline]
def domainSuffix (v : HashVariant) : UInt8 :=
  match v with
  | .ethereum => 0x01
  | .nist     => 0x06

/-- Pads the message tail (0 to 135 bytes) to a full 136-byte block. -/
def padBlock (leftover : ByteArray) (variant : HashVariant) : ByteArray :=
  let rate := 136
  let arr1 := leftover.data.push (domainSuffix variant)
  let padLen := rate - arr1.size
  let arr2 := arr1 ++ Array.replicate padLen 0
  let lastIdx := rate - 1
  let lastVal := arr2[lastIdx]? |>.getD 0
  let arr3 := arr2.set! lastIdx (lastVal ||| 0x80)
  ⟨arr3⟩

/-- Kernel-friendly evaluation of a single bitwise instruction. -/
@[always_inline, inline]
def kernelEvalInstr (mem : Array (BitVec 64)) (inst : Instr) : Array (BitVec 64) :=
  match inst with
  | .xor a b       => mem.push (mem.getD a 0#64 ^^^ mem.getD b 0#64)
  | .xor_const a c => mem.push (mem.getD a 0#64 ^^^ c)
  | .and a b       => mem.push (mem.getD a 0#64 &&& mem.getD b 0#64)
  | .not a         => mem.push (~~~mem.getD a 0#64)
  | .rotl a n      => mem.push ((mem.getD a 0#64).rotateLeft n)

/--
Executes the Keccak-f[1600] permutation.
Processes the 24 unrolled round chunks sequentially to manage elaborator memory.
-/
def keccakF1600 (state : Array (BitVec 64)) : Array (BitVec 64) :=
  let s1  := sha3_round_0.foldl kernelEvalInstr state
  let s2  := sha3_round_1.foldl kernelEvalInstr s1
  let s3  := sha3_round_2.foldl kernelEvalInstr s2
  let s4  := sha3_round_3.foldl kernelEvalInstr s3
  let s5  := sha3_round_4.foldl kernelEvalInstr s4
  let s6  := sha3_round_5.foldl kernelEvalInstr s5
  let s7  := sha3_round_6.foldl kernelEvalInstr s6
  let s8  := sha3_round_7.foldl kernelEvalInstr s7
  let s9  := sha3_round_8.foldl kernelEvalInstr s8
  let s10 := sha3_round_9.foldl kernelEvalInstr s9
  let s11 := sha3_round_10.foldl kernelEvalInstr s10
  let s12 := sha3_round_11.foldl kernelEvalInstr s11
  let s13 := sha3_round_12.foldl kernelEvalInstr s12
  let s14 := sha3_round_13.foldl kernelEvalInstr s13
  let s15 := sha3_round_14.foldl kernelEvalInstr s14
  let s16 := sha3_round_15.foldl kernelEvalInstr s15
  let s17 := sha3_round_16.foldl kernelEvalInstr s16
  let s18 := sha3_round_17.foldl kernelEvalInstr s17
  let s19 := sha3_round_18.foldl kernelEvalInstr s18
  let s20 := sha3_round_19.foldl kernelEvalInstr s19
  let s21 := sha3_round_20.foldl kernelEvalInstr s20
  let s22 := sha3_round_21.foldl kernelEvalInstr s21
  let s23 := sha3_round_22.foldl kernelEvalInstr s22
  let memTape := sha3_round_23.foldl kernelEvalInstr s23

  let extractWord (s : Array (BitVec 64)) (i : Nat) :=
    let v_idx := final_vstate.getD i 0
    s.set! i (memTape.getD v_idx 0#64)

  let indices := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24]
  indices.foldl extractWord (Array.replicate 25 (0#64))

/--
Main Sponge Loop.
Mathematically verified termination using `omega` to prove strict reduction of remaining bytes.
-/
def spongeLoop (state : Array (BitVec 64)) (data : ByteArray) (offset : Nat) (variant : HashVariant) : Array (BitVec 64) :=
  let remaining := data.size - offset
  if h : remaining >= 136 then
    let state' := absorbBlock state data offset
    let state'' := keccakF1600 state'
    have proof_of_termination : data.size - (offset + 136) < data.size - offset := by omega
    spongeLoop state'' data (offset + 136) variant
  else
    let leftover := data.extract offset data.size
    let padded := padBlock leftover variant
    let state' := absorbBlock state padded 0
    keccakF1600 state'
termination_by data.size - offset

/-- Converts a 64-bit word to 8 bytes (Little-Endian). -/
def wordToBytesLE (word : BitVec 64) : Array UInt8 :=
  #[
    UInt8.ofNat (word &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 8) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 16) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 24) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 32) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 40) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 48) &&& 0xFF#64).toNat,
    UInt8.ofNat ((word >>> 56) &&& 0xFF#64).toNat
  ]

/-- Extracts the first 32 bytes (256 bits) from the final state. -/
def squeeze256 (state : Array (BitVec 64)) : ByteArray :=
  let b0 := wordToBytesLE (state.getD 0 0#64)
  let b1 := wordToBytesLE (state.getD 1 0#64)
  let b2 := wordToBytesLE (state.getD 2 0#64)
  let b3 := wordToBytesLE (state.getD 3 0#64)
  ⟨b0 ++ b1 ++ b2 ++ b3⟩

def keccak256_core (data : ByteArray) (variant : HashVariant) : ByteArray :=
  let initialState := Array.replicate 25 (0#64)
  let finalState := spongeLoop initialState data 0 variant
  squeeze256 finalState

/-- Computes the Keccak-256 hash (Ethereum standard). -/
def keccak256 (data : ByteArray) : ByteArray :=
  keccak256_core data .ethereum

/-- Computes the SHA3-256 hash (NIST standard). -/
def sha3_256 (data : ByteArray) : ByteArray :=
  keccak256_core data .nist

/-- Computes the Keccak-256 hash of a UTF-8 encoded string. -/
def keccak256_str (s : String) : ByteArray :=
  keccak256 s.toUTF8

/-- Extracts the 4-byte EVM function selector from a hash (Big-Endian). -/
def getSelector (hash : ByteArray) : BitVec 32 :=
  let b0 := BitVec.ofNat 32 (hash[0]? |>.getD 0).toNat
  let b1 := BitVec.ofNat 32 (hash[1]? |>.getD 0).toNat
  let b2 := BitVec.ofNat 32 (hash[2]? |>.getD 0).toNat
  let b3 := BitVec.ofNat 32 (hash[3]? |>.getD 0).toNat
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Computes the 4-byte EVM selector directly from a function signature string. -/
def keccak256_selector (s : String) : BitVec 32 :=
  getSelector (keccak256_str s)

end KeccakEngine
