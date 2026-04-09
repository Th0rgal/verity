import Compiler.Keccak.Sponge

/-!
# Keccak Sponge Output Properties

Structural lemmas about the kernel-computable Keccak-256 implementation.
These enable eliminating the `solidityMappingSlot_lt_evmModulus` axiom
by proving that keccak256 always outputs exactly 32 bytes.

## Strategy

1. `wordToBytesLE_size`: each 64-bit word encodes to exactly 8 bytes
2. `squeeze256_size`: squeezing 4 words produces exactly 32 bytes
3. `keccak256_size`: the full hash always returns a 32-byte `ByteArray`

Once `keccak256_size` is proved, `fromByteArrayBigEndian` of a 32-byte
array is trivially < 2^256, eliminating the need for the mapping-slot axiom.
-/

namespace KeccakEngine

/-! ### Word-to-bytes size lemma -/

theorem wordToBytesLE_size (word : BitVec 64) :
    (wordToBytesLE word).size = 8 := by
  simp [wordToBytesLE]

/-! ### Squeeze output size lemma -/

theorem squeeze256_size (state : Array (BitVec 64)) :
    (squeeze256 state).size = 32 := by
  simp [squeeze256, ByteArray.size, Array.size_append, wordToBytesLE_size]

/-! ### Full keccak256 output size -/

theorem keccak256_core_size (data : ByteArray) (variant : HashVariant) :
    (keccak256_core data variant).size = 32 := by
  unfold keccak256_core; exact squeeze256_size _

theorem keccak256_size (data : ByteArray) :
    (keccak256 data).size = 32 := by
  exact keccak256_core_size data .ethereum

theorem sha3_256_size (data : ByteArray) :
    (sha3_256 data).size = 32 := by
  exact keccak256_core_size data .nist

end KeccakEngine
