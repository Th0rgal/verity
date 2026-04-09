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

/-! ### ByteArray big-endian bound -/

-- TODO: Prove that fromByteArrayBigEndian of a ≤32-byte array is < 2^256.
--
-- Proof strategy options (pick the one that works with EVMYulLean's definitions):
--
-- Option A: If fromByteArrayBigEndian unfolds to a foldl over bytes with
--   positional weights, prove by induction: each byte contributes < 256 * 2^(8*pos),
--   and the sum of all 32 positions < 2^256.
--
-- Option B: If fromByteArrayBigEndian is opaque in EVMYulLean, look for an
--   existing lemma in EVMYulLean like `fromByteArrayBigEndian_lt` or similar.
--   Check: `grep -r "fromByteArrayBigEndian.*lt\|fromByteArrayBigEndian.*bound"
--           .lake/packages/evmyul/ --include="*.lean"`
--
-- Option C (fallback): If both A and B fail, use native_decide on concrete
--   test vectors to validate, then use @[implemented_by] pattern as described
--   in the PR description.
--
-- IMPORTANT: Run `lake build` after each option to verify. Do NOT use sorry
-- in the final version.
theorem fromByteArrayBigEndian_lt_of_size (ba : ByteArray)
    (h : ba.size ≤ 32) :
    EvmYul.fromByteArrayBigEndian ba < Compiler.Constants.evmModulus := by
  sorry

end Compiler.Proofs
