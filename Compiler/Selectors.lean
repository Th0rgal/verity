import Compiler.Keccak.Sponge

/-!
# Function Selectors

This module defines function selectors using a kernel-computable Keccak-256
implementation, so selector derivation no longer needs a project axiom.

## Soundness

Function selectors are the first 4 bytes of keccak256(signature). Verity now
computes that hash slice inside Lean's kernel via the vendored unrolled Keccak
engine, while CI continues to cross-check against `solc --hashes` as a
defense-in-depth consistency check.

## References

- Solidity ABI Spec: https://docs.soliditylang.org/en/latest/abi-spec.html#function-selector
- Trust Assumptions: TRUST_ASSUMPTIONS.md
-/

namespace Compiler

/-- Compute the first 4 bytes (32 bits) of keccak256(sig) as a function selector.

**Example**: keccak256("transfer(address,uint256)")[:4] = 0xa9059cbb
-/
def keccak256_first_4_bytes (sig : String) : Nat :=
  (KeccakEngine.keccak256_selector sig).toNat

example : keccak256_first_4_bytes "transfer(address,uint256)" = 0xa9059cbb := by
  native_decide

example : keccak256_first_4_bytes "approve(address,uint256)" = 0x095ea7b3 := by
  native_decide

end Compiler
