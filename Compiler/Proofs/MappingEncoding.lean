/-
  Shared mapping slot encoding for proof interpreters.

  We model EVM mapping slots as tagged values so the interpreters can route
  `sload`/`sstore` to the mapping table instead of flat storage.
-//

namespace Compiler.Proofs

/-- EVM word modulus (2^256). -/
def evmModulus : Nat := 2 ^ 256

/-- Tag values above the EVM word range so mapping slots never collide. -/
def mappingTag : Nat := evmModulus

/-- Encode a mapping slot (base slot + key) into a tagged word. -/
def encodeMappingSlot (baseSlot key : Nat) : Nat :=
  mappingTag + (baseSlot % evmModulus) * evmModulus + (key % evmModulus)

/-- Decode a tagged mapping slot back into (base slot, key). -/
def decodeMappingSlot (slot : Nat) : Option (Nat × Nat) :=
  if slot < mappingTag then
    none
  else
    let raw := slot - mappingTag
    some (raw / evmModulus, raw % evmModulus)

end Compiler.Proofs
