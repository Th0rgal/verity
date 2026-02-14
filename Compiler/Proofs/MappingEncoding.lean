/-
  Shared mapping slot encoding for proof interpreters.

  We model EVM mapping slots as tagged values so the interpreters can route
  `sload`/`sstore` to the mapping table instead of flat storage.
-/

namespace Compiler.Proofs

/-- EVM word modulus (2^256). -/
def evmModulus : Nat := 2 ^ 256

/-- Tag values above the EVM word range so mapping slots never collide. -/
def mappingTag : Nat := evmModulus

/-- Preserve tagged base slots for nested mappings; otherwise normalize to EVM word range. -/
def normalizeMappingBaseSlot (baseSlot : Nat) : Nat :=
  if baseSlot < mappingTag then
    baseSlot % evmModulus
  else
    baseSlot

/-- Encode a mapping slot (base slot + key) into a tagged word. -/
def encodeMappingSlot (baseSlot key : Nat) : Nat :=
  mappingTag + (normalizeMappingBaseSlot baseSlot) * evmModulus + (key % evmModulus)

/-- Decode a tagged mapping slot back into (base slot, key). -/
def decodeMappingSlot (slot : Nat) : Option (Nat × Nat) :=
  if slot < mappingTag then
    none
  else
    let raw := slot - mappingTag
    some (raw / evmModulus, raw % evmModulus)

/-! ## Nested Mapping Helper

EVM nested mappings are effectively a mapping whose base slot is itself
another mapping slot. This helper makes that structure explicit so
proofs and specs can name it directly.
-/

/-- Encode a nested mapping slot (base slot + key1 + key2). -/
def encodeNestedMappingSlot (baseSlot key1 key2 : Nat) : Nat :=
  encodeMappingSlot (encodeMappingSlot baseSlot key1) key2

end Compiler.Proofs
