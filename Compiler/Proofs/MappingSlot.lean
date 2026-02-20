import Compiler.Proofs.MappingEncoding

namespace Compiler.Proofs

/-!
Mapping slot abstraction used by proof interpreters.

Today this delegates to the tagged encoding model in `MappingEncoding.lean`.
When issue #259 is implemented, only this module should need backend changes.
-/

/-- Active proof-model mapping slot encoding backend. -/
def abstractMappingSlot (baseSlot key : Nat) : Nat :=
  encodeMappingSlot baseSlot key

/-- Active proof-model mapping slot tag sentinel (backend-specific). -/
def abstractMappingTag : Nat :=
  mappingTag

/-- Active proof-model mapping slot decoder backend. -/
def abstractDecodeMappingSlot (slot : Nat) : Option (Nat × Nat) :=
  decodeMappingSlot slot

/-- Active proof-model nested mapping slot helper. -/
def abstractNestedMappingSlot (baseSlot key1 key2 : Nat) : Nat :=
  abstractMappingSlot (abstractMappingSlot baseSlot key1) key2

@[simp] theorem abstractMappingSlot_eq_encode (baseSlot key : Nat) :
    abstractMappingSlot baseSlot key = encodeMappingSlot baseSlot key := rfl

@[simp] theorem abstractMappingTag_eq_mappingTag :
    abstractMappingTag = mappingTag := rfl

@[simp] theorem abstractDecodeMappingSlot_eq_decode (slot : Nat) :
    abstractDecodeMappingSlot slot = decodeMappingSlot slot := rfl

@[simp] theorem abstractNestedMappingSlot_eq_encodeNested (baseSlot key1 key2 : Nat) :
    abstractNestedMappingSlot baseSlot key1 key2 = encodeNestedMappingSlot baseSlot key1 key2 := by
  simp [abstractNestedMappingSlot, encodeNestedMappingSlot]

end Compiler.Proofs
