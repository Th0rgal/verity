/-
  Compiler.CompilationModel.AdtStorageLayout: Storage layout helpers for ADTs

  ADT storage encoding uses a tagged-union layout:
  - Slot 0 (relative): tag byte (uint8, identifies the variant)
  - Slots 1..N (relative): max-width fields in consecutive slots

  The total storage footprint is 1 + max(variant field counts).
  All variants share the same field slots — unused trailing slots
  are simply not read/written for shorter variants.

  (#1727, Phase 5 Steps 5c+5d)
-/
import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

open Compiler.Yul

/-- Look up an ADT type definition by name. -/
def lookupAdtTypeDef (adtTypes : List AdtTypeDef) (name : String) :
    Except String AdtTypeDef :=
  match adtTypes.find? (·.name == name) with
  | some def_ => pure def_
  | none => throw s!"Compilation error: unknown ADT type '{name}'"

/-- Look up a variant within an ADT type definition by name. -/
def lookupAdtVariant (def_ : AdtTypeDef) (variantName : String) :
    Except String AdtVariant :=
  match def_.variants.find? (·.name == variantName) with
  | some v => pure v
  | none => throw s!"Compilation error: unknown variant '{variantName}' in ADT '{def_.name}'"

/-- Maximum number of field slots across all variants. -/
def adtMaxFieldSlots (def_ : AdtTypeDef) : Nat :=
  def_.variants.foldl (fun acc v => max acc v.fields.length) 0

/-- Total storage slots for an ADT: 1 (tag) + max field slots. -/
def adtTotalSlots (def_ : AdtTypeDef) : Nat :=
  1 + adtMaxFieldSlots def_

/-- Find the field within a variant by name and return its 0-based index. -/
def lookupAdtFieldIndex (variant : AdtVariant) (fieldName : String) :
    Except String Nat :=
  match variant.fields.findIdx? (·.name == fieldName) with
  | some idx => pure idx
  | none => throw s!"Compilation error: unknown field '{fieldName}' in variant '{variant.name}'"

/-! ### Yul compilation helpers for ADT storage operations

These generate Yul AST fragments for reading/writing ADT values
stored in contract storage. The caller provides the base slot
(resolved from the contract's field list) and the ADT type info.
-/

/-- Read the tag byte from an ADT's storage slot.
    `baseSlot` is the Yul expression for the ADT field's first slot. -/
def compileAdtTagRead (baseSlot : YulExpr) : YulExpr :=
  -- Tag is stored as a full word in the base slot (mask to uint8)
  YulExpr.call "and" [
    YulExpr.call "sload" [baseSlot],
    YulExpr.lit 0xFF
  ]

/-- Write the tag byte to an ADT's storage base slot. -/
def compileAdtTagWrite (baseSlot : YulExpr) (tagValue : Nat) : YulStmt :=
  YulStmt.expr (YulExpr.call "sstore" [baseSlot, YulExpr.lit tagValue])

/-- Read a field from an ADT variant in storage.
    `baseSlot` is the ADT's first slot, `fieldIndex` is 0-based within the variant.
    Fields occupy slots base+1, base+2, ... -/
def compileAdtFieldRead (baseSlot : YulExpr) (fieldIndex : Nat) : YulExpr :=
  YulExpr.call "sload" [
    YulExpr.call "add" [baseSlot, YulExpr.lit (fieldIndex + 1)]
  ]

/-- Write a field value into an ADT variant's storage slot.
    `baseSlot` is the ADT's first slot, `fieldIndex` is 0-based. -/
def compileAdtFieldWrite (baseSlot : YulExpr) (fieldIndex : Nat)
    (valueExpr : YulExpr) : YulStmt :=
  YulStmt.expr (YulExpr.call "sstore" [
    YulExpr.call "add" [baseSlot, YulExpr.lit (fieldIndex + 1)],
    valueExpr
  ])

end Compiler.CompilationModel
