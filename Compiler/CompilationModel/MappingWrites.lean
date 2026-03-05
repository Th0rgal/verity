import Compiler.CompilationModel.Types
import Compiler.CompilationModel.ValidationHelpers

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

def compileMappingSlotWrite (fields : List Field) (field : String)
    (keyExpr valueExpr : YulExpr) (label : String) (wordOffset : Nat := 0) : Except String (List YulStmt) :=
  if !isMapping fields field then
    throw s!"Compilation error: field '{field}' is not a mapping"
  else
    match findFieldWriteSlots fields field with
    | some slots =>
        match slots with
        | [] =>
            throw s!"Compilation error: internal invariant failure: no write slots for mapping field '{field}' in {label}"
        | [slot] =>
            let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyExpr]
            let writeSlot := if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
            pure [
              YulStmt.expr (YulExpr.call "sstore" [
                writeSlot,
                valueExpr
              ])
            ]
        | _ =>
            let compatSlotExpr := fun (slot : Nat) =>
              let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key"]
              if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
            pure [
              YulStmt.block (
                [YulStmt.let_ "__compat_key" keyExpr, YulStmt.let_ "__compat_value" valueExpr] ++
                slots.map (fun slot =>
                  YulStmt.expr (YulExpr.call "sstore" [
                    compatSlotExpr slot,
                    YulExpr.ident "__compat_value"
                  ]))
              )
            ]
    | none => throw s!"Compilation error: unknown mapping field '{field}' in {label}"

def compileMappingPackedSlotWrite (fields : List Field) (field : String)
    (keyExpr valueExpr : YulExpr) (wordOffset : Nat) (packed : PackedBits)
    (label : String) : Except String (List YulStmt) :=
  if !isMapping fields field then
    throw s!"Compilation error: field '{field}' is not a mapping"
  else if !packedBitsValid packed then
    throw s!"Compilation error: {label} for field '{field}' has invalid packed range offset={packed.offset} width={packed.width}. Require 0 < width <= 256, offset < 256, and offset + width <= 256."
  else
    match findFieldWriteSlots fields field with
    | some slots =>
        match slots with
        | [] =>
            throw s!"Compilation error: internal invariant failure: no write slots for mapping field '{field}' in {label}"
        | [slot] =>
            let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyExpr]
            let writeSlot := if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
            let maskNat := packedMaskNat packed
            let shiftedMaskNat := packedShiftedMaskNat packed
            pure [
              YulStmt.block [
                YulStmt.let_ "__compat_value" valueExpr,
                YulStmt.let_ "__compat_packed" (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit maskNat]),
                YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [writeSlot]),
                YulStmt.let_ "__compat_slot_cleared" (YulExpr.call "and" [
                  YulExpr.ident "__compat_slot_word",
                  YulExpr.call "not" [YulExpr.lit shiftedMaskNat]
                ]),
                YulStmt.expr (YulExpr.call "sstore" [
                  writeSlot,
                  YulExpr.call "or" [
                    YulExpr.ident "__compat_slot_cleared",
                    YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]
                  ]
                ])
              ]
            ]
        | _ =>
            let slotExpr := fun (slot : Nat) =>
              let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key"]
              if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
            let maskNat := packedMaskNat packed
            let shiftedMaskNat := packedShiftedMaskNat packed
            pure [
              YulStmt.block (
                [YulStmt.let_ "__compat_key" keyExpr,
                 YulStmt.let_ "__compat_value" valueExpr,
                 YulStmt.let_ "__compat_packed" (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit maskNat])] ++
                slots.map (fun slot =>
                  YulStmt.block [
                    YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [slotExpr slot]),
                    YulStmt.let_ "__compat_slot_cleared" (YulExpr.call "and" [
                      YulExpr.ident "__compat_slot_word",
                      YulExpr.call "not" [YulExpr.lit shiftedMaskNat]
                    ]),
                    YulStmt.expr (YulExpr.call "sstore" [
                      slotExpr slot,
                      YulExpr.call "or" [
                        YulExpr.ident "__compat_slot_cleared",
                        YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]
                      ]
                    ])
                  ])
              )
            ]
    | none => throw s!"Compilation error: unknown mapping field '{field}' in {label}"

end Compiler.CompilationModel
