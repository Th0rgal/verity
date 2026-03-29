import Compiler.CompilationModel.ExpressionCompile
import Compiler.CompilationModel.AbiTypeLayout
import Compiler.CompilationModel.IssueRefs
import Compiler.CompilationModel.MappingWrites
import Compiler.CompilationModel.ValidationHelpers

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

private def validateDynamicArrayField (fields : List Field) (field : String) :
    Except String (Nat × StorageArrayElemType) := do
  match findFieldWithResolvedSlot fields field with
  | some (f, slot) =>
      match f.ty with
      | .dynamicArray elemType =>
          pure (slot, elemType)
      | _ =>
          throw s!"Compilation error: field '{field}' is not a storage dynamic array"
  | none =>
      throw s!"Compilation error: unknown storage field '{field}'"

def compilePackedStorageWrite (writeSlot valueExpr : YulExpr) (packed : PackedBits) :
    List YulStmt :=
  let maskNat := packedMaskNat packed
  let shiftedMaskNat := packedShiftedMaskNat packed
  [
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

def compileCompatPackedStorageWrites (writeSlots : List YulExpr) (valueExpr : YulExpr)
    (packed : PackedBits) : List YulStmt :=
  let maskNat := packedMaskNat packed
  let shiftedMaskNat := packedShiftedMaskNat packed
  [
    YulStmt.block (
      [YulStmt.let_ "__compat_value" valueExpr,
       YulStmt.let_ "__compat_packed" (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit maskNat])] ++
      writeSlots.map (fun writeSlot =>
        YulStmt.block [
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
        ])
    )
  ]

def compileSetStorage (fields : List Field) (dynamicSource : DynamicDataSource)
    (field : String) (value : Expr) (requireAddressField : Bool := false) :
    Except String (List YulStmt) := do
  if isMapping fields field then
    throw s!"Compilation error: field '{field}' is a mapping; use setMapping, setMappingWord, or setMappingPackedWord"
  else
    match findFieldWithResolvedSlot fields field with
    | some (f, slot) => do
        if requireAddressField then
          match f.ty with
          | .address => pure ()
          | _ =>
              throw s!"Compilation error: field '{field}' is not address-typed; use Stmt.setStorage instead"
        let slots := slot :: f.aliasSlots
        let valueExpr ← compileExpr fields dynamicSource value
        let storedValueExpr :=
          if requireAddressField then
            YulExpr.call "and" [valueExpr, YulExpr.hex Compiler.Constants.addressMask]
          else
            valueExpr
        match slots with
        | [] =>
            throw s!"Compilation error: internal invariant failure: no write slots for field '{field}' in setStorage"
        | [singleSlot] =>
            match f.packedBits with
            | none =>
                pure [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit singleSlot, storedValueExpr])]
            | some packed =>
                pure (compilePackedStorageWrite (YulExpr.lit singleSlot) storedValueExpr packed)
        | _ =>
            let writeSlots := slots.map YulExpr.lit
            match f.packedBits with
            | none =>
                pure [
                  YulStmt.block (
                    [YulStmt.let_ "__compat_value" storedValueExpr] ++
                    writeSlots.map (fun writeSlot =>
                      YulStmt.expr (YulExpr.call "sstore" [writeSlot, YulExpr.ident "__compat_value"]))
                  )
                ]
            | some packed =>
                pure (compileCompatPackedStorageWrites writeSlots storedValueExpr packed)
    | none => throw s!"Compilation error: unknown storage field '{field}' in setStorage"

def compileStorageArrayPush (fields : List Field) (dynamicSource : DynamicDataSource)
    (field : String) (value : Expr) : Except String (List YulStmt) := do
  let (slot, _) ← validateDynamicArrayField fields field
  let valueExpr ← compileExpr fields dynamicSource value
  pure [
    YulStmt.block [
      YulStmt.let_ "__array_len" (YulExpr.call "sload" [YulExpr.lit slot]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit slot]),
      YulStmt.let_ "__array_base" (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit 32]),
      YulStmt.expr (YulExpr.call "sstore" [
        YulExpr.call "add" [YulExpr.ident "__array_base", YulExpr.ident "__array_len"],
        valueExpr
      ]),
      YulStmt.expr (YulExpr.call "sstore" [
        YulExpr.lit slot,
        YulExpr.call "add" [YulExpr.ident "__array_len", YulExpr.lit 1]
      ])
    ]
  ]

def compileStorageArrayPop (fields : List Field) (field : String) : Except String (List YulStmt) := do
  let (slot, _) ← validateDynamicArrayField fields field
  pure [
    YulStmt.block [
      YulStmt.let_ "__array_len" (YulExpr.call "sload" [YulExpr.lit slot]),
      YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__array_len"]) [
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
      ],
      YulStmt.let_ "__array_new_len" (YulExpr.call "sub" [YulExpr.ident "__array_len", YulExpr.lit 1]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit slot]),
      YulStmt.let_ "__array_base" (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit 32]),
      YulStmt.expr (YulExpr.call "sstore" [
        YulExpr.call "add" [YulExpr.ident "__array_base", YulExpr.ident "__array_new_len"],
        YulExpr.lit 0
      ]),
      YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident "__array_new_len"])
    ]
  ]

def compileSetStorageArrayElement (fields : List Field) (dynamicSource : DynamicDataSource)
    (field : String) (index value : Expr) : Except String (List YulStmt) := do
  let (slot, _) ← validateDynamicArrayField fields field
  let indexExpr ← compileExpr fields dynamicSource index
  let valueExpr ← compileExpr fields dynamicSource value
  pure [
    YulStmt.block [
      YulStmt.let_ "__array_len" (YulExpr.call "sload" [YulExpr.lit slot]),
      YulStmt.let_ "__array_index" indexExpr,
      YulStmt.if_ (YulExpr.call "iszero" [
        YulExpr.call "lt" [YulExpr.ident "__array_index", YulExpr.ident "__array_len"]
      ]) [
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
      ],
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit slot]),
      YulStmt.let_ "__array_base" (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit 32]),
      YulStmt.expr (YulExpr.call "sstore" [
        YulExpr.call "add" [YulExpr.ident "__array_base", YulExpr.ident "__array_index"],
        valueExpr
      ])
    ]
  ]

def compileSetMapping2 (fields : List Field) (dynamicSource : DynamicDataSource)
    (field : String) (key1 key2 value : Expr) : Except String (List YulStmt) := do
  if !isMapping2 fields field then
    throw s!"Compilation error: field '{field}' is not a double mapping"
  else
    match findFieldWriteSlots fields field with
    | some slots => do
        let key1Expr ← compileExpr fields dynamicSource key1
        let key2Expr ← compileExpr fields dynamicSource key2
        let valueExpr ← compileExpr fields dynamicSource value
        match slots with
        | [] =>
            throw s!"Compilation error: internal invariant failure: no write slots for mapping field '{field}' in setMapping2"
        | [slot] =>
            let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
            pure [
              YulStmt.expr (YulExpr.call "sstore" [
                YulExpr.call "mappingSlot" [innerSlot, key2Expr],
                valueExpr
              ])
            ]
        | _ =>
            pure [
              YulStmt.block (
                [YulStmt.let_ "__compat_key1" key1Expr, YulStmt.let_ "__compat_key2" key2Expr,
                  YulStmt.let_ "__compat_value" valueExpr] ++
                slots.map (fun slot =>
                  let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key1"]
                  YulStmt.expr (YulExpr.call "sstore" [
                    YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"],
                    YulExpr.ident "__compat_value"
                  ]))
              )
            ]
    | none => throw s!"Compilation error: unknown mapping field '{field}' in setMapping2"

def compileSetMapping2Word (fields : List Field) (dynamicSource : DynamicDataSource)
    (field : String) (key1 key2 : Expr) (wordOffset : Nat) (value : Expr) :
    Except String (List YulStmt) := do
  if !isMapping2 fields field then
    throw s!"Compilation error: field '{field}' is not a double mapping"
  else
    match findFieldWriteSlots fields field with
    | some slots => do
        let key1Expr ← compileExpr fields dynamicSource key1
        let key2Expr ← compileExpr fields dynamicSource key2
        let valueExpr ← compileExpr fields dynamicSource value
        match slots with
        | [] =>
            throw s!"Compilation error: internal invariant failure: no write slots for mapping field '{field}' in setMapping2Word"
        | [slot] =>
            let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
            let outerSlot := YulExpr.call "mappingSlot" [innerSlot, key2Expr]
            let finalSlot := if wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
            pure [YulStmt.expr (YulExpr.call "sstore" [finalSlot, valueExpr])]
        | _ =>
            pure [
              YulStmt.block (
                [YulStmt.let_ "__compat_key1" key1Expr, YulStmt.let_ "__compat_key2" key2Expr,
                  YulStmt.let_ "__compat_value" valueExpr] ++
                slots.map (fun slot =>
                  let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key1"]
                  let outerSlot := YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
                  let finalSlot := if wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
                  YulStmt.expr (YulExpr.call "sstore" [finalSlot, YulExpr.ident "__compat_value"])))
            ]
    | none => throw s!"Compilation error: unknown mapping field '{field}' in setMapping2Word"

def compileSetMappingChain (fields : List Field) (dynamicSource : DynamicDataSource)
    (field : String) (keys : List Expr) (value : Expr) : Except String (List YulStmt) := do
  if !isMapping fields field then
    throw s!"Compilation error: field '{field}' is not a mapping"
  else
    match findFieldWriteSlots fields field with
    | some slots => do
        let keyExprs ← compileExprList fields dynamicSource keys
        let valueExpr ← compileExpr fields dynamicSource value
        let writeAt (slot : Nat) (keysRef : List YulExpr) (valueRef : YulExpr) : YulStmt :=
          YulStmt.expr (YulExpr.call "sstore" [
            keysRef.foldl (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr]) (YulExpr.lit slot),
            valueRef
          ])
        match slots with
        | [] =>
            throw s!"Compilation error: internal invariant failure: no write slots for mapping field '{field}' in setMappingChain"
        | [slot] =>
            pure [writeAt slot keyExprs valueExpr]
        | _ =>
            pure [
              YulStmt.block (
                [YulStmt.let_ "__compat_value" valueExpr] ++
                keyExprs.zipIdx.map (fun (keyExpr, idx) => YulStmt.let_ s!"__compat_key{idx}" keyExpr) ++
                slots.map (fun slot =>
                  let compatKeys := List.range keyExprs.length |>.map (fun idx => YulExpr.ident s!"__compat_key{idx}")
                  writeAt slot compatKeys (YulExpr.ident "__compat_value"))
              )
            ]
    | none => throw s!"Compilation error: unknown mapping field '{field}' in setMappingChain"

def compileSetStructMember (fields : List Field) (dynamicSource : DynamicDataSource)
    (field : String) (key : Expr) (memberName : String) (value : Expr) :
    Except String (List YulStmt) := do
  if isMapping2 fields field then
    throw s!"Compilation error: field '{field}' is a double mapping; use Stmt.setStructMember2 instead of Stmt.setStructMember"
  match findStructMembers fields field with
  | none => throw s!"Compilation error: field '{field}' is not a mappingStruct"
  | some members =>
      match findStructMember members memberName with
      | none => throw s!"Compilation error: struct field '{field}' has no member '{memberName}'"
      | some member =>
          match member.packed with
          | none =>
              compileMappingSlotWrite fields field
                (← compileExpr fields dynamicSource key)
                (← compileExpr fields dynamicSource value)
                s!"setStructMember.{memberName}"
                member.wordOffset
          | some packed =>
              compileMappingPackedSlotWrite fields field
                (← compileExpr fields dynamicSource key)
                (← compileExpr fields dynamicSource value)
                member.wordOffset
                packed
                s!"setStructMember.{memberName}"

def compileSetStructMember2 (fields : List Field) (dynamicSource : DynamicDataSource)
    (field : String) (key1 key2 : Expr) (memberName : String) (value : Expr) :
    Except String (List YulStmt) := do
  if !isMapping2 fields field then
    throw s!"Compilation error: field '{field}' is not a double mapping; use Stmt.setStructMember instead of Stmt.setStructMember2"
  else
    match findStructMembers fields field with
    | none => throw s!"Compilation error: field '{field}' is not a mappingStruct"
    | some members =>
        match findStructMember members memberName with
        | none => throw s!"Compilation error: struct field '{field}' has no member '{memberName}'"
        | some member =>
            match findFieldWriteSlots fields field with
            | some slots => do
                let key1Expr ← compileExpr fields dynamicSource key1
                let key2Expr ← compileExpr fields dynamicSource key2
                let valueExpr ← compileExpr fields dynamicSource value
                match slots with
                | [] =>
                    throw s!"Compilation error: internal invariant failure: no write slots for mapping field '{field}' in setStructMember2.{memberName}"
                | [slot] =>
                    let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
                    let outerSlot := YulExpr.call "mappingSlot" [innerSlot, key2Expr]
                    let finalSlot := if member.wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit member.wordOffset]
                    match member.packed with
                    | none =>
                        pure [YulStmt.expr (YulExpr.call "sstore" [finalSlot, valueExpr])]
                    | some packed =>
                        pure (compilePackedStorageWrite finalSlot valueExpr packed)
                | _ =>
                    let finalSlots := slots.map fun slot =>
                      let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key1"]
                      let outerSlot := YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
                      if member.wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit member.wordOffset]
                    match member.packed with
                    | none =>
                        pure [
                          YulStmt.block (
                            [YulStmt.let_ "__compat_key1" key1Expr, YulStmt.let_ "__compat_key2" key2Expr,
                              YulStmt.let_ "__compat_value" valueExpr] ++
                            finalSlots.map (fun finalSlot =>
                              YulStmt.expr (YulExpr.call "sstore" [finalSlot, YulExpr.ident "__compat_value"]))
                          )
                        ]
                    | some packed =>
                        pure [
                          YulStmt.block (
                            [YulStmt.let_ "__compat_key1" key1Expr, YulStmt.let_ "__compat_key2" key2Expr] ++
                            compileCompatPackedStorageWrites finalSlots valueExpr packed
                          )
                        ]
            | none => throw s!"Compilation error: unknown mapping field '{field}' in setStructMember2.{memberName}"

end Compiler.CompilationModel
