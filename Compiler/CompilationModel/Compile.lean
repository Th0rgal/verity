/-
  Compiler.CompilationModel.Compile: Compilation pipeline implementation

  This module defines a declarative way to model contracts for compilation,
  eliminating manual IR writing while keeping the system simple and maintainable.

  Philosophy:
  - Contracts specify their structure declaratively
  - Compiler generates IR automatically from the spec
  - Reduces boilerplate and eliminates manual slot/selector management

  Features:
  - Storage fields with automatic slot assignment (uint256, address, mapping)
  - Flexible mapping types: Address→Uint256, Uint256→Uint256, nested mappings (#154)
  - Functions with automatic selector computation
  - Guards and access control patterns
  - If/else branching and bounded loops (#179)
  - Array/bytes parameter types and dynamic calldata (#180)
  - Internal function composition (#181)
  - Event emission (#153)
  - Verified external library integration (#184)
-/
import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.EcmAxiomCollection
import Compiler.CompilationModel.InternalNaming
import Compiler.CompilationModel.LayoutValidation
import Compiler.CompilationModel.MappingWrites
import Compiler.CompilationModel.UsageAnalysis
import Compiler.CompilationModel.ValidationHelpers
import Compiler.CompilationModel.SelectorInteropHelpers
import Compiler.CompilationModel.ExpressionCompile
import Compiler.CompilationModel.Validation

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

private def encodeStaticCustomErrorArg (errorName : String) (ty : ParamType) (argExpr : YulExpr) :
    Except String YulExpr :=
  match ty with
  | ParamType.uint256 | ParamType.bytes32 =>
      pure argExpr
  | ParamType.uint8 =>
      pure (YulExpr.call "and" [argExpr, YulExpr.lit 255])
  | ParamType.address =>
      pure (YulExpr.call "and" [argExpr, YulExpr.hex addressMask])
  | ParamType.bool =>
      pure (yulToBool argExpr)
  | _ =>
      throw s!"Compilation error: custom error '{errorName}' uses unsupported non-scalar parameter type {repr ty} in scalar encoding ({issue586Ref})."

/-- Compute the ABI head size (in bytes) for a list of member types.
Static members take their flattened word count × 32; dynamic members take 32 (offset word). -/
private def abiHeadSize (tys : List ParamType) : Nat :=
  tys.foldl (fun acc ty => acc + eventHeadWordSize ty) 0

/-- Recursively ABI-encode a dynamic composite type into memory at `dstBase`.
    Reads input from `dynamicSource` at `srcBase`.
    Returns (stmts, totalLenExpr) where totalLenExpr is the total bytes written. -/
private partial def compileUnindexedAbiEncode
    (dynamicSource : DynamicDataSource) (ty : ParamType)
    (srcBase dstBase : YulExpr) (stem : String) :
    Except String (List YulStmt × YulExpr) := do
  match ty with
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      let loaded := dynamicWordLoad dynamicSource srcBase
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [dstBase, normalizeEventWord ty loaded])
      ], YulExpr.lit 32)
  | ParamType.bytes =>
      let lenName := s!"{stem}_len"
      let paddedName := s!"{stem}_padded"
      pure ([
        YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase),
        YulStmt.expr (YulExpr.call "mstore" [dstBase, YulExpr.ident lenName])
      ] ++ dynamicCopyData dynamicSource
        (YulExpr.call "add" [dstBase, YulExpr.lit 32])
        (YulExpr.call "add" [srcBase, YulExpr.lit 32])
        (YulExpr.ident lenName) ++ [
        YulStmt.let_ paddedName (YulExpr.call "and" [
          YulExpr.call "add" [YulExpr.ident lenName, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [
            YulExpr.call "add" [dstBase, YulExpr.lit 32],
            YulExpr.ident lenName
          ],
          YulExpr.lit 0
        ])
      ], YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName])
  | ParamType.tuple elemTys =>
      let headSize := abiHeadSize elemTys
      let tailLenName := s!"{stem}_tail_len"
      let initStmts := [YulStmt.let_ tailLenName (YulExpr.lit headSize)]
      let rec goMembers (remaining : List ParamType) (elemIdx headOffset : Nat) :
          Except String (List YulStmt) := do
        match remaining with
        | [] => pure []
        | elemTy :: rest =>
            let elemSrcName := s!"{stem}_m{elemIdx}_src"
            let elemDstName := s!"{stem}_m{elemIdx}_dst"
            let srcStmts :=
              if eventIsDynamicType elemTy then
                let relName := s!"{stem}_m{elemIdx}_rel"
                [
                  YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                    srcBase, YulExpr.lit headOffset
                  ])),
                  YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
                ]
              else
                [YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.lit headOffset])]
            let encStmts ←
              if eventIsDynamicType elemTy then do
                let storeOffset := YulStmt.expr (YulExpr.call "mstore" [
                  YulExpr.call "add" [dstBase, YulExpr.lit headOffset],
                  YulExpr.ident tailLenName
                ])
                let (innerStmts, innerLen) ←
                  compileUnindexedAbiEncode dynamicSource elemTy
                    (YulExpr.ident elemSrcName)
                    (YulExpr.ident elemDstName)
                    s!"{stem}_m{elemIdx}"
                pure ([storeOffset,
                  YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident tailLenName])
                ] ++ innerStmts ++ [
                  YulStmt.assign tailLenName (YulExpr.call "add" [YulExpr.ident tailLenName, innerLen])
                ])
              else do
                let (innerStmts, _) ←
                  compileUnindexedAbiEncode dynamicSource elemTy
                    (YulExpr.ident elemSrcName)
                    (YulExpr.call "add" [dstBase, YulExpr.lit headOffset])
                    s!"{stem}_m{elemIdx}"
                pure innerStmts
            let restStmts ← goMembers rest (elemIdx + 1) (headOffset + eventHeadWordSize elemTy)
            pure (srcStmts ++ encStmts ++ restStmts)
      let memberStmts ← goMembers elemTys 0 0
      pure (initStmts ++ memberStmts, YulExpr.ident tailLenName)
  | ParamType.fixedArray elemTy n =>
      if eventIsDynamicType elemTy then
        let tailLenName := s!"{stem}_fa_tail_len"
        let headSize := n * 32
        let initStmts := [YulStmt.let_ tailLenName (YulExpr.lit headSize)]
        let rec goElems (i : Nat) : Except String (List YulStmt) := do
          if i < n then
            let elemSrcName := s!"{stem}_fa{i}_src"
            let elemDstName := s!"{stem}_fa{i}_dst"
            let relName := s!"{stem}_fa{i}_rel"
            let storeOffset := YulStmt.expr (YulExpr.call "mstore" [
              YulExpr.call "add" [dstBase, YulExpr.lit (i * 32)],
              YulExpr.ident tailLenName
            ])
            let srcStmts := [
              YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                srcBase, YulExpr.lit (i * 32)
              ])),
              YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
            ]
            let (innerStmts, innerLen) ←
              compileUnindexedAbiEncode dynamicSource elemTy
                (YulExpr.ident elemSrcName)
                (YulExpr.ident elemDstName)
                s!"{stem}_fa{i}"
            let restStmts ← goElems (i + 1)
            pure (srcStmts ++ [storeOffset,
              YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident tailLenName])
            ] ++ innerStmts ++ [
              YulStmt.assign tailLenName (YulExpr.call "add" [YulExpr.ident tailLenName, innerLen])
            ] ++ restStmts)
          else
            pure []
        let elemStmts ← goElems 0
        pure (initStmts ++ elemStmts, YulExpr.ident tailLenName)
      else
        let elemWordSize := eventHeadWordSize elemTy
        let rec goStaticElems (i : Nat) : Except String (List YulStmt) := do
          if i < n then
            let elemSrcName := s!"{stem}_fa{i}_src"
            let srcStmt := YulStmt.let_ elemSrcName (YulExpr.call "add" [
              srcBase, YulExpr.lit (i * elemWordSize)
            ])
            let (innerStmts, _) ←
              compileUnindexedAbiEncode dynamicSource elemTy
                (YulExpr.ident elemSrcName)
                (YulExpr.call "add" [dstBase, YulExpr.lit (i * elemWordSize)])
                s!"{stem}_fa{i}"
            let restStmts ← goStaticElems (i + 1)
            pure ([srcStmt] ++ innerStmts ++ restStmts)
          else
            pure []
        let elemStmts ← goStaticElems 0
        pure (elemStmts, YulExpr.lit (n * elemWordSize))
  | ParamType.array elemTy =>
      -- Dynamic array: [length][head_0]...[head_{n-1}][tail_0]...[tail_{n-1}]
      -- Each head word is an offset (relative to start of elements area) pointing
      -- to the element's tail data. For static elements the data is inline.
      let lenName := s!"{stem}_arr_len"
      let lenStmt := YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase)
      let storeLenStmt := YulStmt.expr (YulExpr.call "mstore" [dstBase, YulExpr.ident lenName])
      if eventIsDynamicType elemTy then
        -- Dynamic elements need offset-based head/tail layout
        let headLenName := s!"{stem}_arr_head_len"
        let tailLenName := s!"{stem}_arr_tail_len"
        let loopIdxName := s!"{stem}_arr_i"
        let elemRelName := s!"{stem}_arr_elem_rel"
        let elemSrcName := s!"{stem}_arr_elem_src"
        let elemDstName := s!"{stem}_arr_elem_dst"
        -- We generate a loop that processes each element:
        --   1) Read element offset from source, resolve to absolute source position
        --   2) Store current tail offset as the head word
        --   3) Recursively encode element data at current tail position
        --   4) Advance tail offset
        -- Since element encoding size is data-dependent, we track tail with a mutable var.
        let (innerStmts, innerLen) ←
          compileUnindexedAbiEncode dynamicSource elemTy
            (YulExpr.ident elemSrcName)
            (YulExpr.ident elemDstName)
            s!"{stem}_arr_e"
        let loopBody := [
          -- Read element's relative offset from source head area
          YulStmt.let_ elemRelName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
            YulExpr.call "add" [srcBase, YulExpr.lit 32],
            YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit 32]
          ])),
          -- Resolve to absolute source position (relative to array data start = srcBase + 32)
          YulStmt.let_ elemSrcName (YulExpr.call "add" [
            YulExpr.call "add" [srcBase, YulExpr.lit 32],
            YulExpr.ident elemRelName
          ]),
          -- Store offset in head area of destination
          YulStmt.expr (YulExpr.call "mstore" [
            YulExpr.call "add" [
              YulExpr.call "add" [dstBase, YulExpr.lit 32],
              YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit 32]
            ],
            YulExpr.ident tailLenName
          ]),
          -- Destination for this element's encoded data
          YulStmt.let_ elemDstName (YulExpr.call "add" [
            YulExpr.call "add" [dstBase, YulExpr.lit 32],
            YulExpr.ident tailLenName
          ])
        ] ++ innerStmts ++ [
          YulStmt.assign tailLenName (YulExpr.call "add" [YulExpr.ident tailLenName, innerLen])
        ]
        let loopStmt := YulStmt.for_
          [YulStmt.let_ loopIdxName (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident loopIdxName, YulExpr.ident lenName])
          [YulStmt.assign loopIdxName (YulExpr.call "add" [YulExpr.ident loopIdxName, YulExpr.lit 1])]
          loopBody
        pure ([lenStmt, storeLenStmt,
          YulStmt.let_ headLenName (YulExpr.call "mul" [YulExpr.ident lenName, YulExpr.lit 32]),
          YulStmt.let_ tailLenName (YulExpr.ident headLenName),
          loopStmt
        ], YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident tailLenName])
      else
        -- Static elements: each takes a fixed number of words, no offsets needed
        let elemWordSize := eventHeadWordSize elemTy
        let byteLenName := s!"{stem}_arr_byte_len"
        let loopIdxName := s!"{stem}_arr_i"
        let elemSrcName := s!"{stem}_arr_elem_src"
        let (innerStmts, _) ←
          compileUnindexedAbiEncode dynamicSource elemTy
            (YulExpr.ident elemSrcName)
            (YulExpr.call "add" [
              YulExpr.call "add" [dstBase, YulExpr.lit 32],
              YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit elemWordSize]
            ])
            s!"{stem}_arr_e"
        let loopBody := [
          YulStmt.let_ elemSrcName (YulExpr.call "add" [
            YulExpr.call "add" [srcBase, YulExpr.lit 32],
            YulExpr.call "mul" [YulExpr.ident loopIdxName, YulExpr.lit elemWordSize]
          ])
        ] ++ innerStmts
        let loopStmt := YulStmt.for_
          [YulStmt.let_ loopIdxName (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident loopIdxName, YulExpr.ident lenName])
          [YulStmt.assign loopIdxName (YulExpr.call "add" [YulExpr.ident loopIdxName, YulExpr.lit 1])]
          loopBody
        let paddedName := s!"{stem}_arr_padded"
        pure ([lenStmt, storeLenStmt,
            YulStmt.let_ byteLenName (YulExpr.call "mul" [YulExpr.ident lenName, YulExpr.lit elemWordSize]),
            loopStmt,
            YulStmt.let_ paddedName (YulExpr.call "and" [
              YulExpr.call "add" [YulExpr.ident byteLenName, YulExpr.lit 31],
              YulExpr.call "not" [YulExpr.lit 31]
            ])
          ], YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName])

private def revertWithCustomError (dynamicSource : DynamicDataSource)
    (errorDef : ErrorDef) (sourceArgs : List Expr) (args : List YulExpr) :
    Except String (List YulStmt) := do
  if errorDef.params.length != args.length || sourceArgs.length != args.length then
    throw s!"Compilation error: custom error '{errorDef.name}' expects {errorDef.params.length} args, got {args.length}"
  let sigBytes := bytesFromString (errorSignature errorDef)
  let storePtr := YulStmt.let_ "__err_ptr" (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
  let sigStores := (chunkBytes32 sigBytes).zipIdx.map fun (chunk, idx) =>
    YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.call "add" [YulExpr.ident "__err_ptr", YulExpr.lit (idx * 32)],
      YulExpr.hex (wordFromBytes chunk)
    ])
  let hashStmt := YulStmt.let_ "__err_hash"
    (YulExpr.call "keccak256" [YulExpr.ident "__err_ptr", YulExpr.lit sigBytes.length])
  let selectorStmt := YulStmt.let_ "__err_selector"
    (YulExpr.call "shl" [YulExpr.lit selectorShift, YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.ident "__err_hash"]])
  let selectorStore := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.ident "__err_selector"])
  let headSize := abiHeadSize errorDef.params
  let tailInit := YulStmt.let_ "__err_tail" (YulExpr.lit headSize)
  let argsWithSources := (errorDef.params.zip sourceArgs).zip args |>.map (fun ((ty, srcExpr), argExpr) => (ty, srcExpr, argExpr))
  let rec attachOffsets (items : List (ParamType × Expr × YulExpr)) (headOffset : Nat) :
      List (ParamType × Expr × YulExpr × Nat) :=
    match items with
    | [] => []
    | (ty, srcExpr, argExpr) :: rest =>
        (ty, srcExpr, argExpr, headOffset) :: attachOffsets rest (headOffset + paramHeadSize ty)
  let argsWithHeadOffsets := attachOffsets argsWithSources 4
  let argStores ← argsWithHeadOffsets.zipIdx.mapM fun ((ty, srcExpr, argExpr, headOffset), idx) => do
    match ty with
    | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
        let encoded ← encodeStaticCustomErrorArg errorDef.name ty argExpr
        pure [YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit headOffset, encoded])]
    | ParamType.tuple _ | ParamType.fixedArray _ _ =>
        match srcExpr with
        | Expr.param name =>
            if isDynamicParamType ty then
              let dstName := s!"__err_arg{idx}_dst"
              let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
              let (encStmts, encLen) ←
                compileUnindexedAbiEncode dynamicSource ty srcBase (YulExpr.ident dstName) s!"__err_arg{idx}"
              pure ([
                YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit headOffset, YulExpr.ident "__err_tail"]),
                YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"])
              ] ++ encStmts ++ [
                YulStmt.assign "__err_tail" (YulExpr.call "add" [YulExpr.ident "__err_tail", encLen])
              ])
            else
              let leaves := staticCompositeLeaves name ty
              let stores := leaves.zipIdx.map fun ((leafTy, leafExpr), wordIdx) =>
                YulStmt.expr (YulExpr.call "mstore" [
                  YulExpr.lit (headOffset + wordIdx * 32),
                  normalizeEventWord leafTy leafExpr
                ])
              pure stores
        | _ =>
            throw s!"Compilation error: custom error '{errorDef.name}' parameter of type {repr ty} currently requires direct parameter reference ({issue586Ref})."
    | ParamType.bytes | ParamType.array _ =>
        match srcExpr with
        | Expr.param name =>
            let dstName := s!"__err_arg{idx}_dst"
            let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
            let (encStmts, encLen) ←
              compileUnindexedAbiEncode dynamicSource ty srcBase (YulExpr.ident dstName) s!"__err_arg{idx}"
            pure ([
              YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit headOffset, YulExpr.ident "__err_tail"]),
              YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"])
            ] ++ encStmts ++ [
              YulStmt.assign "__err_tail" (YulExpr.call "add" [YulExpr.ident "__err_tail", encLen])
            ])
        | _ =>
            throw s!"Compilation error: custom error '{errorDef.name}' parameter of type {repr ty} currently requires direct parameter reference ({issue586Ref})."
  let revertStmt := YulStmt.expr (YulExpr.call "revert" [
    YulExpr.lit 0,
    YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"]
  ])
  pure [YulStmt.block ([storePtr] ++ sigStores ++ [hashStmt, selectorStmt, selectorStore, tailInit] ++ argStores.flatten ++ [revertStmt])]

-- Compile statement to Yul (using mutual recursion for lists).
-- When isInternal=true, Stmt.return compiles to `__ret := value; leave` so internal
-- function execution terminates immediately without exiting the outer EVM call.
mutual
def compileStmtList (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false)
    (inScopeNames : List String := []) :
    List Stmt → Except String (List YulStmt)
  | [] => pure []
  | s :: ss => do
      let head ← compileStmt fields events errors dynamicSource internalRetNames isInternal inScopeNames s
      let nextScopeNames := collectStmtNames s ++ inScopeNames
      let tail ← compileStmtList fields events errors dynamicSource internalRetNames isInternal nextScopeNames ss
      pure (head ++ tail)

def compileStmt (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false)
    (inScopeNames : List String := []) :
    Stmt → Except String (List YulStmt)
  | Stmt.letVar name value => do
      pure [YulStmt.let_ name (← compileExpr fields dynamicSource value)]
  | Stmt.assignVar name value => do
      pure [YulStmt.assign name (← compileExpr fields dynamicSource value)]
  | Stmt.setStorage field value =>
    if isMapping fields field then
      throw s!"Compilation error: field '{field}' is a mapping; use setMapping, setMappingWord, or setMappingPackedWord"
    else
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) => do
          let slots := slot :: f.aliasSlots
          let valueExpr ← compileExpr fields dynamicSource value
          match slots with
          | [] =>
              throw s!"Compilation error: internal invariant failure: no write slots for field '{field}' in setStorage"
          | [singleSlot] =>
              match f.packedBits with
              | none =>
                  pure [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit singleSlot, valueExpr])]
              | some packed =>
                  let maskNat := packedMaskNat packed
                  let shiftedMaskNat := packedShiftedMaskNat packed
                  pure [
                    YulStmt.block [
                      YulStmt.let_ "__compat_value" valueExpr,
                      YulStmt.let_ "__compat_packed" (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit maskNat]),
                      YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [YulExpr.lit singleSlot]),
                      YulStmt.let_ "__compat_slot_cleared" (YulExpr.call "and" [
                        YulExpr.ident "__compat_slot_word",
                        YulExpr.call "not" [YulExpr.lit shiftedMaskNat]
                      ]),
                      YulStmt.expr (YulExpr.call "sstore" [
                        YulExpr.lit singleSlot,
                        YulExpr.call "or" [
                          YulExpr.ident "__compat_slot_cleared",
                          YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]
                        ]
                      ])
                    ]
                  ]
          | _ =>
              match f.packedBits with
              | none =>
                  pure [
                    YulStmt.block (
                      [YulStmt.let_ "__compat_value" valueExpr] ++
                      slots.map (fun writeSlot =>
                        YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"]))
                    )
                  ]
              | some packed =>
                  let maskNat := packedMaskNat packed
                  let shiftedMaskNat := packedShiftedMaskNat packed
                  pure [
                    YulStmt.block (
                      [YulStmt.let_ "__compat_value" valueExpr,
                       YulStmt.let_ "__compat_packed" (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit maskNat])] ++
                      slots.map (fun writeSlot =>
                        YulStmt.block [
                          YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [YulExpr.lit writeSlot]),
                          YulStmt.let_ "__compat_slot_cleared" (YulExpr.call "and" [
                            YulExpr.ident "__compat_slot_word",
                            YulExpr.call "not" [YulExpr.lit shiftedMaskNat]
                          ]),
                          YulStmt.expr (YulExpr.call "sstore" [
                            YulExpr.lit writeSlot,
                            YulExpr.call "or" [
                              YulExpr.ident "__compat_slot_cleared",
                              YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]
                            ]
                          ])
                        ])
                    )
                  ]
      | none => throw s!"Compilation error: unknown storage field '{field}' in setStorage"
  | Stmt.setMapping field key value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMapping"
  | Stmt.setMappingWord field key wordOffset value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMappingWord"
        wordOffset
  | Stmt.setMappingPackedWord field key wordOffset packed value => do
      compileMappingPackedSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        wordOffset
        packed
        "setMappingPackedWord"
  | Stmt.setMapping2 field key1 key2 value =>
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
                  [YulStmt.let_ "__compat_key1" key1Expr, YulStmt.let_ "__compat_key2" key2Expr, YulStmt.let_ "__compat_value" valueExpr] ++
                  slots.map (fun slot =>
                    let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key1"]
                    YulStmt.expr (YulExpr.call "sstore" [
                      YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"],
                      YulExpr.ident "__compat_value"
                    ]))
                )
              ]
      | none => throw s!"Compilation error: unknown mapping field '{field}' in setMapping2"
  | Stmt.setMapping2Word field key1 key2 wordOffset value =>
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
              pure [
                YulStmt.expr (YulExpr.call "sstore" [finalSlot, valueExpr])
              ]
          | _ =>
              pure [
                YulStmt.block (
                  [YulStmt.let_ "__compat_key1" key1Expr, YulStmt.let_ "__compat_key2" key2Expr, YulStmt.let_ "__compat_value" valueExpr] ++
                  slots.map (fun slot =>
                    let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key1"]
                    let outerSlot := YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
                    let finalSlot := if wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
                    YulStmt.expr (YulExpr.call "sstore" [finalSlot, YulExpr.ident "__compat_value"])))
              ]
      | none => throw s!"Compilation error: unknown mapping field '{field}' in setMapping2Word"
  | Stmt.setMappingUint field key value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMappingUint"
  | Stmt.setStructMember field key memberName value => do
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
  | Stmt.setStructMember2 field key1 key2 memberName value =>
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
                      let maskNat := packedMaskNat packed
                      let shiftedMaskNat := packedShiftedMaskNat packed
                      pure [
                        YulStmt.block [
                          YulStmt.let_ "__compat_value" valueExpr,
                          YulStmt.let_ "__compat_packed" (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit maskNat]),
                          YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [finalSlot]),
                          YulStmt.let_ "__compat_slot_cleared" (YulExpr.call "and" [
                            YulExpr.ident "__compat_slot_word",
                            YulExpr.call "not" [YulExpr.lit shiftedMaskNat]
                          ]),
                          YulStmt.expr (YulExpr.call "sstore" [
                            finalSlot,
                            YulExpr.call "or" [
                              YulExpr.ident "__compat_slot_cleared",
                              YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]
                            ]
                          ])
                        ]
                      ]
                | _ =>
                    pure [
                      YulStmt.block (
                        [YulStmt.let_ "__compat_key1" key1Expr, YulStmt.let_ "__compat_key2" key2Expr, YulStmt.let_ "__compat_value" valueExpr] ++
                        slots.map (fun slot =>
                          let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, YulExpr.ident "__compat_key1"]
                          let outerSlot := YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
                          let finalSlot := if member.wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit member.wordOffset]
                          match member.packed with
                          | none =>
                            YulStmt.expr (YulExpr.call "sstore" [finalSlot, YulExpr.ident "__compat_value"])
                          | some packed =>
                            let maskNat := packedMaskNat packed
                            let shiftedMaskNat := packedShiftedMaskNat packed
                            YulStmt.block [
                              YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [finalSlot]),
                              YulStmt.let_ "__compat_slot_cleared" (YulExpr.call "and" [
                                YulExpr.ident "__compat_slot_word",
                                YulExpr.call "not" [YulExpr.lit shiftedMaskNat]
                              ]),
                              YulStmt.expr (YulExpr.call "sstore" [
                                finalSlot,
                                YulExpr.call "or" [
                                  YulExpr.ident "__compat_slot_cleared",
                                  YulExpr.call "shl" [YulExpr.lit packed.offset,
                                    YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit maskNat]]
                                ]
                              ])
                            ])
                      )
                    ]
            | none => throw s!"Compilation error: unknown mapping field '{field}' in setStructMember2.{memberName}"
  | Stmt.require cond message =>
    do
      let failCond ← compileRequireFailCond fields dynamicSource cond
      pure [
        YulStmt.if_ failCond (revertWithMessage message)
      ]
  | Stmt.requireError cond errorName args => do
      let failCond ← compileRequireFailCond fields dynamicSource cond
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      let argExprs ← compileExprList fields dynamicSource args
      let revertStmts ← revertWithCustomError dynamicSource errorDef args argExprs
      pure [YulStmt.if_ failCond revertStmts]
  | Stmt.revertError errorName args => do
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      let argExprs ← compileExprList fields dynamicSource args
      revertWithCustomError dynamicSource errorDef args argExprs
  | Stmt.return value =>
    do
      let valueExpr ← compileExpr fields dynamicSource value
      if isInternal then
        match internalRetNames with
        | retName :: _ => pure [YulStmt.assign retName valueExpr, YulStmt.leave]
        | [] => throw s!"Compilation error: internal return target is missing"
      else
        pure [
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueExpr]),
          YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
  | Stmt.stop => return [YulStmt.expr (YulExpr.call "stop" [])]

  | Stmt.ite cond thenBranch elseBranch => do
      -- If/else: compile to Yul if + negated if (#179)
      let condExpr ← compileExpr fields dynamicSource cond
      let thenStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal inScopeNames thenBranch
      let elseStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal inScopeNames elseBranch
      if elseBranch.isEmpty then
        -- Simple if (no else)
        pure [YulStmt.if_ condExpr thenStmts]
      else
        -- If/else: cache condition in a block-scoped local to avoid re-evaluation
        -- after then-branch may have mutated state.
        -- Wrapped in block { } and freshened against names seen in this if/else shape
        -- so user locals cannot shadow the compiler-generated temp.
        let iteUsedNames := inScopeNames ++ collectExprNames cond ++ collectStmtListNames thenBranch ++ collectStmtListNames elseBranch
        let iteCondName := pickFreshName "__ite_cond" iteUsedNames
        pure [YulStmt.block [
          YulStmt.let_ iteCondName condExpr,
          YulStmt.if_ (YulExpr.ident iteCondName) thenStmts,
          YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident iteCondName]) elseStmts
        ]]

  | Stmt.forEach varName count body => do
      -- Bounded loop: for { let i := 0 } lt(i, count) { i := add(i, 1) } { body } (#179)
      let countExpr ← compileExpr fields dynamicSource count
      let bodyStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal (varName :: inScopeNames) body
      let initStmts := [YulStmt.let_ varName (YulExpr.lit 0)]
      let condExpr := YulExpr.call "lt" [YulExpr.ident varName, countExpr]
      let postStmts := [YulStmt.assign varName (YulExpr.call "add" [YulExpr.ident varName, YulExpr.lit 1])]
      pure [YulStmt.for_ initStmts condExpr postStmts bodyStmts]

  | Stmt.emit eventName args => do
      let eventDef? := events.find? (·.name == eventName)
      let eventDef ←
        match eventDef? with
        | some e => pure e
        | none => throw s!"Compilation error: unknown event '{eventName}'"
      if args.length != eventDef.params.length then
        throw s!"Compilation error: event '{eventName}' expects {eventDef.params.length} args, got {args.length}"
      let compiledArgs ← compileExprList fields dynamicSource args
      let zippedWithSource := (eventDef.params.zip args).zip compiledArgs |>.map (fun ((p, srcExpr), argExpr) =>
        (p, srcExpr, argExpr))
      let indexed := zippedWithSource.filter (fun (p, _, _) => p.kind == EventParamKind.indexed)
      let unindexed := zippedWithSource.filter (fun (p, _, _) => p.kind == EventParamKind.unindexed)
      if indexed.length > 3 then
        throw s!"Compilation error: event '{eventName}' has {indexed.length} indexed params; max is 3"
      let sig := eventSignature eventDef
      let sigBytes := bytesFromString sig
      let freeMemPtr := YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]
      let storePtr := YulStmt.let_ "__evt_ptr" freeMemPtr
      let sigStores := (chunkBytes32 sigBytes).zipIdx.map fun (chunk, idx) =>
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit (idx * 32)],
          YulExpr.hex (wordFromBytes chunk)
        ])
      let topic0Expr := YulExpr.call "keccak256" [YulExpr.ident "__evt_ptr", YulExpr.lit sigBytes.length]
      let topic0Store := YulStmt.let_ "__evt_topic0" topic0Expr
      let unindexedHeadSize := (unindexed.map (fun (p, _, _) => eventHeadWordSize p.ty)).foldl (· + ·) 0
      let hasUnindexedDynamicData := unindexed.any (fun (p, _, _) => eventIsDynamicType p.ty)
      let unindexedTailInit :=
        if hasUnindexedDynamicData then
          [YulStmt.let_ "__evt_data_tail" (YulExpr.lit unindexedHeadSize)]
        else
          []
      let rec compileUnindexedStores
          (remaining : List (EventParam × Expr × YulExpr)) (argIdx : Nat) (headOffset : Nat) :
          Except String (List YulStmt) := do
        match remaining with
        | [] => pure []
        | (p, srcExpr, argExpr) :: rest =>
            let curHeadPtr := YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit headOffset]
            let current ←
              match p.ty with
              | ParamType.bytes =>
                  match srcExpr with
                  | Expr.param name =>
                      let lenName := s!"__evt_arg{argIdx}_len"
                      let dstName := s!"__evt_arg{argIdx}_dst"
                      let paddedName := s!"__evt_arg{argIdx}_padded"
                      pure ([
                        YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                        YulStmt.let_ lenName (YulExpr.ident s!"{name}_length"),
                        YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"]),
                        YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident dstName, YulExpr.ident lenName]),
                      ] ++ dynamicCopyData dynamicSource
                        (YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32])
                        (YulExpr.ident s!"{name}_data_offset")
                        (YulExpr.ident lenName) ++ [
                        YulStmt.let_ paddedName (YulExpr.call "and" [
                          YulExpr.call "add" [YulExpr.ident lenName, YulExpr.lit 31],
                          YulExpr.call "not" [YulExpr.lit 31]
                        ]),
                        YulStmt.expr (YulExpr.call "mstore" [
                          YulExpr.call "add" [
                            YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                            YulExpr.ident lenName
                          ],
                          YulExpr.lit 0
                        ]),
                        YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [
                          YulExpr.ident "__evt_data_tail",
                          YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName]
                        ])
                      ])
                  | _ =>
                      throw s!"Compilation error: unindexed bytes event param '{p.name}' in event '{eventName}' currently requires direct bytes parameter reference ({issue586Ref})."
              | ParamType.array elemTy =>
                  if elemTy == ParamType.bytes then
                      match srcExpr with
                      | Expr.param name =>
                          let lenName := s!"__evt_arg{argIdx}_len"
                          let dstName := s!"__evt_arg{argIdx}_dst"
                          let headLenName := s!"__evt_arg{argIdx}_head_len"
                          let tailLenName := s!"__evt_arg{argIdx}_tail_len"
                          let loopIndexName := s!"__evt_arg{argIdx}_i"
                          let elemOffsetName := s!"__evt_arg{argIdx}_elem_offset"
                          let elemLenPosName := s!"__evt_arg{argIdx}_elem_len_pos"
                          let elemLenName := s!"__evt_arg{argIdx}_elem_len"
                          let elemDataName := s!"__evt_arg{argIdx}_elem_data"
                          let elemDstName := s!"__evt_arg{argIdx}_elem_dst"
                          let elemPaddedName := s!"__evt_arg{argIdx}_elem_padded"
                          pure ([
                            YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                            YulStmt.let_ lenName (YulExpr.ident s!"{name}_length"),
                            YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"]),
                            YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident dstName, YulExpr.ident lenName]),
                            YulStmt.let_ headLenName (YulExpr.call "mul" [YulExpr.ident lenName, YulExpr.lit 32]),
                            YulStmt.let_ tailLenName (YulExpr.ident headLenName),
                            YulStmt.for_
                              [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
                              (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident lenName])
                              [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
                              ([
                                YulStmt.let_ elemOffsetName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                                  YulExpr.ident s!"{name}_data_offset",
                                  YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit 32]
                                ])),
                                YulStmt.let_ elemLenPosName (YulExpr.call "add" [
                                  YulExpr.ident s!"{name}_data_offset",
                                  YulExpr.ident elemOffsetName
                                ]),
                                YulStmt.let_ elemLenName (dynamicWordLoad dynamicSource (YulExpr.ident elemLenPosName)),
                                YulStmt.let_ elemDataName (YulExpr.call "add" [YulExpr.ident elemLenPosName, YulExpr.lit 32]),
                                YulStmt.expr (YulExpr.call "mstore" [
                                  YulExpr.call "add" [
                                    YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                                    YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit 32]
                                  ],
                                  YulExpr.ident tailLenName
                                ]),
                                YulStmt.let_ elemDstName (YulExpr.call "add" [
                                  YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                                  YulExpr.ident tailLenName
                                ]),
                                YulStmt.expr (YulExpr.call "mstore" [
                                  YulExpr.ident elemDstName,
                                  YulExpr.ident elemLenName
                                ])
                              ] ++ dynamicCopyData dynamicSource
                                (YulExpr.call "add" [YulExpr.ident elemDstName, YulExpr.lit 32])
                                (YulExpr.ident elemDataName)
                                (YulExpr.ident elemLenName) ++ [
                                YulStmt.let_ elemPaddedName (YulExpr.call "and" [
                                  YulExpr.call "add" [YulExpr.ident elemLenName, YulExpr.lit 31],
                                  YulExpr.call "not" [YulExpr.lit 31]
                                ]),
                                YulStmt.expr (YulExpr.call "mstore" [
                                  YulExpr.call "add" [
                                    YulExpr.call "add" [YulExpr.ident elemDstName, YulExpr.lit 32],
                                    YulExpr.ident elemLenName
                                  ],
                                  YulExpr.lit 0
                                ]),
                                YulStmt.assign tailLenName (YulExpr.call "add" [
                                  YulExpr.ident tailLenName,
                                  YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident elemPaddedName]
                                ])
                              ]),
                            YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [
                              YulExpr.ident "__evt_data_tail",
                              YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident tailLenName]
                            ])
                          ])
                      | _ =>
                          throw s!"Compilation error: unindexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                  else if indexedDynamicArrayElemSupported elemTy then
                    match srcExpr with
                    | Expr.param name =>
                        let lenName := s!"__evt_arg{argIdx}_len"
                        let dstName := s!"__evt_arg{argIdx}_dst"
                        let elemWordSize := eventHeadWordSize elemTy
                        let byteLenName := s!"__evt_arg{argIdx}_byte_len"
                        let paddedName := s!"__evt_arg{argIdx}_padded"
                        let elemBaseName := s!"__evt_arg{argIdx}_elem_base"
                        let elemOutBaseName := s!"__evt_arg{argIdx}_out_base"
                        let loopIndexName := s!"__evt_arg{argIdx}_i"
                        let leafStores :=
                          (staticCompositeLeafTypeOffsets 0 elemTy).map fun (leafOffset, leafTy) =>
                            let loadExpr := dynamicWordLoad dynamicSource (YulExpr.call "add" [
                              YulExpr.ident elemBaseName,
                              YulExpr.lit leafOffset
                            ])
                            YulStmt.expr (YulExpr.call "mstore" [
                              YulExpr.call "add" [YulExpr.ident elemOutBaseName, YulExpr.lit leafOffset],
                              normalizeEventWord leafTy loadExpr
                            ])
                        pure ([
                          YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                          YulStmt.let_ lenName (YulExpr.ident s!"{name}_length"),
                          YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"]),
                          YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident dstName, YulExpr.ident lenName]),
                          YulStmt.let_ byteLenName (YulExpr.call "mul" [YulExpr.ident lenName, YulExpr.lit elemWordSize]),
                          YulStmt.for_
                            [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
                            (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident lenName])
                            [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
                            ([
                              YulStmt.let_ elemBaseName (YulExpr.call "add" [
                                YulExpr.ident s!"{name}_data_offset",
                                YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                              ]),
                              YulStmt.let_ elemOutBaseName (YulExpr.call "add" [
                                YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                                YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                              ])
                            ] ++ leafStores),
                          YulStmt.let_ paddedName (YulExpr.call "and" [
                            YulExpr.call "add" [YulExpr.ident byteLenName, YulExpr.lit 31],
                            YulExpr.call "not" [YulExpr.lit 31]
                          ]),
                          YulStmt.expr (YulExpr.call "mstore" [
                            YulExpr.call "add" [
                              YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                              YulExpr.ident byteLenName
                            ],
                            YulExpr.lit 0
                          ]),
                          YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [
                            YulExpr.ident "__evt_data_tail",
                            YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName]
                          ])
                        ])
                    | _ =>
                        throw s!"Compilation error: unindexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                  else if eventIsDynamicType elemTy then
                    match srcExpr with
                    | Expr.param name =>
                        let dstName := s!"__evt_arg{argIdx}_dst"
                        let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
                        let (encStmts, encLen) ←
                          compileUnindexedAbiEncode dynamicSource p.ty srcBase (YulExpr.ident dstName) s!"__evt_arg{argIdx}"
                        pure ([
                          YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                          YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"])
                        ] ++ encStmts ++ [
                          YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [YulExpr.ident "__evt_data_tail", encLen])
                        ])
                    | _ =>
                        throw s!"Compilation error: unindexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                  else
                    throw s!"Compilation error: unindexed array event param '{p.name}' in event '{eventName}' has unsupported element type {repr elemTy} ({issue586Ref})."
              | ParamType.fixedArray _ _ | ParamType.tuple _ =>
                  if eventIsDynamicType p.ty then
                    match srcExpr with
                    | Expr.param name =>
                        let dstName := s!"__evt_arg{argIdx}_dst"
                        let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
                        let (encStmts, encLen) ←
                          compileUnindexedAbiEncode dynamicSource p.ty srcBase (YulExpr.ident dstName) s!"__evt_arg{argIdx}"
                        pure ([
                          YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                          YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"])
                        ] ++ encStmts ++ [
                          YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [YulExpr.ident "__evt_data_tail", encLen])
                        ])
                    | _ =>
                        throw s!"Compilation error: unindexed dynamic composite event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                  else
                    match srcExpr with
                    | Expr.param name =>
                        let leaves := staticCompositeLeaves name p.ty
                        let stores := leaves.zipIdx.map fun ((leafTy, leafExpr), wordIdx) =>
                          YulStmt.expr (YulExpr.call "mstore" [
                            YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit (headOffset + wordIdx * 32)],
                            normalizeEventWord leafTy leafExpr
                          ])
                        pure stores
                    | _ =>
                        throw s!"Compilation error: unindexed static composite event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              | _ =>
                  pure [YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, normalizeEventWord p.ty argExpr])]
            let tail ← compileUnindexedStores rest (argIdx + 1) (headOffset + eventHeadWordSize p.ty)
            pure (current ++ tail)
      let unindexedStores ← compileUnindexedStores unindexed 0 0
      let dataSizeExpr :=
        if hasUnindexedDynamicData then YulExpr.ident "__evt_data_tail" else YulExpr.lit unindexedHeadSize
      let indexedTopicParts ← indexed.zipIdx.mapM fun ((p, srcExpr, argExpr), idx) => do
        match p.ty with
        | ParamType.bytes =>
            match srcExpr with
            | Expr.param name =>
                let topicName := s!"__evt_topic{idx + 1}"
                let hashStmts :=
                  dynamicCopyData dynamicSource
                    (YulExpr.ident "__evt_ptr")
                    (YulExpr.ident s!"{name}_data_offset")
                    (YulExpr.ident s!"{name}_length") ++ [
                  YulStmt.let_ topicName (YulExpr.call "keccak256" [
                    YulExpr.ident "__evt_ptr",
                    YulExpr.ident s!"{name}_length"
                  ])
                ]
                pure (hashStmts, YulExpr.ident topicName)
            | _ =>
                throw s!"Compilation error: indexed bytes event param '{p.name}' in event '{eventName}' currently requires direct bytes parameter reference ({issue586Ref})."
        | ParamType.array elemTy =>
            match elemTy with
            | ParamType.bytes =>
                match srcExpr with
                | Expr.param name =>
                    let topicName := s!"__evt_topic{idx + 1}"
                    let tailLenName := s!"__evt_arg{idx}_tail_len"
                    let loopIndexName := s!"__evt_arg{idx}_i"
                    let elemOffsetName := s!"__evt_arg{idx}_elem_offset"
                    let elemLenPosName := s!"__evt_arg{idx}_elem_len_pos"
                    let elemLenName := s!"__evt_arg{idx}_elem_len"
                    let elemDataName := s!"__evt_arg{idx}_elem_data"
                    let elemDstName := s!"__evt_arg{idx}_elem_dst"
                    let elemPaddedName := s!"__evt_arg{idx}_elem_padded"
                    let hashStmts := [
                      YulStmt.let_ tailLenName (YulExpr.lit 0),
                      YulStmt.for_
                        [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
                        (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident s!"{name}_length"])
                        [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
                        ([
                          YulStmt.let_ elemOffsetName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                            YulExpr.ident s!"{name}_data_offset",
                            YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit 32]
                          ])),
                          YulStmt.let_ elemLenPosName (YulExpr.call "add" [
                            YulExpr.ident s!"{name}_data_offset",
                            YulExpr.ident elemOffsetName
                          ]),
                          YulStmt.let_ elemLenName (dynamicWordLoad dynamicSource (YulExpr.ident elemLenPosName)),
                          YulStmt.let_ elemDataName (YulExpr.call "add" [YulExpr.ident elemLenPosName, YulExpr.lit 32]),
                          YulStmt.let_ elemDstName (YulExpr.call "add" [
                            YulExpr.ident "__evt_ptr",
                            YulExpr.ident tailLenName
                          ])
                        ] ++ dynamicCopyData dynamicSource
                          (YulExpr.ident elemDstName)
                          (YulExpr.ident elemDataName)
                          (YulExpr.ident elemLenName) ++ [
                          YulStmt.let_ elemPaddedName (YulExpr.call "and" [
                            YulExpr.call "add" [YulExpr.ident elemLenName, YulExpr.lit 31],
                            YulExpr.call "not" [YulExpr.lit 31]
                          ]),
                          YulStmt.expr (YulExpr.call "mstore" [
                            YulExpr.call "add" [YulExpr.ident elemDstName, YulExpr.ident elemLenName],
                            YulExpr.lit 0
                          ]),
                          YulStmt.assign tailLenName (YulExpr.call "add" [
                            YulExpr.ident tailLenName,
                            YulExpr.ident elemPaddedName
                          ])
                        ]),
                      YulStmt.let_ topicName (YulExpr.call "keccak256" [
                        YulExpr.ident "__evt_ptr",
                        YulExpr.ident tailLenName
                      ])
                    ]
                    pure (hashStmts, YulExpr.ident topicName)
                | _ =>
                    throw s!"Compilation error: indexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
            | _ =>
                if indexedDynamicArrayElemSupported elemTy then
                  match srcExpr with
                  | Expr.param name =>
                      let topicName := s!"__evt_topic{idx + 1}"
                      let byteLenName := s!"__evt_arg{idx}_byte_len"
                      let elemWordSize := eventHeadWordSize elemTy
                      let elemBaseName := s!"__evt_arg{idx}_elem_base"
                      let elemOutBaseName := s!"__evt_arg{idx}_out_base"
                      let loopIndexName := s!"__evt_arg{idx}_i"
                      let leafStores :=
                        (staticCompositeLeafTypeOffsets 0 elemTy).map fun (leafOffset, leafTy) =>
                          let loadExpr := dynamicWordLoad dynamicSource (YulExpr.call "add" [
                            YulExpr.ident elemBaseName,
                            YulExpr.lit leafOffset
                          ])
                          YulStmt.expr (YulExpr.call "mstore" [
                            YulExpr.call "add" [
                              YulExpr.ident elemOutBaseName,
                              YulExpr.lit leafOffset
                            ],
                            normalizeEventWord leafTy loadExpr
                          ])
                      let hashStmts := [
                        YulStmt.let_ byteLenName (YulExpr.call "mul" [
                          YulExpr.ident s!"{name}_length",
                          YulExpr.lit elemWordSize
                        ]),
                        YulStmt.for_
                          [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
                          (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident s!"{name}_length"])
                          [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
                          ([
                            YulStmt.let_ elemBaseName (YulExpr.call "add" [
                              YulExpr.ident s!"{name}_data_offset",
                              YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                            ]),
                            YulStmt.let_ elemOutBaseName (YulExpr.call "add" [
                              YulExpr.ident "__evt_ptr",
                              YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                            ])
                          ] ++ leafStores),
                        YulStmt.let_ topicName (YulExpr.call "keccak256" [
                          YulExpr.ident "__evt_ptr",
                          YulExpr.ident byteLenName
                        ])
                      ]
                      pure (hashStmts, YulExpr.ident topicName)
                  | _ =>
                      throw s!"Compilation error: indexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                else if eventIsDynamicType elemTy then
                  match srcExpr with
                  | Expr.param name =>
                      let topicName := s!"__evt_topic{idx + 1}"
                      let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
                      let (encodeStmts, encodeLen) ←
                        compileIndexedInPlaceEncoding dynamicSource p.ty srcBase (YulExpr.ident "__evt_ptr") s!"__evt_arg{idx}_indexed"
                      pure (encodeStmts ++ [YulStmt.let_ topicName (YulExpr.call "keccak256" [
                        YulExpr.ident "__evt_ptr",
                        encodeLen
                      ])], YulExpr.ident topicName)
                  | _ =>
                      throw s!"Compilation error: indexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                else
                  throw s!"Compilation error: indexed array event param '{p.name}' in event '{eventName}' has unsupported element type {repr elemTy} ({issue586Ref})."
        | ParamType.fixedArray _ _ | ParamType.tuple _ =>
            if eventIsDynamicType p.ty then
              match srcExpr with
              | Expr.param name =>
                  let topicName := s!"__evt_topic{idx + 1}"
                  let srcBase := indexedDynamicBaseOffsetExpr dynamicSource name
                  let (encodeStmts, encodeLen) ←
                    compileIndexedInPlaceEncoding dynamicSource p.ty srcBase (YulExpr.ident "__evt_ptr") s!"__evt_arg{idx}_indexed"
                  pure (encodeStmts ++ [YulStmt.let_ topicName (YulExpr.call "keccak256" [
                    YulExpr.ident "__evt_ptr",
                    encodeLen
                  ])], YulExpr.ident topicName)
              | _ =>
                  throw s!"Compilation error: indexed dynamic composite event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
            else
              match srcExpr with
              | Expr.param name =>
                  let topicName := s!"__evt_topic{idx + 1}"
                  let leaves := staticCompositeLeaves name p.ty
                  let stores := leaves.zipIdx.map fun ((leafTy, leafExpr), wordIdx) =>
                    YulStmt.expr (YulExpr.call "mstore" [
                      YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit (wordIdx * 32)],
                      normalizeEventWord leafTy leafExpr
                    ])
                  pure (stores ++ [YulStmt.let_ topicName (YulExpr.call "keccak256" [
                    YulExpr.ident "__evt_ptr",
                    YulExpr.lit (eventHeadWordSize p.ty)
                  ])], YulExpr.ident topicName)
              | _ =>
                  throw s!"Compilation error: indexed static composite event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
        | ParamType.address =>
            pure ([], YulExpr.call "and" [argExpr, YulExpr.hex addressMask])
        | ParamType.bool =>
            pure ([], yulToBool argExpr)
        | _ =>
            pure ([], argExpr)
      let indexedTopicStmts := indexedTopicParts.flatMap (·.1)
      let topicExprs := [YulExpr.ident "__evt_topic0"] ++ indexedTopicParts.map (·.2)
      let logFn := match indexed.length with
        | 0 => "log1"
        | 1 => "log2"
        | 2 => "log3"
        | _ => "log4"
      let logArgs := [YulExpr.ident "__evt_ptr", dataSizeExpr] ++ topicExprs
      let logStmt := YulStmt.expr (YulExpr.call logFn logArgs)
      pure [YulStmt.block ([storePtr] ++ sigStores ++ [topic0Store] ++ indexedTopicStmts ++ unindexedTailInit ++ unindexedStores ++ [logStmt])]

  | Stmt.internalCall functionName args => do
      -- Internal function call as statement (#181)
      let argExprs ← compileExprList fields dynamicSource args
      pure [YulStmt.expr (YulExpr.call (internalFunctionYulName functionName) argExprs)]
  | Stmt.internalCallAssign names functionName args => do
      let argExprs ← compileExprList fields dynamicSource args
      pure [YulStmt.letMany names (YulExpr.call (internalFunctionYulName functionName) argExprs)]
  | Stmt.externalCallBind resultVars externalName args => do
      let argExprs ← compileExprList fields dynamicSource args
      pure [YulStmt.letMany resultVars (YulExpr.call externalName argExprs)]
  -- NOTE: safeTransfer, safeTransferFrom, externalCallWithReturn, callback, ecrecover
  -- have been removed. Use Stmt.ecm with the appropriate module from Compiler/Modules/.
  | Stmt.ecm mod args => do
      if args.length != mod.numArgs then
        throw s!"ECM '{mod.name}': expected {mod.numArgs} arguments, got {args.length}"
      let compiledArgs ← compileExprList fields dynamicSource args
      let ctx : ECM.CompilationContext := {
        isDynamicFromCalldata := dynamicSource == .calldata
      }
      mod.compile ctx compiledArgs
  | Stmt.returnValues values => do
      if isInternal then
        if values.length != internalRetNames.length then
          throw s!"Compilation error: internal return arity mismatch: expected {internalRetNames.length}, got {values.length}"
        else
          let compiled ← compileExprList fields dynamicSource values
          let assigns := (internalRetNames.zip compiled).map fun (name, valueExpr) =>
            YulStmt.assign name valueExpr
          pure (assigns ++ [YulStmt.leave])
      else if values.isEmpty then
        pure [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 0])]
      else
        let compiled ← compileExprList fields dynamicSource values
        let stores := (compiled.zipIdx.map fun (valueExpr, idx) =>
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit (idx * 32), valueExpr]))
        pure (stores ++ [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit (values.length * 32)])])
  | Stmt.returnArray name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      let byteLen := YulExpr.call "mul" [lenIdent, YulExpr.lit 32]
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
      ] ++ dynamicCopyData dynamicSource (YulExpr.lit 64) dataOffset byteLen ++ [
        YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.call "add" [YulExpr.lit 64, byteLen]])
      ])
  | Stmt.returnBytes name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      let tailOffset := YulExpr.call "add" [YulExpr.lit 64, lenIdent]
      let paddedLen :=
        YulExpr.call "and" [
          YulExpr.call "add" [lenIdent, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
      ] ++ dynamicCopyData dynamicSource (YulExpr.lit 64) dataOffset lenIdent ++ [
        YulStmt.expr (YulExpr.call "mstore" [tailOffset, YulExpr.lit 0]),
        YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.call "add" [YulExpr.lit 64, paddedLen]])
      ])
  | Stmt.returnStorageWords name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      pure [
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
        YulStmt.for_
          [YulStmt.let_ "__i" (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident "__i", lenIdent])
          [YulStmt.assign "__i" (YulExpr.call "add" [YulExpr.ident "__i", YulExpr.lit 1])]
          [
            YulStmt.let_ "__slot" (dynamicWordLoad dynamicSource (YulExpr.call "add" [
              dataOffset,
              YulExpr.call "mul" [YulExpr.ident "__i", YulExpr.lit 32]
            ])),
            YulStmt.expr (YulExpr.call "mstore" [
              YulExpr.call "add" [YulExpr.lit 64, YulExpr.call "mul" [YulExpr.ident "__i", YulExpr.lit 32]],
              YulExpr.call "sload" [YulExpr.ident "__slot"]
            ])
          ],
        YulStmt.expr (YulExpr.call "return" [
          YulExpr.lit 0,
          YulExpr.call "add" [YulExpr.lit 64, YulExpr.call "mul" [lenIdent, YulExpr.lit 32]]
        ])
      ]
  | Stmt.mstore offset value => do
      pure [YulStmt.expr (YulExpr.call "mstore" [
        ← compileExpr fields dynamicSource offset,
        ← compileExpr fields dynamicSource value
      ])]
  | Stmt.calldatacopy destOffset sourceOffset size => do
      pure [YulStmt.expr (YulExpr.call "calldatacopy" [
        ← compileExpr fields dynamicSource destOffset,
        ← compileExpr fields dynamicSource sourceOffset,
        ← compileExpr fields dynamicSource size
      ])]
  | Stmt.returndataCopy destOffset sourceOffset size => do
      pure [YulStmt.expr (YulExpr.call "returndatacopy" [
        ← compileExpr fields dynamicSource destOffset,
        ← compileExpr fields dynamicSource sourceOffset,
        ← compileExpr fields dynamicSource size
      ])]
  | Stmt.revertReturndata =>
      pure [YulStmt.block [
        YulStmt.let_ "__returndata_size" (YulExpr.call "returndatasize" []),
        YulStmt.expr (YulExpr.call "returndatacopy" [
          YulExpr.lit 0,
          YulExpr.lit 0,
          YulExpr.ident "__returndata_size"
        ]),
        YulStmt.expr (YulExpr.call "revert" [
          YulExpr.lit 0,
          YulExpr.ident "__returndata_size"
        ])
      ]]
  | Stmt.rawLog topics dataOffset dataSize => do
      if topics.length > 4 then
        throw s!"Compilation error: rawLog supports at most 4 topics (log0–log4), got {topics.length}"
      let topicExprs ← compileExprList fields dynamicSource topics
      let offsetExpr ← compileExpr fields dynamicSource dataOffset
      let sizeExpr ← compileExpr fields dynamicSource dataSize
      let logFn := s!"log{topics.length}"
      pure [YulStmt.expr (YulExpr.call logFn ([offsetExpr, sizeExpr] ++ topicExprs))]
end

private def isScalarParamType : ParamType → Bool
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 => true
  | _ => false

private def genDynamicParamLoads
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr) (headSize : Nat)
    (baseOffset : Nat) (name : String) (ty : ParamType) (headOffset : Nat) :
    List YulStmt :=
  let offsetLoad := YulStmt.let_ s!"{name}_offset"
    (loadWord (YulExpr.lit headOffset))
  let relativeOffset := YulExpr.ident s!"{name}_offset"
  let absoluteOffsetExpr :=
    if baseOffset == 0 then
      relativeOffset
    else
      YulExpr.call "add" [YulExpr.lit baseOffset, relativeOffset]
  let absoluteOffsetName := s!"{name}_abs_offset"
  let absoluteOffsetLoad := YulStmt.let_ absoluteOffsetName absoluteOffsetExpr
  let absoluteOffset := YulExpr.ident absoluteOffsetName
  let offsetBoundsCheck := YulStmt.if_ (YulExpr.call "lt" [relativeOffset, YulExpr.lit headSize]) [
    YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
  ]
  let absoluteBoundsCheck := YulStmt.if_ (YulExpr.call "gt" [
    absoluteOffset,
    YulExpr.call "sub" [sizeExpr, YulExpr.lit 32]
  ]) [
    YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
  ]
  let lengthLoad := YulStmt.let_ s!"{name}_length"
    (loadWord absoluteOffset)
  let tailHeadEndName := s!"{name}_tail_head_end"
  let tailHeadEndLoad := YulStmt.let_ tailHeadEndName
    (YulExpr.call "add" [absoluteOffset, YulExpr.lit 32])
  let tailRemainingName := s!"{name}_tail_remaining"
  let tailRemainingLoad := YulStmt.let_ tailRemainingName
    (YulExpr.call "sub" [sizeExpr, YulExpr.ident tailHeadEndName])
  let lengthBoundsCheck :=
    match ty with
    | ParamType.bytes =>
        [YulStmt.if_ (YulExpr.call "gt" [
            YulExpr.ident s!"{name}_length",
            YulExpr.ident tailRemainingName
          ]) [
            YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
          ]]
    | ParamType.array _ =>
        [YulStmt.if_ (YulExpr.call "gt" [
            YulExpr.ident s!"{name}_length",
            YulExpr.call "div" [YulExpr.ident tailRemainingName, YulExpr.lit 32]
          ]) [
            YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
          ]]
    | _ => []
  let dataOffsetLoad := YulStmt.let_ s!"{name}_data_offset"
    (YulExpr.ident tailHeadEndName)
  [offsetLoad, offsetBoundsCheck, absoluteOffsetLoad, absoluteBoundsCheck, lengthLoad, tailHeadEndLoad, tailRemainingLoad]
    ++ lengthBoundsCheck ++ [dataOffsetLoad]

private def genScalarLoad
    (loadWord : YulExpr → YulExpr) (name : String) (ty : ParamType) (offset : Nat) :
    List YulStmt :=
  let load := loadWord (YulExpr.lit offset)
  match ty with
  | ParamType.uint256 =>
      [YulStmt.let_ name load]
  | ParamType.uint8 =>
      [YulStmt.let_ name (YulExpr.call "and" [load, YulExpr.lit 255])]
  | ParamType.bytes32 =>
      [YulStmt.let_ name load]
  | ParamType.address =>
      [YulStmt.let_ name (YulExpr.call "and" [
        load,
        YulExpr.hex addressMask
      ])]
  | ParamType.bool =>
      let boolWord := s!"__abi_bool_word_{offset}"
      [ YulStmt.let_ boolWord load
      , YulStmt.if_ (YulExpr.call "iszero" [
          YulExpr.call "or" [
            YulExpr.call "eq" [YulExpr.ident boolWord, YulExpr.lit 0],
            YulExpr.call "eq" [YulExpr.ident boolWord, YulExpr.lit 1]
          ]
        ]) [
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
        ]
      , YulStmt.let_ name (YulExpr.call "iszero" [YulExpr.call "iszero" [
          YulExpr.ident boolWord
        ]])
      ]
  | _ => []

private partial def genStaticTypeLoads
    (loadWord : YulExpr → YulExpr) (name : String) (ty : ParamType) (offset : Nat) :
    List YulStmt :=
  match ty with
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      genScalarLoad loadWord name ty offset
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap fun i =>
        genStaticTypeLoads loadWord s!"{name}_{i}" elemTy (offset + i * paramHeadSize elemTy)
  | ParamType.tuple elemTys =>
      let rec go (tys : List ParamType) (idx : Nat) (curOffset : Nat) : List YulStmt :=
        match tys with
        | [] => []
        | elemTy :: rest =>
            let elemName := s!"{name}_{idx}"
            let here := genStaticTypeLoads loadWord elemName elemTy curOffset
            here ++ go rest (idx + 1) (curOffset + paramHeadSize elemTy)
      go elemTys 0 offset
  | _ => []

private def genParamLoadsFrom
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headStart : Nat) (baseOffset : Nat) (params : List Param) :
    List YulStmt :=
  let headSize := (params.map (fun p => paramHeadSize p.ty)).foldl (· + ·) 0
  let minInputSizeCheck :=
    YulStmt.if_ (YulExpr.call "lt" [sizeExpr, YulExpr.lit (baseOffset + headSize)]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
  let rec go (paramList : List Param) (headOffset : Nat) : List YulStmt :=
    match paramList with
    | [] => []
    | param :: rest =>
      let stmts := match param.ty with
        | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
          genScalarLoad loadWord param.name param.ty headOffset
        | ParamType.tuple elemTypes =>
          if isDynamicParamType param.ty then
            genDynamicParamLoads loadWord sizeExpr headSize baseOffset param.name param.ty headOffset
          else
            genStaticTypeLoads loadWord param.name (ParamType.tuple elemTypes) headOffset
        | ParamType.array _ =>
          genDynamicParamLoads loadWord sizeExpr headSize baseOffset param.name param.ty headOffset
        | ParamType.fixedArray _ n =>
          -- Static fixed arrays are decoded inline recursively (including nested tuple members).
          -- For scalar element arrays we preserve `<name>` as an alias to `<name>_0`.
          if isDynamicParamType param.ty then
            genDynamicParamLoads loadWord sizeExpr headSize baseOffset param.name param.ty headOffset
          else
            let staticLoads := genStaticTypeLoads loadWord param.name param.ty headOffset
            if n == 0 then staticLoads else
              -- Backward compatibility: keep `<name>` bound to first element for scalar fixed arrays.
              let firstAlias := match param.ty with
                | ParamType.fixedArray elemTy _ =>
                    if isScalarParamType elemTy then
                      [YulStmt.let_ param.name (YulExpr.ident s!"{param.name}_0")]
                    else
                      []
                | _ => []
              staticLoads ++ firstAlias
        | ParamType.bytes =>
          genDynamicParamLoads loadWord sizeExpr headSize baseOffset param.name param.ty headOffset
      stmts ++ go rest (headOffset + paramHeadSize param.ty)
  minInputSizeCheck :: go params headStart

-- Generate parameter loading code (from calldata)
def genParamLoads (params : List Param) : List YulStmt :=
  genParamLoadsFrom (fun pos => YulExpr.call "calldataload" [pos]) (YulExpr.call "calldatasize" []) 4 4 params

private def pickFreshInternalRetName (usedNames : List String) (idx : Nat) : String :=
  pickFreshName s!"__ret{idx}" usedNames

private def freshInternalRetNames (returns : List ParamType) (usedNames : List String) : List String :=
  let (_, namesRev) := returns.zipIdx.foldl
    (fun (acc : List String × List String) (_retTy, idx) =>
      let (used, names) := acc
      let fresh := pickFreshInternalRetName used idx
      (fresh :: used, fresh :: names))
    (usedNames, [])
  namesRev.reverse

-- Compile internal function to a Yul function definition (#181)
def compileInternalFunction (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (spec : FunctionSpec) :
    Except String YulStmt := do
  validateFunctionSpec spec
  let returns ← functionReturns spec
  let paramNames := spec.params.map (·.name)
  let usedNames := paramNames ++ collectStmtListBindNames spec.body
  let retNames := freshInternalRetNames returns usedNames
  let bodyStmts ← compileStmtList fields events errors .calldata retNames true
    (paramNames ++ retNames) spec.body
  pure (YulStmt.funcDef (internalFunctionYulName spec.name) paramNames retNames bodyStmts)

-- Compile function spec to IR function
def compileFunctionSpec (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) :
    Except String IRFunction := do
  validateFunctionSpec spec
  let returns ← functionReturns spec
  let paramLoads := genParamLoads spec.params
  let bodyStmts ← compileStmtList fields events errors .calldata [] false
    (spec.params.map (·.name)) spec.body
  let allStmts := paramLoads ++ bodyStmts
  let retType := match returns with
    | [single] => single.toIRType
    | _ => IRType.unit
  return {
    name := spec.name
    selector := selector
    params := spec.params.map Param.toIRParam
    ret := retType
    payable := spec.isPayable
    body := allStmts
  }

private def compileSpecialEntrypoint (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (spec : FunctionSpec) :
    Except String IREntrypoint := do
  let bodyChunks ← compileStmtList fields events errors .calldata [] false [] spec.body
  pure {
    payable := spec.isPayable
    body := bodyChunks
  }

private def pickUniqueFunctionByName (name : String) (funcs : List FunctionSpec) :
    Except String (Option FunctionSpec) :=
  match funcs.filter (·.name == name) with
  | [] => pure none
  | [single] => pure (some single)
  | _ => throw s!"Compilation error: multiple '{name}' entrypoints are not allowed ({issue586Ref})"

-- Check if contract uses mappings
def usesMapping (fields : List Field) : Bool :=
  fields.any fun f => isMapping fields f.name

private def constructorArgAliases (params : List Param) : List YulStmt :=
  let rec go (ps : List Param) (idx : Nat) (headOffset : Nat) : List YulStmt :=
    match ps with
    | [] => []
    | param :: rest =>
        let source := if isDynamicParamType param.ty then
          YulExpr.ident s!"{param.name}_offset"
        else
          match param.ty with
          | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
              YulExpr.ident param.name
          | _ =>
              YulExpr.call "mload" [YulExpr.lit headOffset]
        let alias := YulStmt.let_ s!"arg{idx}" source
        alias :: go rest (idx + 1) (headOffset + paramHeadSize param.ty)
  go params 0 0

-- Generate constructor argument loading code (from appended initcode args)
def genConstructorArgLoads (params : List Param) : List YulStmt :=
  if params.isEmpty then []
  else
    let argsOffset := YulExpr.call "add" [
      YulExpr.call "dataoffset" [YulExpr.str "runtime"],
      YulExpr.call "datasize" [YulExpr.str "runtime"]
    ]
    let initcodeArgCopy := [
      YulStmt.let_ "argsOffset" argsOffset,
      YulStmt.let_ "argsSize"
        (YulExpr.call "sub" [YulExpr.call "codesize" [], YulExpr.ident "argsOffset"]),
      YulStmt.expr (YulExpr.call "codecopy" [YulExpr.lit 0, YulExpr.ident "argsOffset", YulExpr.ident "argsSize"])
    ]
    let paramLoads := genParamLoadsFrom (fun pos => YulExpr.call "mload" [pos]) (YulExpr.ident "argsSize") 0 0 params
    initcodeArgCopy ++ paramLoads ++ constructorArgAliases params

-- Compile deploy code (constructor)
-- Note: Don't append datacopy/return here - Codegen.deployCode does that
def compileConstructor (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (ctor : Option ConstructorSpec) :
    Except String (List YulStmt) := do
  match ctor with
  | none => return []
  | some spec =>
    let argLoads := genConstructorArgLoads spec.params
    let bodyChunks ← compileStmtList fields events errors .memory [] false [] spec.body
    return argLoads ++ bodyChunks

-- Main compilation function
-- NOTE: this is the pure core compiler and does *not* verify canonical
-- selector/signature correspondence (it only checks count/duplicates).
-- Use `Compiler.Selector.compileChecked` on caller-provided selector lists.
-- WARNING: Order matters! If selector list is reordered but function list isn't,
-- functions will be mapped to wrong selectors with no runtime error.


def compile (spec : CompilationModel) (selectors : List Nat) : Except String IRContract := do
  validateIdentifierShapes spec
  match firstInvalidSlotAliasRange spec.slotAliasRanges with
  | some (idx, range) =>
      throw s!"Compilation error: slotAliasRanges[{idx}] has invalid source interval {range.sourceStart}..{range.sourceEnd} in {spec.name} ({issue623Ref}). slotAliasRanges require sourceStart <= sourceEnd."
  | none =>
      pure ()
  match firstSlotAliasSourceOverlap spec.slotAliasRanges with
  | some (idxA, a, idxB, b) =>
      throw s!"Compilation error: slotAliasRanges[{idxA}]={a.sourceStart}..{a.sourceEnd} and slotAliasRanges[{idxB}]={b.sourceStart}..{b.sourceEnd} overlap in source slots in {spec.name} ({issue623Ref}). Ensure slotAliasRanges source intervals are disjoint."
  | none =>
      pure ()
  let fields := applySlotAliasRanges spec.fields spec.slotAliasRanges
  let externalFns := spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)
  let internalFns := spec.functions.filter (·.isInternal)
  match firstInternalDynamicParam spec.functions with
  | some (fnName, paramName, ty) =>
      throw s!"Compilation error: internal function '{fnName}' parameter '{paramName}' has dynamic type {repr ty}, which is currently unsupported ({issue753Ref}). Internal dynamic ABI lowering is not implemented yet."
  | none =>
      pure ()
  match firstDuplicateFunctionParamName spec.functions with
  | some (fnName, dup) =>
      throw s!"Compilation error: duplicate parameter name '{dup}' in function '{fnName}'"
  | none =>
      pure ()
  match firstDuplicateConstructorParamName spec.constructor with
  | some dup =>
      throw s!"Compilation error: duplicate parameter name '{dup}' in constructor"
  | none =>
      pure ()
  for fn in spec.functions do
    validateFunctionSpec fn
    validateInteropFunctionSpec fn
    validateSpecialEntrypointSpec fn
    validateEventArgShapesInFunction fn spec.events
    validateCustomErrorArgShapesInFunction fn spec.errors
    validateInternalCallShapesInFunction spec.functions fn
    validateExternalCallTargetsInFunction spec.externals fn
  validateConstructorSpec spec.constructor
  validateInteropConstructorSpec spec.constructor
  validateExternalCallTargetsInConstructor spec.externals spec.constructor
  match spec.constructor with
  | none => pure ()
  | some ctor => do
      ctor.body.forM (validateEventArgShapesInStmt "constructor" ctor.params spec.events)
      ctor.body.forM (validateCustomErrorArgShapesInStmt "constructor" ctor.params spec.errors)
      ctor.body.forM (validateInternalCallShapesInStmt spec.functions "constructor")
  for ext in spec.externals do
    let _ ← externalFunctionReturns ext
    validateInteropExternalSpec ext
  match firstDuplicateName (spec.functions.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate function name '{dup}' in {spec.name}"
  | none =>
      pure ()
  match firstDuplicateName (spec.errors.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate custom error declaration '{dup}'"
  | none =>
      pure ()
  match firstDuplicateName (spec.fields.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate field name '{dup}' in {spec.name}"
  | none =>
      pure ()
  match firstInvalidPackedBits spec.fields with
  | some (fieldName, packed) =>
      throw s!"Compilation error: field '{fieldName}' has invalid packedBits offset={packed.offset} width={packed.width} in {spec.name} ({issue623Ref}). Require 0 < width <= 256, offset < 256, and offset + width <= 256."
  | none =>
      pure ()
  match firstMappingPackedBits spec.fields with
  | some fieldName =>
      throw s!"Compilation error: field '{fieldName}' is a mapping and cannot declare packedBits in {spec.name} ({issue623Ref}). Packed subfields are only supported for value-word fields."
  | none =>
      pure ()
  firstInvalidStructField spec.fields
  match firstFieldWriteSlotConflict fields with
  | some (slot, existingField, conflictingField) =>
      throw s!"Compilation error: storage slot {slot} has overlapping write ranges for '{existingField}' and '{conflictingField}' in {spec.name} ({issue623Ref}). Ensure full-slot writes are unique and packed bit ranges are disjoint per slot."
  | none =>
      pure ()
  match firstInvalidReservedRange spec.reservedSlotRanges with
  | some (idx, range) =>
      throw s!"Compilation error: reservedSlotRanges[{idx}] has invalid interval {range.start}..{range.end_} in {spec.name} ({issue623Ref}). Reserved slot range start must be <= end."
  | none =>
      pure ()
  match firstReservedRangeOverlap spec.reservedSlotRanges with
  | some (idxA, a, idxB, b) =>
      throw s!"Compilation error: reserved slot ranges reservedSlotRanges[{idxA}]={a.start}..{a.end_} and reservedSlotRanges[{idxB}]={b.start}..{b.end_} overlap in {spec.name} ({issue623Ref}). Ensure reserved ranges are disjoint."
  | none =>
      pure ()
  match firstReservedSlotWriteConflict fields spec.reservedSlotRanges with
  | some (slot, ownerName, rangeIdx, range) =>
      throw s!"Compilation error: field write slot {slot} ('{ownerName}') overlaps reservedSlotRanges[{rangeIdx}]={range.start}..{range.end_} in {spec.name} ({issue623Ref}). Adjust field slot/aliasSlots or reservedSlotRanges."
  | none =>
      pure ()
  match firstDuplicateName (spec.events.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate event name '{dup}' in {spec.name}"
  | none =>
      pure ()
  for eventDef in spec.events do
    validateEventDef eventDef
  match firstDuplicateEventParamName spec.events with
  | some (evName, dup) =>
      throw s!"Compilation error: duplicate parameter name '{dup}' in event '{evName}'"
  | none =>
      pure ()
  match firstDuplicateName (spec.externals.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate external declaration '{dup}' in {spec.name}"
  | none =>
      pure ()
  let mappingHelpersRequired := usesMapping fields
  let arrayHelpersRequired := contractUsesArrayElement spec
  match firstReservedExternalCollision spec mappingHelpersRequired arrayHelpersRequired with
  | some name =>
      if name.startsWith internalFunctionPrefix then
        throw s!"Compilation error: external declaration '{name}' uses reserved prefix '{internalFunctionPrefix}' ({issue756Ref})."
      else
        throw s!"Compilation error: external declaration '{name}' collides with compiler-generated/reserved symbol '{name}' ({issue756Ref}). Rename the external wrapper."
  | none =>
      pure ()
  for err in spec.errors do
    validateErrorDef err
  let fallbackSpec ← pickUniqueFunctionByName "fallback" spec.functions
  let receiveSpec ← pickUniqueFunctionByName "receive" spec.functions
  if externalFns.length != selectors.length then
    throw s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {externalFns.length} external functions"
  match firstDuplicateSelector selectors with
  | some dup =>
      let names := selectorNames spec selectors dup
      let nameStr := if names.isEmpty then "<unknown>" else String.intercalate ", " names
      throw s!"Selector collision in {spec.name}: {dup} assigned to {nameStr}"
  | none => pure ()
  let functions ← (externalFns.zip selectors).mapM fun (fnSpec, sel) =>
    compileFunctionSpec fields spec.events spec.errors sel fnSpec
  -- Compile internal functions as Yul function definitions (#181)
  let internalFuncDefs ← internalFns.mapM (compileInternalFunction fields spec.events spec.errors)
  let arrayElementHelpers :=
    if arrayHelpersRequired then
      [checkedArrayElementCalldataHelper, checkedArrayElementMemoryHelper]
    else
      []
  let fallbackEntrypoint ← fallbackSpec.mapM (compileSpecialEntrypoint fields spec.events spec.errors)
  let receiveEntrypoint ← receiveSpec.mapM (compileSpecialEntrypoint fields spec.events spec.errors)
  return {
    name := spec.name
    deploy := (← compileConstructor fields spec.events spec.errors spec.constructor)
    constructorPayable := spec.constructor.map (·.isPayable) |>.getD false
    functions := functions
    fallbackEntrypoint := fallbackEntrypoint
    receiveEntrypoint := receiveEntrypoint
    usesMapping := mappingHelpersRequired
    internalFunctions := arrayElementHelpers ++ internalFuncDefs
  }


end Compiler.CompilationModel
