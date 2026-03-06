import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.AbiEncoding
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.EventAbiHelpers
import Compiler.CompilationModel.IssueRefs
import Compiler.CompilationModel.ValidationHelpers
import Compiler.CompilationModel.ExpressionCompile

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

def compileEmit (fields : List Field) (events : List EventDef)
    (dynamicSource : DynamicDataSource := .calldata)
    (eventName : String) (args : List Expr) : Except String (List YulStmt) := do
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

end Compiler.CompilationModel
