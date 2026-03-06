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
import Compiler.CompilationModel.AbiEncoding
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.EcmAxiomCollection
import Compiler.CompilationModel.InternalNaming
import Compiler.CompilationModel.LayoutValidation
import Compiler.CompilationModel.MappingWrites
import Compiler.CompilationModel.UsageAnalysis
import Compiler.CompilationModel.ValidationHelpers
import Compiler.CompilationModel.SelectorInteropHelpers
import Compiler.CompilationModel.ExpressionCompile
import Compiler.CompilationModel.StorageWrites
import Compiler.CompilationModel.Validation

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

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
      compileSetStorage fields dynamicSource field value
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
      compileSetMapping2 fields dynamicSource field key1 key2 value
  | Stmt.setMapping2Word field key1 key2 wordOffset value =>
      compileSetMapping2Word fields dynamicSource field key1 key2 wordOffset value
  | Stmt.setMappingUint field key value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMappingUint"
  | Stmt.setStructMember field key memberName value =>
      compileSetStructMember fields dynamicSource field key memberName value
  | Stmt.setStructMember2 field key1 key2 memberName value =>
      compileSetStructMember2 fields dynamicSource field key1 key2 memberName value
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

end Compiler.CompilationModel
