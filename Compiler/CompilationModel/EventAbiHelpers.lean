import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.AbiTypeLayout
import Compiler.CompilationModel.ExpressionCompile

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

def indexedDynamicArrayElemSupported (elemTy : ParamType) : Bool :=
  !eventIsDynamicType elemTy &&
    eventHeadWordSize elemTy > 0

def normalizeEventWord (ty : ParamType) (expr : YulExpr) : YulExpr :=
  match ty with
  | ParamType.uint8 => YulExpr.call "and" [expr, YulExpr.lit 255]
  | ParamType.address => YulExpr.call "and" [expr, YulExpr.hex addressMask]
  | ParamType.bool => yulToBool expr
  | _ => expr

partial def staticCompositeLeaves (baseName : String) (ty : ParamType) :
    List (ParamType × YulExpr) :=
  match ty with
  | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      [(ty, YulExpr.ident baseName)]
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap fun i =>
        staticCompositeLeaves s!"{baseName}_{i}" elemTy
  | ParamType.tuple elemTys =>
      let rec go (tys : List ParamType) (idx : Nat) : List (ParamType × YulExpr) :=
        match tys with
        | [] => []
        | elemTy :: rest =>
            staticCompositeLeaves s!"{baseName}_{idx}" elemTy ++ go rest (idx + 1)
      go elemTys 0
  | _ => []

partial def staticCompositeLeafTypeOffsets
    (baseOffset : Nat) (ty : ParamType) : List (Nat × ParamType) :=
  match ty with
  | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      [(baseOffset, ty)]
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap fun i =>
        staticCompositeLeafTypeOffsets (baseOffset + i * eventHeadWordSize elemTy) elemTy
  | ParamType.tuple elemTys =>
      let rec go (remaining : List ParamType) (curOffset : Nat) : List (Nat × ParamType) :=
        match remaining with
        | [] => []
        | elemTy :: rest =>
            staticCompositeLeafTypeOffsets curOffset elemTy ++
              go rest (curOffset + eventHeadWordSize elemTy)
      go elemTys baseOffset
  | _ => []

def indexedDynamicBaseOffsetExpr (dynamicSource : DynamicDataSource) (paramName : String) : YulExpr :=
  match dynamicSource with
  | .calldata => YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident s!"{paramName}_offset"]
  | .memory => YulExpr.ident s!"{paramName}_offset"

partial def compileIndexedInPlaceEncoding
    (dynamicSource : DynamicDataSource) (ty : ParamType)
    (srcBase dstBase : YulExpr) (stem : String) :
    Except String (List YulStmt × YulExpr) := do
  match ty with
  | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      let loaded := dynamicWordLoad dynamicSource srcBase
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [dstBase, normalizeEventWord ty loaded])
      ], YulExpr.lit 32)
  | ParamType.bytes | ParamType.string =>
      let lenName := s!"{stem}_len"
      let paddedName := s!"{stem}_padded"
      pure ([
        YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase)
      ] ++ dynamicCopyData dynamicSource
        dstBase
        (YulExpr.call "add" [srcBase, YulExpr.lit 32])
        (YulExpr.ident lenName) ++ [
        YulStmt.let_ paddedName (YulExpr.call "and" [
          YulExpr.call "add" [YulExpr.ident lenName, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [dstBase, YulExpr.ident lenName],
          YulExpr.lit 0
        ])
      ], YulExpr.ident paddedName)
  | ParamType.array elemTy =>
      let lenName := s!"{stem}_arr_len"
      let dataBaseName := s!"{stem}_arr_data"
      let loopIndexName := s!"{stem}_arr_i"
      let outLenName := s!"{stem}_arr_out_len"
      let elemSrcName := s!"{stem}_arr_elem_src"
      let elemDstName := s!"{stem}_arr_elem_dst"
      let initStmts := [
        YulStmt.let_ lenName (dynamicWordLoad dynamicSource srcBase),
        YulStmt.let_ dataBaseName (YulExpr.call "add" [srcBase, YulExpr.lit 32]),
        YulStmt.let_ outLenName (YulExpr.lit 0)
      ]
      let elemSrcExpr :=
        if eventIsDynamicType elemTy then
          let relName := s!"{stem}_arr_elem_rel"
          let relDecl := YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
            YulExpr.ident dataBaseName,
            YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit 32]
          ]))
          let srcDecl := YulStmt.let_ elemSrcName (YulExpr.call "add" [
            YulExpr.ident dataBaseName,
            YulExpr.ident relName
          ])
          ([relDecl, srcDecl], YulExpr.ident elemSrcName)
        else
          let srcDecl := YulStmt.let_ elemSrcName (YulExpr.call "add" [
            YulExpr.ident dataBaseName,
            YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit (eventHeadWordSize elemTy)]
          ])
          ([srcDecl], YulExpr.ident elemSrcName)
      let (elemEncodeStmts, elemEncodedLen) ←
        compileIndexedInPlaceEncoding dynamicSource elemTy (elemSrcExpr.2) (YulExpr.ident elemDstName) s!"{stem}_arr_elem"
      let loopBody :=
        elemSrcExpr.1 ++ [
          YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident outLenName])
        ] ++ elemEncodeStmts ++ [
          YulStmt.assign outLenName (YulExpr.call "add" [YulExpr.ident outLenName, elemEncodedLen])
        ]
      pure (initStmts ++ [
        YulStmt.for_
          [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident lenName])
          [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
          loopBody
      ], YulExpr.ident outLenName)
  | ParamType.fixedArray elemTy n =>
      let outLenName := s!"{stem}_fixed_out_len"
      let initStmts := [YulStmt.let_ outLenName (YulExpr.lit 0)]
      let rec goFixed (i : Nat) : Except String (List YulStmt) := do
        if i < n then
          let elemSrcName := s!"{stem}_fixed_elem_src_{i}"
          let elemDstName := s!"{stem}_fixed_elem_dst_{i}"
          let srcStmts :=
            if eventIsDynamicType elemTy then
              let relName := s!"{stem}_fixed_elem_rel_{i}"
              [
                YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                  srcBase, YulExpr.lit (i * 32)
                ])),
                YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
              ]
            else
              [YulStmt.let_ elemSrcName (YulExpr.call "add" [
                srcBase, YulExpr.lit (i * eventHeadWordSize elemTy)
              ])]
          let elemDstStmt := YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident outLenName])
          let (elemEncodeStmts, elemEncodedLen) ←
            compileIndexedInPlaceEncoding dynamicSource elemTy
              (YulExpr.ident elemSrcName)
              (YulExpr.ident elemDstName)
              s!"{stem}_fixed_elem_{i}"
          let rest ← goFixed (i + 1)
          pure (srcStmts ++ [elemDstStmt] ++ elemEncodeStmts ++ [
            YulStmt.assign outLenName (YulExpr.call "add" [YulExpr.ident outLenName, elemEncodedLen])
          ] ++ rest)
        else
          pure []
      pure (initStmts ++ (← goFixed 0), YulExpr.ident outLenName)
  | ParamType.tuple elemTys =>
      let outLenName := s!"{stem}_tuple_out_len"
      let initStmts := [YulStmt.let_ outLenName (YulExpr.lit 0)]
      let rec goTuple (remaining : List ParamType) (elemIdx headOffset : Nat) :
          Except String (List YulStmt) := do
        match remaining with
        | [] => pure []
        | elemTy :: rest =>
            let elemSrcName := s!"{stem}_tuple_elem_src_{elemIdx}"
            let elemDstName := s!"{stem}_tuple_elem_dst_{elemIdx}"
            let srcStmts :=
              if eventIsDynamicType elemTy then
                let relName := s!"{stem}_tuple_elem_rel_{elemIdx}"
                [
                  YulStmt.let_ relName (dynamicWordLoad dynamicSource (YulExpr.call "add" [
                    srcBase, YulExpr.lit headOffset
                  ])),
                  YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.ident relName])
                ]
              else
                [YulStmt.let_ elemSrcName (YulExpr.call "add" [srcBase, YulExpr.lit headOffset])]
            let elemDstStmt := YulStmt.let_ elemDstName (YulExpr.call "add" [dstBase, YulExpr.ident outLenName])
            let (elemEncodeStmts, elemEncodedLen) ←
              compileIndexedInPlaceEncoding dynamicSource elemTy
                (YulExpr.ident elemSrcName)
                (YulExpr.ident elemDstName)
                s!"{stem}_tuple_elem_{elemIdx}"
            let restStmts ← goTuple rest (elemIdx + 1) (headOffset + eventHeadWordSize elemTy)
            pure (srcStmts ++ [elemDstStmt] ++ elemEncodeStmts ++ [
              YulStmt.assign outLenName (YulExpr.call "add" [YulExpr.ident outLenName, elemEncodedLen])
            ] ++ restStmts)
      pure (initStmts ++ (← goTuple elemTys 0 0), YulExpr.ident outLenName)

end Compiler.CompilationModel
