/- 
  Compiler.CompilationModel.ParamLoading: ABI parameter decoding helpers

  This module isolates calldata/initcode parameter loading so dispatch and
  constructor assembly do not depend on the full statement compiler body.
-/
import Compiler.CompilationModel.AbiTypeLayout

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

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

def genParamLoads (params : List Param) : List YulStmt :=
  genParamLoadsFrom (fun pos => YulExpr.call "calldataload" [pos]) (YulExpr.call "calldatasize" []) 4 4 params

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

end Compiler.CompilationModel
