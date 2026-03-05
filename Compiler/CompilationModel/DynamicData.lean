import Compiler.Yul.Ast

namespace Compiler.CompilationModel

open Compiler.Yul

inductive DynamicDataSource where
  | calldata
  | memory
  deriving DecidableEq

def dynamicWordLoad (source : DynamicDataSource) (offset : YulExpr) : YulExpr :=
  match source with
  | .calldata => YulExpr.call "calldataload" [offset]
  | .memory => YulExpr.call "mload" [offset]

def checkedArrayElementCalldataHelperName : String :=
  "__verity_array_element_calldata_checked"

def checkedArrayElementMemoryHelperName : String :=
  "__verity_array_element_memory_checked"

private def checkedArrayElementHelper (helperName loadOp : String) : YulStmt :=
  YulStmt.funcDef helperName ["data_offset", "length", "index"] ["word"] [
    YulStmt.if_ (YulExpr.call "iszero" [
      YulExpr.call "lt" [YulExpr.ident "index", YulExpr.ident "length"]
    ]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ],
    YulStmt.assign "word" (YulExpr.call loadOp [
      YulExpr.call "add" [
        YulExpr.ident "data_offset",
        YulExpr.call "mul" [YulExpr.ident "index", YulExpr.lit 32]
      ]
    ])
  ]

def checkedArrayElementCalldataHelper : YulStmt :=
  checkedArrayElementHelper checkedArrayElementCalldataHelperName "calldataload"

def checkedArrayElementMemoryHelper : YulStmt :=
  checkedArrayElementHelper checkedArrayElementMemoryHelperName "mload"

def dynamicCopyData (source : DynamicDataSource)
    (destOffset sourceOffset len : YulExpr) : List YulStmt :=
  match source with
  | .calldata =>
      [YulStmt.expr (YulExpr.call "calldatacopy" [destOffset, sourceOffset, len])]
  | .memory =>
      [YulStmt.for_
        [YulStmt.let_ "__copy_i" (YulExpr.lit 0)]
        (YulExpr.call "lt" [YulExpr.ident "__copy_i", len])
        [YulStmt.assign "__copy_i" (YulExpr.call "add" [YulExpr.ident "__copy_i", YulExpr.lit 32])]
        [YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [destOffset, YulExpr.ident "__copy_i"],
          YulExpr.call "mload" [YulExpr.call "add" [sourceOffset, YulExpr.ident "__copy_i"]]
        ])]]

end Compiler.CompilationModel
