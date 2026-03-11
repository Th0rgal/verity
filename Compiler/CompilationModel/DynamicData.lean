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

def checkedStorageArrayElementHelperName : String :=
  "__verity_storage_array_element_checked"

def dynamicBytesEqCalldataHelperName : String :=
  "__verity_dynamic_bytes_eq_calldata"

def dynamicBytesEqMemoryHelperName : String :=
  "__verity_dynamic_bytes_eq_memory"

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

def checkedStorageArrayElementHelper : YulStmt :=
  YulStmt.funcDef checkedStorageArrayElementHelperName ["slot", "index"] ["word"] [
    YulStmt.let_ "__array_len" (YulExpr.call "sload" [YulExpr.ident "slot"]),
    YulStmt.if_ (YulExpr.call "iszero" [
      YulExpr.call "lt" [YulExpr.ident "index", YulExpr.ident "__array_len"]
    ]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ],
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.ident "slot"]),
    YulStmt.let_ "__array_base" (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit 32]),
    YulStmt.assign "word" (YulExpr.call "sload" [
      YulExpr.call "add" [YulExpr.ident "__array_base", YulExpr.ident "index"]
    ])
  ]

private def dynamicBytesEqHelper (helperName loadOp : String) : YulStmt :=
  YulStmt.funcDef helperName
    ["lhs_data_offset", "lhs_length", "rhs_data_offset", "rhs_length"]
    ["same"] [
      YulStmt.assign "same" (YulExpr.call "eq" [YulExpr.ident "lhs_length", YulExpr.ident "rhs_length"]),
      YulStmt.for_
        [YulStmt.let_ "__cmp_i" (YulExpr.lit 0)]
        (YulExpr.call "and" [
          YulExpr.ident "same",
          YulExpr.call "lt" [YulExpr.ident "__cmp_i", YulExpr.ident "lhs_length"]
        ])
        [YulStmt.assign "__cmp_i" (YulExpr.call "add" [YulExpr.ident "__cmp_i", YulExpr.lit 1])]
        [YulStmt.if_ (YulExpr.call "iszero" [
            YulExpr.call "eq" [
              YulExpr.call "byte" [
                YulExpr.lit 0,
                YulExpr.call loadOp [
                  YulExpr.call "add" [YulExpr.ident "lhs_data_offset", YulExpr.ident "__cmp_i"]
                ]
              ],
              YulExpr.call "byte" [
                YulExpr.lit 0,
                YulExpr.call loadOp [
                  YulExpr.call "add" [YulExpr.ident "rhs_data_offset", YulExpr.ident "__cmp_i"]
                ]
              ]
            ]
          ]) [
            YulStmt.assign "same" (YulExpr.lit 0)
          ]]
    ]

def dynamicBytesEqCalldataHelper : YulStmt :=
  dynamicBytesEqHelper dynamicBytesEqCalldataHelperName "calldataload"

def dynamicBytesEqMemoryHelper : YulStmt :=
  dynamicBytesEqHelper dynamicBytesEqMemoryHelperName "mload"

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
