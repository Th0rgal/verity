import Compiler.Yul.PatchRulesCatalog.Base

namespace Compiler.Yul

private def incrementUint256HelperBody : List YulStmt :=
  [ .if_ (.call "eq" [.ident "value", .hex 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x11])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  , .assign "ret" (.call "add" [.ident "value", .lit 1])
  ]

private def incrementUint256HelperStmt : YulStmt :=
  .funcDef "increment_uint256" ["value"] ["ret"] incrementUint256HelperBody

def hasTopLevelFunctionNamed (stmts : List YulStmt) (name : String) : Bool :=
  stmts.any
    (fun stmt =>
      match stmt with
      | .funcDef fnName _ _ _ => fnName = name
      | _ => false)

private def insertTopLevelFuncDefAfterPrefix (stmts : List YulStmt) (funcDef : YulStmt) : List YulStmt :=
  let rec splitPrefix : List YulStmt → List YulStmt × List YulStmt
    | [] => ([], [])
    | stmt :: rest =>
        match stmt with
        | .funcDef _ _ _ _ =>
            let (pref, suff) := splitPrefix rest
            (stmt :: pref, suff)
        | _ => ([], stmt :: rest)
  let (pref, suff) := splitPrefix stmts
  pref ++ [funcDef] ++ suff

private def materializeIncrementUint256HelperIfCalled (stmts : List YulStmt) : List YulStmt × Nat :=
  let (wrapped, topStmts) :=
    match stmts with
    | [.block inner] => (true, inner)
    | _ => (false, stmts)
  if hasTopLevelFunctionNamed topStmts "increment_uint256" then
    (stmts, 0)
  else if (callNamesInStmts topStmts).any (fun called => called = "increment_uint256") then
    let inserted := insertTopLevelFuncDefAfterPrefix topStmts incrementUint256HelperStmt
    if wrapped then
      ([.block inserted], 1)
    else
      (inserted, 1)
  else
    (stmts, 0)

private def checkedSubUint256HelperBody : List YulStmt :=
  [ .assign "diff" (.call "sub" [.ident "x", .ident "y"])
  , .if_ (.call "gt" [.ident "diff", .ident "x"])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x11])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  ]

private def checkedSubUint256HelperStmt : YulStmt :=
  .funcDef "checked_sub_uint256" ["x", "y"] ["diff"] checkedSubUint256HelperBody

private def materializeCheckedSubUint256HelperIfCalled (stmts : List YulStmt) : List YulStmt × Nat :=
  let (wrapped, topStmts) :=
    match stmts with
    | [.block inner] => (true, inner)
    | _ => (false, stmts)
  if hasTopLevelFunctionNamed topStmts "checked_sub_uint256" then
    (stmts, 0)
  else if (callNamesInStmts topStmts).any (fun called => called = "checked_sub_uint256") then
    let inserted := insertTopLevelFuncDefAfterPrefix topStmts checkedSubUint256HelperStmt
    if wrapped then
      ([.block inserted], 1)
    else
      (inserted, 1)
  else
    (stmts, 0)

private def checkedAddUint256HelperBody : List YulStmt :=
  [ .assign "sum" (.call "add" [.ident "x", .ident "y"])
  , .if_ (.call "gt" [.ident "x", .ident "sum"])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x11])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  ]

private def checkedAddUint256HelperStmt : YulStmt :=
  .funcDef "checked_add_uint256" ["x", "y"] ["sum"] checkedAddUint256HelperBody

private def checkedAddUint128HelperBody : List YulStmt :=
  [ .let_ "_1" (.hex 0xffffffffffffffffffffffffffffffff)
  , .assign "sum"
      (.call "add"
        [ .call "and" [.ident "x", .ident "_1"]
        , .call "and" [.ident "y", .ident "_1"]
        ])
  , .if_ (.call "gt" [.ident "sum", .ident "_1"])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x11])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  ]

private def checkedAddUint128HelperStmt : YulStmt :=
  .funcDef "checked_add_uint128" ["x", "y"] ["sum"] checkedAddUint128HelperBody

private def checkedSubUint128HelperBody : List YulStmt :=
  [ .let_ "_1" (.hex 0xffffffffffffffffffffffffffffffff)
  , .assign "diff"
      (.call "sub"
        [ .call "and" [.ident "x", .ident "_1"]
        , .call "and" [.ident "y", .ident "_1"]
        ])
  , .if_ (.call "gt" [.ident "diff", .ident "_1"])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x11])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  ]

private def checkedSubUint128HelperStmt : YulStmt :=
  .funcDef "checked_sub_uint128" ["x", "y"] ["diff"] checkedSubUint128HelperBody

private def checkedMulUint256HelperBody : List YulStmt :=
  [ .assign "product" (.call "mul" [.ident "x", .ident "y"])
  , .if_ (.call "iszero"
      [ .call "or"
          [ .call "iszero" [.ident "x"]
          , .call "eq" [.ident "y", .call "div" [.ident "product", .ident "x"]]
          ]
      ])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x11])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  ]

private def checkedMulUint256HelperStmt : YulStmt :=
  .funcDef "checked_mul_uint256" ["x", "y"] ["product"] checkedMulUint256HelperBody

private def checkedDivUint256HelperBody : List YulStmt :=
  [ .if_ (.call "iszero" [.ident "y"])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x12])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  , .assign "r" (.call "div" [.ident "x", .ident "y"])
  ]

private def checkedDivUint256HelperStmt : YulStmt :=
  .funcDef "checked_div_uint256" ["x", "y"] ["r"] checkedDivUint256HelperBody

private def toSharesDownHelperBody : List YulStmt :=
  [ .let_ "sum" (.call "add" [.ident "var_totalShares", .hex 0x0f4240])
  , .if_ (.call "gt" [.ident "var_totalShares", .ident "sum"])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x11])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  , .let_ "sum_1" (.call "add" [.ident "var_totalAssets", .hex 0x01])
  , .if_ (.call "gt" [.ident "var_totalAssets", .ident "sum_1"])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x11])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  , .assign "var_"
      (.call "checked_div_uint256"
        [ .call "checked_mul_uint256" [.ident "var_assets", .ident "sum"]
        , .ident "sum_1"
        ])
  ]

private def toSharesDownHelperStmt : YulStmt :=
  .funcDef "fun_toSharesDown" ["var_assets", "var_totalAssets", "var_totalShares"] ["var_"] toSharesDownHelperBody

private def requireHelperStringBody : List YulStmt :=
  [ .if_ (.call "iszero" [.ident "condition"])
      [ .let_ "memPtr" (.call "mload" [.lit 64])
      , .expr
          (.call "mstore"
            [ .ident "memPtr"
            , .hex 0x08c379a000000000000000000000000000000000000000000000000000000000
            ])
      , .let_ "_1" (.lit 32)
      , .expr (.call "mstore" [.call "add" [.ident "memPtr", .lit 4], .ident "_1"])
      , .let_ "length" (.call "mload" [.ident "message"])
      , .expr (.call "mstore" [.call "add" [.ident "memPtr", .lit 36], .ident "length"])
      , .let_ "i" (.lit 0)
      , .for_ []
          (.call "lt" [.ident "i", .ident "length"])
          [ .assign "i" (.call "add" [.ident "i", .ident "_1"]) ]
          [ .expr
              (.call "mstore"
                [ .call "add"
                    [ .call "add" [.ident "memPtr", .ident "i"]
                    , .lit 68
                    ]
                , .call "mload"
                    [ .call "add"
                        [ .call "add" [.ident "message", .ident "i"]
                        , .ident "_1"
                        ]
                    ]
                ])
          ]
      , .expr
          (.call "mstore"
            [ .call "add"
                [ .call "add" [.ident "memPtr", .ident "length"]
                , .lit 68
                ]
            , .lit 0
            ])
      , .expr
          (.call "revert"
            [ .ident "memPtr"
            , .call "add"
                [ .call "sub"
                    [ .call "add"
                        [ .ident "memPtr"
                        , .call "and"
                            [ .call "add" [.ident "length", .lit 31]
                            , .hex 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0
                            ]
                        ]
                    , .ident "memPtr"
                    ]
                , .lit 68
                ]
            ])
      ]
  ]

private def requireHelperStringStmt : YulStmt :=
  .funcDef "require_helper_string" ["condition", "message"] [] requireHelperStringBody

private def finalizeAllocation35876HelperBody : List YulStmt :=
  [ .let_ "newFreePtr" (.call "add" [.ident "memPtr", .lit 64])
  , .if_ (.call "or"
      [ .call "gt" [.ident "newFreePtr", .hex 0xffffffffffffffff]
      , .call "lt" [.ident "newFreePtr", .ident "memPtr"]
      ])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x41])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  , .expr (.call "mstore" [.lit 64, .ident "newFreePtr"])
  ]

private def finalizeAllocation35876HelperStmt : YulStmt :=
  .funcDef "finalize_allocation_35876" ["memPtr"] [] finalizeAllocation35876HelperBody

private def finalizeAllocation27020HelperBody : List YulStmt :=
  [ .if_ (.call "gt" [.ident "memPtr", .hex 0xffffffffffffffff])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x41])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  , .expr (.call "mstore" [.lit 64, .ident "memPtr"])
  ]

private def finalizeAllocation27020HelperStmt : YulStmt :=
  .funcDef "finalize_allocation_27020" ["memPtr"] [] finalizeAllocation27020HelperBody

private def finalizeAllocation27033HelperBody : List YulStmt :=
  [ .let_ "newFreePtr" (.call "add" [.ident "memPtr", .hex 0xa0])
  , .if_ (.call "or"
      [ .call "gt" [.ident "newFreePtr", .hex 0xffffffffffffffff]
      , .call "lt" [.ident "newFreePtr", .ident "memPtr"]
      ])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x41])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  , .expr (.call "mstore" [.lit 64, .ident "newFreePtr"])
  ]

private def finalizeAllocation27033HelperStmt : YulStmt :=
  .funcDef "finalize_allocation_27033" ["memPtr"] [] finalizeAllocation27033HelperBody

private def finalizeAllocationHelperBody : List YulStmt :=
  [ .let_ "newFreePtr"
      (.call "add"
        [ .ident "memPtr"
        , .call "and"
            [ .call "add" [.ident "size", .lit 31]
            , .hex 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0
            ]
        ])
  , .if_ (.call "or"
      [ .call "gt" [.ident "newFreePtr", .hex 0xffffffffffffffff]
      , .call "lt" [.ident "newFreePtr", .ident "memPtr"]
      ])
      [ .expr (.call "mstore"
          [ .lit 0
          , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
          ])
      , .expr (.call "mstore" [.lit 4, .hex 0x41])
      , .expr (.call "revert" [.lit 0, .hex 0x24])
      ]
  , .expr (.call "mstore" [.lit 64, .ident "newFreePtr"])
  ]

private def finalizeAllocationHelperStmt : YulStmt :=
  .funcDef "finalize_allocation" ["memPtr", "size"] [] finalizeAllocationHelperBody

private def extractReturndataHelperBody : List YulStmt :=
  [ .switch (.call "returndatasize" [])
      [ (0, [ .assign "data" (.lit 96) ]) ]
      (some
        [ .let_ "_1" (.call "returndatasize" [])
        , .if_ (.call "gt" [.ident "_1", .hex 0xffffffffffffffff])
            [ .expr (.call "mstore"
                [ .lit 0
                , .lit 35408467139433450592217433187231851964531694900788300625387963629091585785856
                ])
            , .expr (.call "mstore" [.lit 4, .hex 0x41])
            , .expr (.call "revert" [.lit 0, .hex 0x24])
            ]
        , .let_ "memPtr" (.call "mload" [.lit 64])
        , .expr
            (.call "finalize_allocation"
              [ .ident "memPtr"
              , .call "add"
                  [ .call "and"
                      [ .call "add" [.ident "_1", .lit 31]
                      , .hex 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0
                      ]
                  , .hex 0x20
                  ]
              ])
        , .expr (.call "mstore" [.ident "memPtr", .ident "_1"])
        , .assign "data" (.ident "memPtr")
        , .expr
            (.call "returndatacopy"
              [ .call "add" [.ident "memPtr", .hex 0x20]
              , .lit 0
              , .call "returndatasize" []
              ])
        ])
  ]

private def extractReturndataHelperStmt : YulStmt :=
  .funcDef "extract_returndata" [] ["data"] extractReturndataHelperBody

private def toUint128HelperBody : List YulStmt :=
  [ .let_ "_1" (.hex 0xffffffffffffffffffffffffffffffff)
  , .let_ "memPtr" (.call "mload" [.lit 64])
  , .expr (.call "finalize_allocation_35876" [.ident "memPtr"])
  , .expr (.call "mstore" [.ident "memPtr", .lit 20])
  , .expr
      (.call "mstore"
        [ .call "add" [.ident "memPtr", .lit 32]
        , .str "max uint128 exceeded"
        ])
  , .expr
      (.call "require_helper_string"
        [ .call "iszero" [.call "gt" [.ident "var_x", .ident "_1"]]
        , .ident "memPtr"
        ])
  , .assign "var" (.call "and" [.ident "var_x", .ident "_1"])
  ]

private def toUint128HelperStmt : YulStmt :=
  .funcDef "fun_toUint128" ["var_x"] ["var"] toUint128HelperBody

private def updateStorageValueOffsetUint128HelperBody : List YulStmt :=
  [ .let_ "_1" (.call "sload" [.ident "slot"])
  , .expr
      (.call "sstore"
        [ .ident "slot"
        , .call "or"
            [ .call "and" [.ident "_1", .hex 0xffffffffffffffffffffffffffffffff]
            , .call "and"
                [ .call "shl" [.lit 128, .ident "value"]
                , .hex 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
                ]
            ]
        ])
  ]

private def updateStorageValueOffsetUint128HelperStmt : YulStmt :=
  .funcDef "update_storage_value_offsett_uint128_to_uint128" ["slot", "value"] [] updateStorageValueOffsetUint128HelperBody

private def updateStorageValueOffsetBoolHelperBody : List YulStmt :=
  [ .let_ "value_1"
      (.call "and"
        [ .call "sload" [.ident "slot"]
        , .hex 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00
        ])
  , .expr
      (.call "sstore"
        [ .ident "slot"
        , .call "or"
            [ .ident "value_1"
            , .call "and"
                [ .call "iszero" [.call "iszero" [.ident "value"]]
                , .lit 255
                ]
            ]
        ])
  ]

private def updateStorageValueOffsetBoolHelperStmt : YulStmt :=
  .funcDef "update_storage_value_offsett_bool_to_bool" ["slot", "value"] [] updateStorageValueOffsetBoolHelperBody

private def materializeCheckedAddMulDivUint256HelpersIfCalled (stmts : List YulStmt) : List YulStmt × Nat :=
  let (wrapped, topStmts) :=
    match stmts with
    | [.block inner] => (true, inner)
    | _ => (false, stmts)
  let needsAdd :=
    !hasTopLevelFunctionNamed topStmts "checked_add_uint256" &&
      (callNamesInStmts topStmts).any (fun called => called = "checked_add_uint256")
  let withAdd :=
    if needsAdd then
      insertTopLevelFuncDefAfterPrefix topStmts checkedAddUint256HelperStmt
    else
      topStmts
  let needsSub256 :=
    !hasTopLevelFunctionNamed withAdd "checked_sub_uint256" &&
      (callNamesInStmts withAdd).any (fun called => called = "checked_sub_uint256")
  let withAddSub256 :=
    if needsSub256 then
      insertTopLevelFuncDefAfterPrefix withAdd checkedSubUint256HelperStmt
    else
      withAdd
  let needsMul :=
    !hasTopLevelFunctionNamed withAddSub256 "checked_mul_uint256" &&
      (callNamesInStmts withAddSub256).any (fun called => called = "checked_mul_uint256")
  let withAddMul :=
    if needsMul then
      insertTopLevelFuncDefAfterPrefix withAddSub256 checkedMulUint256HelperStmt
    else
      withAddSub256
  let needsDiv :=
    !hasTopLevelFunctionNamed withAddMul "checked_div_uint256" &&
      (callNamesInStmts withAddMul).any (fun called => called = "checked_div_uint256")
  let withAddMulDiv :=
    if needsDiv then
      insertTopLevelFuncDefAfterPrefix withAddMul checkedDivUint256HelperStmt
    else
      withAddMul
  let needsAdd128 :=
    !hasTopLevelFunctionNamed withAddMulDiv "checked_add_uint128" &&
      (callNamesInStmts withAddMulDiv).any (fun called => called = "checked_add_uint128")
  let withAddMulDivAdd128 :=
    if needsAdd128 then
      insertTopLevelFuncDefAfterPrefix withAddMulDiv checkedAddUint128HelperStmt
    else
      withAddMulDiv
  let needsSub128 :=
    !hasTopLevelFunctionNamed withAddMulDivAdd128 "checked_sub_uint128" &&
      (callNamesInStmts withAddMulDivAdd128).any (fun called => called = "checked_sub_uint128")
  let withAddMulDivAdd128Sub128 :=
    if needsSub128 then
      insertTopLevelFuncDefAfterPrefix withAddMulDivAdd128 checkedSubUint128HelperStmt
    else
      withAddMulDivAdd128
  let needsToUint128 :=
    !hasTopLevelFunctionNamed withAddMulDivAdd128Sub128 "fun_toUint128" &&
      (callNamesInStmts withAddMulDivAdd128Sub128).any (fun called => called = "fun_toUint128")
  let withAddMulDivAdd128Sub128ToUint128 :=
    if needsToUint128 then
      insertTopLevelFuncDefAfterPrefix withAddMulDivAdd128Sub128 toUint128HelperStmt
    else
      withAddMulDivAdd128Sub128
  let needsRequireHelperString :=
    !hasTopLevelFunctionNamed withAddMulDivAdd128Sub128ToUint128 "require_helper_string" &&
      (callNamesInStmts withAddMulDivAdd128Sub128ToUint128).any (fun called => called = "require_helper_string")
  let withAddMulDivAdd128Sub128ToUint128RequireHelperString :=
    if needsRequireHelperString then
      insertTopLevelFuncDefAfterPrefix withAddMulDivAdd128Sub128ToUint128 requireHelperStringStmt
    else
      withAddMulDivAdd128Sub128ToUint128
  let needsFinalizeAllocation35876 :=
    !hasTopLevelFunctionNamed withAddMulDivAdd128Sub128ToUint128RequireHelperString "finalize_allocation_35876" &&
      (callNamesInStmts withAddMulDivAdd128Sub128ToUint128RequireHelperString).any
        (fun called => called = "finalize_allocation_35876")
  let withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876 :=
    if needsFinalizeAllocation35876 then
      insertTopLevelFuncDefAfterPrefix
        withAddMulDivAdd128Sub128ToUint128RequireHelperString
        finalizeAllocation35876HelperStmt
    else
      withAddMulDivAdd128Sub128ToUint128RequireHelperString
  let needsFinalizeAllocation :=
    !hasTopLevelFunctionNamed withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876
        "finalize_allocation" &&
      (callNamesInStmts withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876).any
        (fun called => called = "finalize_allocation")
  let withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation :=
    if needsFinalizeAllocation then
      insertTopLevelFuncDefAfterPrefix
        withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876
        finalizeAllocationHelperStmt
    else
      withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876
  let needsFinalizeAllocation27020 :=
    !hasTopLevelFunctionNamed
        withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation
        "finalize_allocation_27020" &&
      (callNamesInStmts
          withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation).any
        (fun called => called = "finalize_allocation_27020")
  let withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation27020 :=
    if needsFinalizeAllocation27020 then
      insertTopLevelFuncDefAfterPrefix
        withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation
        finalizeAllocation27020HelperStmt
    else
      withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation
  let needsFinalizeAllocation27033 :=
    !hasTopLevelFunctionNamed
        withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation27020
        "finalize_allocation_27033" &&
      (callNamesInStmts
          withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation27020).any
        (fun called => called = "finalize_allocation_27033")
  let withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation27020FinalizeAllocation27033 :=
    if needsFinalizeAllocation27033 then
      insertTopLevelFuncDefAfterPrefix
        withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation27020
        finalizeAllocation27033HelperStmt
    else
      withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation27020
  let needsToSharesDown :=
    !hasTopLevelFunctionNamed
        withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation27020FinalizeAllocation27033
        "fun_toSharesDown" &&
      (callNamesInStmts
          withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation27020FinalizeAllocation27033).any
        (fun called => called = "fun_toSharesDown")
  let withAll :=
    if needsToSharesDown then
      insertTopLevelFuncDefAfterPrefix
        withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation27020FinalizeAllocation27033
        toSharesDownHelperStmt
    else
      withAddMulDivAdd128Sub128ToUint128RequireHelperStringFinalizeAllocation35876FinalizeAllocation27020FinalizeAllocation27033
  let needsUpdateStorageUint128 :=
    !hasTopLevelFunctionNamed withAll "update_storage_value_offsett_uint128_to_uint128" &&
      (callNamesInStmts withAll).any (fun called => called = "update_storage_value_offsett_uint128_to_uint128")
  let withAll' :=
    if needsUpdateStorageUint128 then
      insertTopLevelFuncDefAfterPrefix withAll updateStorageValueOffsetUint128HelperStmt
    else
      withAll
  let needsUpdateStorageBool :=
    !hasTopLevelFunctionNamed withAll' "update_storage_value_offsett_bool_to_bool" &&
      (callNamesInStmts withAll').any (fun called => called = "fun_accrueInterest")
  let withAll'' :=
    if needsUpdateStorageBool then
      insertTopLevelFuncDefAfterPrefix withAll' updateStorageValueOffsetBoolHelperStmt
    else
      withAll'
  let needsExtractReturndata :=
    !hasTopLevelFunctionNamed withAll'' "extract_returndata" &&
      (callNamesInStmts withAll'').any (fun called => called = "extract_returndata")
  let withAll''' :=
    if needsExtractReturndata then
      insertTopLevelFuncDefAfterPrefix withAll'' extractReturndataHelperStmt
    else
      withAll''
  let inserted : Nat :=
    (if needsAdd then 1 else 0) + (if needsSub256 then 1 else 0) +
      (if needsMul then 1 else 0) + (if needsDiv then 1 else 0) +
      (if needsAdd128 then 1 else 0) + (if needsSub128 then 1 else 0) +
      (if needsToUint128 then 1 else 0) + (if needsRequireHelperString then 1 else 0) +
      (if needsFinalizeAllocation35876 then 1 else 0) +
      (if needsFinalizeAllocation then 1 else 0) +
      (if needsFinalizeAllocation27020 then 1 else 0) +
      (if needsFinalizeAllocation27033 then 1 else 0) +
      (if needsToSharesDown then 1 else 0) + (if needsUpdateStorageUint128 then 1 else 0) +
      (if needsUpdateStorageBool then 1 else 0) + (if needsExtractReturndata then 1 else 0)
  if inserted = 0 then
    (stmts, 0)
  else if wrapped then
    ([.block withAll'''], inserted)
  else
    (withAll''', inserted)

private def hasAccrueInterestCompatBaseName (base name : String) : Bool :=
  name = base || name.startsWith s!"{base}_"

private def isAccrueInterestSixArgCompatCall
    (idName loanTokenName collateralTokenName oracleName irmName lltvName : String) : Bool :=
  let rec allDistinct (seen : List String) : List String → Bool
    | [] => true
    | name :: rest =>
        if seen.any (fun prior => prior = name) then false else allDistinct (name :: seen) rest
  hasAccrueInterestCompatBaseName "id" idName &&
    hasAccrueInterestCompatBaseName "loanToken" loanTokenName &&
    hasAccrueInterestCompatBaseName "collateralToken" collateralTokenName &&
    hasAccrueInterestCompatBaseName "oracle" oracleName &&
    hasAccrueInterestCompatBaseName "irm" irmName &&
    hasAccrueInterestCompatBaseName "lltv" lltvName &&
    allDistinct [] [idName, loanTokenName, collateralTokenName, oracleName, irmName, lltvName]

private def namesAreDistinct (names : List String) : Bool :=
  let rec go (seen : List String) : List String → Bool
    | [] => true
    | name :: rest =>
        if seen.any (fun prior => prior = name) then
          false
        else
          go (name :: seen) rest
  go [] names

def isAccrueInterestTimestampWriteBlock
    (idName : String) (stmts : List YulStmt) : Bool :=
  match stmts with
  | [ .let_ compatValueName (.call "timestamp" [])
    , .let_ compatPackedName
        (.call "and"
          [ .ident compatValueRef
          , .lit 340282366920938463463374607431768211455
          ])
    , .expr (.call "mstore" [.lit 512, .ident idHead])
    , .expr (.call "mstore" [.lit 544, .lit 3])
    , .let_ compatMappingSlot1
        (.call "keccak256" [.lit 512, .lit 64])
    , .let_ compatSlotWordName
        (.call "sload"
          [ .call "add" [.ident compatMappingSlot1Ref, .lit 2]
          ])
    , .let_ compatSlotClearedName
        (.call "and"
          [ .ident compatSlotWordRef
          , .call "not" [.lit 340282366920938463463374607431768211455]
          ])
    , .expr (.call "mstore" [.lit 512, .ident idTail])
    , .expr (.call "mstore" [.lit 544, .lit 3])
    , .let_ compatMappingSlot2
        (.call "keccak256" [.lit 512, .lit 64])
    , .expr
        (.call "sstore"
          [ .call "add" [.ident compatMappingSlot2Ref, .lit 2]
          , .call "or"
              [ .ident compatSlotClearedRef
              , .call "shl" [.lit 0, .ident compatPackedRef]
              ]
          ])
    ] =>
      decide (compatValueName = compatValueRef) &&
        decide (compatPackedName = compatPackedRef) &&
        decide (compatMappingSlot1 = compatMappingSlot1Ref) &&
        decide (compatSlotWordName = compatSlotWordRef) &&
        decide (compatSlotClearedName = compatSlotClearedRef) &&
        decide (compatMappingSlot2 = compatMappingSlot2Ref) &&
        decide (idHead = idName) &&
        decide (idTail = idName)
  | _ => false

private def isAccrueInterestIrmNonZeroGuardCond
    (irmName : String) (cond : YulExpr) : Bool :=
  match cond with
  | .call "iszero" [.call "eq" [.ident irmHead, .lit 0]] =>
      decide (irmHead = irmName)
  | .call "iszero" [.call "iszero" [.ident irmHead]] =>
      decide (irmHead = irmName)
  | .call "iszero"
      [ .call "eq"
          [ .call "and"
              [ .ident irmHead
              , .lit 1461501637330902918203684832716283019655932542975
              ]
          , .lit 0
          ]
      ] =>
      decide (irmHead = irmName)
  | .call "iszero"
      [ .call "iszero"
          [ .call "and"
              [ .ident irmHead
              , .lit 1461501637330902918203684832716283019655932542975
              ]
          ]
      ] =>
      decide (irmHead = irmName)
  | _ => false

private def moveAccrueInterestTimestampWriteAfterIrmGuard
    (idName irmName : String) (body : List YulStmt) : List YulStmt × Nat :=
  match body with
  | (.expr (.call "mstore" [.lit 512, .ident idHead])) ::
    (.expr (.call "mstore" [.lit 544, .lit 3])) ::
    (.let_ compatMappingSlot0 (.call "keccak256" [.lit 512, .lit 64])) ::
    (.let_ prevLastUpdateName
      (.call "and"
        [ .call "shr"
            [ .lit 0
            , .call "sload"
                [ .call "add" [.ident compatMappingSlot0Ref, .lit 2]
                ]
            ]
        , .lit 340282366920938463463374607431768211455
        ])) ::
    (.let_ compatElapsedName
      (.call "checked_sub_uint256"
        [ .call "timestamp" []
        , .ident prevLastUpdateRef
        ])) ::
    (.if_ (.call "iszero" [.ident compatElapsedRef]) [.leave]) ::
    (.block timestampWriteBlock) ::
    (irmGuard@(.if_ irmCond _)) ::
    rest =>
      if decide (idHead = idName) &&
          decide (compatMappingSlot0 = compatMappingSlot0Ref) &&
          decide (prevLastUpdateName = prevLastUpdateRef) &&
          decide (compatElapsedName = compatElapsedRef) &&
          isAccrueInterestIrmNonZeroGuardCond irmName irmCond &&
          isAccrueInterestTimestampWriteBlock idName timestampWriteBlock then
        ( [ .expr (.call "mstore" [.lit 512, .ident idHead])
          , .expr (.call "mstore" [.lit 544, .lit 3])
          , .let_ compatMappingSlot0 (.call "keccak256" [.lit 512, .lit 64])
          , .let_ prevLastUpdateName
              (.call "and"
                [ .call "shr"
                    [ .lit 0
                    , .call "sload"
                        [ .call "add" [.ident compatMappingSlot0, .lit 2]
                        ]
                    ]
                , .lit 340282366920938463463374607431768211455
                ])
          , .let_ compatElapsedName
              (.call "checked_sub_uint256"
                [ .call "timestamp" []
                , .ident prevLastUpdateName
                ])
          , .if_ (.call "iszero" [.ident compatElapsedName]) [.leave]
          , irmGuard
          , .block timestampWriteBlock
          ] ++ rest
        , 1)
      else
        (body, 0)
  | _ => (body, 0)

mutual

private partial def definesNameInStmt (target : String) (stmt : YulStmt) : Bool :=
  match stmt with
  | .let_ name _ => decide (name = target)
  | .letMany names _ => names.any (fun name => decide (name = target))
  | .assign name _ => decide (name = target)
  | .if_ _ body => definesNameInStmts target body
  | .for_ init _ post body =>
      definesNameInStmts target init ||
        definesNameInStmts target post ||
        definesNameInStmts target body
  | .switch _ cases default =>
      let inCases := cases.any (fun (_, body) => definesNameInStmts target body)
      let inDefault :=
        match default with
        | some body => definesNameInStmts target body
        | none => false
      inCases || inDefault
  | .funcDef name params rets body =>
      decide (name = target) ||
        params.any (fun param => decide (param = target)) ||
        rets.any (fun ret => decide (ret = target)) ||
        definesNameInStmts target body
  | .block body => definesNameInStmts target body
  | _ => false

private partial def definesNameInStmts (target : String) (stmts : List YulStmt) : Bool :=
  match stmts with
  | [] => false
  | stmt :: rest => definesNameInStmt target stmt || definesNameInStmts target rest

end

private def hasAnyNestedDefinitionFor (names : List String) (body : List YulStmt) : Bool :=
  names.any (fun name => definesNameInStmts name body)

private def rewriteAccrueInterestPrologueTemps
    (idName : String) (body : List YulStmt) : List YulStmt × Nat :=
  match body with
  | (.expr (.call "mstore" [.lit 512, .ident idHead])) ::
    (.expr (.call "mstore" [.lit 544, .lit 3])) ::
    (.let_ compatMappingSlot0 (.call "keccak256" [.lit 512, .lit 64])) ::
    (.let_ prevLastUpdateName
      (.call "and"
        [ .call "shr"
            [ .lit 0
            , .call "sload"
                [ .call "add" [.ident compatMappingSlot0Ref, .lit 2]
                ]
            ]
        , .lit 340282366920938463463374607431768211455
        ])) ::
    (.let_ compatElapsedName
      (.call "checked_sub_uint256"
        [ .call "timestamp" []
        , .ident prevLastUpdateRef
        ])) ::
    (.if_ (.call "iszero" [.ident compatElapsedRef]) [.leave]) ::
    rest =>
      if decide (idHead = idName) &&
          decide (compatMappingSlot0 = compatMappingSlot0Ref) &&
          decide (prevLastUpdateName = prevLastUpdateRef) &&
          decide (compatElapsedName = compatElapsedRef) &&
          !definesNameInStmts "_1" body &&
          !definesNameInStmts "_2" body &&
          !definesNameInStmts "_3" body &&
          !definesNameInStmts "_4" body &&
          !definesNameInStmts "_5" body then
        ( [ .let_ "_1" (.lit 0)
          , .expr (.call "mstore" [.ident "_1", .ident idHead])
          , .let_ "_2" (.lit 3)
          , .let_ "_3" (.lit 32)
          , .expr (.call "mstore" [.ident "_3", .ident "_2"])
          , .let_ "_4" (.lit 340282366920938463463374607431768211455)
          , .let_ "_5" (.lit 64)
          , .let_ prevLastUpdateName
              (.call "and"
                [ .call "sload"
                    [ .call "add"
                        [ .call "keccak256" [.ident "_1", .ident "_5"]
                        , .lit 2
                        ]
                    ]
                , .ident "_4"
                ])
          , .let_ compatElapsedName
              (.call "checked_sub_uint256"
                [ .call "timestamp" []
                , .ident prevLastUpdateName
                ])
          , .if_ (.call "iszero" [.ident compatElapsedName]) [.leave]
          ] ++ rest
        , 1)
      else
        (body, 0)
  | _ => (body, 0)

private def accrueInterestMarketParamsLoadExprFor?
    (loanTokenName collateralTokenName oracleName irmName lltvName name : String)
    : Option YulExpr :=
  if name = loanTokenName then
      some (.call "mload" [.ident "var_marketParams_46531_mpos"])
  else if name = collateralTokenName then
      some (.call "mload"
        [ .call "add" [.ident "var_marketParams_46531_mpos", .lit 32]
        ])
  else if name = oracleName then
      some (.call "mload"
        [ .call "add" [.ident "var_marketParams_46531_mpos", .lit 64]
        ])
  else if name = irmName then
      some (.call "mload"
        [ .call "add" [.ident "var_marketParams_46531_mpos", .lit 96]
        ])
  else if name = lltvName then
      some (.call "mload"
        [ .call "add" [.ident "var_marketParams_46531_mpos", .lit 128]
        ])
  else
      none

mutual

private partial def rewriteAccrueInterestMarketParamsExpr
    (idName loanTokenName collateralTokenName oracleName irmName lltvName : String)
    (expr : YulExpr) : YulExpr
  := match expr with
    | .ident name =>
        if name = idName then
          .ident "var_id"
        else
          match accrueInterestMarketParamsLoadExprFor?
              loanTokenName collateralTokenName oracleName irmName lltvName name with
          | some lowered => lowered
          | none => .ident name
    | .lit value => .lit value
    | .hex value => .hex value
    | .str value => .str value
    | .call name args =>
        .call name
          (rewriteAccrueInterestMarketParamsExprs
            idName loanTokenName collateralTokenName oracleName irmName lltvName args)

private partial def rewriteAccrueInterestMarketParamsExprs
    (idName loanTokenName collateralTokenName oracleName irmName lltvName : String)
    (exprs : List YulExpr) : List YulExpr
  := match exprs with
    | [] => []
    | expr :: rest =>
        rewriteAccrueInterestMarketParamsExpr
          idName loanTokenName collateralTokenName oracleName irmName lltvName expr ::
          rewriteAccrueInterestMarketParamsExprs
            idName loanTokenName collateralTokenName oracleName irmName lltvName rest

private partial def rewriteAccrueInterestMarketParamsStmt
    (idName loanTokenName collateralTokenName oracleName irmName lltvName : String)
    (stmt : YulStmt) : YulStmt
  := match stmt with
    | .comment text => .comment text
    | .let_ name value =>
        .let_ name
          (rewriteAccrueInterestMarketParamsExpr
            idName loanTokenName collateralTokenName oracleName irmName lltvName value)
    | .letMany names value =>
        .letMany names
          (rewriteAccrueInterestMarketParamsExpr
            idName loanTokenName collateralTokenName oracleName irmName lltvName value)
    | .assign name value =>
        .assign name
          (rewriteAccrueInterestMarketParamsExpr
            idName loanTokenName collateralTokenName oracleName irmName lltvName value)
    | .expr value =>
        .expr
          (rewriteAccrueInterestMarketParamsExpr
            idName loanTokenName collateralTokenName oracleName irmName lltvName value)
    | .leave => .leave
    | .if_ cond body =>
        .if_
          (rewriteAccrueInterestMarketParamsExpr
            idName loanTokenName collateralTokenName oracleName irmName lltvName cond)
          (rewriteAccrueInterestMarketParamsStmts
            idName loanTokenName collateralTokenName oracleName irmName lltvName body)
    | .for_ init cond post body =>
        .for_
          (rewriteAccrueInterestMarketParamsStmts
            idName loanTokenName collateralTokenName oracleName irmName lltvName init)
          (rewriteAccrueInterestMarketParamsExpr
            idName loanTokenName collateralTokenName oracleName irmName lltvName cond)
          (rewriteAccrueInterestMarketParamsStmts
            idName loanTokenName collateralTokenName oracleName irmName lltvName post)
          (rewriteAccrueInterestMarketParamsStmts
            idName loanTokenName collateralTokenName oracleName irmName lltvName body)
    | .switch expr cases default =>
        let cases' := cases.map (fun (entry : Nat × List YulStmt) =>
          let (tag, caseBody) := entry
          (tag, rewriteAccrueInterestMarketParamsStmts
            idName loanTokenName collateralTokenName oracleName irmName lltvName caseBody))
        let default' := default.map
          (rewriteAccrueInterestMarketParamsStmts
            idName loanTokenName collateralTokenName oracleName irmName lltvName)
        .switch
          (rewriteAccrueInterestMarketParamsExpr
            idName loanTokenName collateralTokenName oracleName irmName lltvName expr)
          cases'
          default'
    | .block stmts =>
        .block
          (rewriteAccrueInterestMarketParamsStmts
            idName loanTokenName collateralTokenName oracleName irmName lltvName stmts)
    | .funcDef name params rets body =>
        .funcDef name params rets
          (rewriteAccrueInterestMarketParamsStmts
            idName loanTokenName collateralTokenName oracleName irmName lltvName body)

private partial def rewriteAccrueInterestMarketParamsStmts
    (idName loanTokenName collateralTokenName oracleName irmName lltvName : String)
    (stmts : List YulStmt) : List YulStmt
  := match stmts with
    | [] => []
    | stmt :: rest =>
        rewriteAccrueInterestMarketParamsStmt
          idName loanTokenName collateralTokenName oracleName irmName lltvName stmt ::
          rewriteAccrueInterestMarketParamsStmts
            idName loanTokenName collateralTokenName oracleName irmName lltvName rest

end

mutual

private partial def rewriteCurrentNonceIncrementExpr
    (expr : YulExpr) : YulExpr × Nat
  := match expr with
    | .lit value => (.lit value, 0)
    | .hex value => (.hex value, 0)
    | .str value => (.str value, 0)
    | .ident name => (.ident name, 0)
    | .call "add" [.ident "currentNonce", .lit 1] =>
        (.call "increment_uint256" [.ident "currentNonce"], 1)
    | .call name args =>
        let (args', rewritten) := rewriteCurrentNonceIncrementExprs args
        (.call name args', rewritten)

private partial def rewriteCurrentNonceIncrementExprs
    (exprs : List YulExpr) : List YulExpr × Nat
  := match exprs with
    | [] => ([], 0)
    | expr :: rest =>
        let (expr', rewrittenHead) := rewriteCurrentNonceIncrementExpr expr
        let (rest', rewrittenTail) := rewriteCurrentNonceIncrementExprs rest
        (expr' :: rest', rewrittenHead + rewrittenTail)

private partial def rewriteCurrentNonceIncrementStmt
    (stmt : YulStmt) : YulStmt × Nat
  := match stmt with
    | .comment text => (.comment text, 0)
    | .let_ name value =>
        let (value', rewritten) := rewriteCurrentNonceIncrementExpr value
        (.let_ name value', rewritten)
    | .letMany names value =>
        let (value', rewritten) := rewriteCurrentNonceIncrementExpr value
        (.letMany names value', rewritten)
    | .assign name value =>
        let (value', rewritten) := rewriteCurrentNonceIncrementExpr value
        (.assign name value', rewritten)
    | .expr value =>
        let (value', rewritten) := rewriteCurrentNonceIncrementExpr value
        (.expr value', rewritten)
    | .leave => (.leave, 0)
    | .if_ cond body =>
        let (cond', condRewritten) := rewriteCurrentNonceIncrementExpr cond
        let (body', bodyRewritten) := rewriteCurrentNonceIncrementStmts body
        (.if_ cond' body', condRewritten + bodyRewritten)
    | .for_ init cond post body =>
        let (init', initRewritten) := rewriteCurrentNonceIncrementStmts init
        let (cond', condRewritten) := rewriteCurrentNonceIncrementExpr cond
        let (post', postRewritten) := rewriteCurrentNonceIncrementStmts post
        let (body', bodyRewritten) := rewriteCurrentNonceIncrementStmts body
        (.for_ init' cond' post' body', initRewritten + condRewritten + postRewritten + bodyRewritten)
    | .switch expr cases default =>
        let (expr', exprRewritten) := rewriteCurrentNonceIncrementExpr expr
        let rewriteCase := fun (entry : Nat × List YulStmt) =>
          let (tag, body) := entry
          let (body', rewritten) := rewriteCurrentNonceIncrementStmts body
          ((tag, body'), rewritten)
        let rewrittenCases := cases.map rewriteCase
        let cases' := rewrittenCases.map Prod.fst
        let caseRewritten := rewrittenCases.foldl (fun acc entry => acc + entry.snd) 0
        let (default', defaultRewritten) :=
          match default with
          | some body =>
              let (body', rewritten) := rewriteCurrentNonceIncrementStmts body
              (some body', rewritten)
          | none => (none, 0)
        (.switch expr' cases' default', exprRewritten + caseRewritten + defaultRewritten)
    | .block stmts =>
        let (stmts', rewritten) := rewriteCurrentNonceIncrementStmts stmts
        (.block stmts', rewritten)
    | .funcDef name params rets body =>
        let (body', rewritten) := rewriteCurrentNonceIncrementStmts body
        (.funcDef name params rets body', rewritten)

private partial def rewriteCurrentNonceIncrementStmts
    (stmts : List YulStmt) : List YulStmt × Nat
  := match stmts with
    | [] => ([], 0)
    | stmt :: rest =>
        let (stmt', rewrittenHead) := rewriteCurrentNonceIncrementStmt stmt
        let (rest', rewrittenTail) := rewriteCurrentNonceIncrementStmts rest
        (stmt' :: rest', rewrittenHead + rewrittenTail)

end

mutual

private partial def rewriteElapsedCheckedSubExpr
    (expr : YulExpr) : YulExpr × Nat
  := match expr with
    | .lit value => (.lit value, 0)
    | .hex value => (.hex value, 0)
    | .str value => (.str value, 0)
    | .ident name => (.ident name, 0)
    | .call "sub" [.call "timestamp" [], .ident "prevLastUpdate"] =>
        (.call "checked_sub_uint256" [.call "timestamp" [], .ident "prevLastUpdate"], 1)
    | .call name args =>
        let (args', rewritten) := rewriteElapsedCheckedSubExprs args
        (.call name args', rewritten)

private partial def rewriteElapsedCheckedSubExprs
    (exprs : List YulExpr) : List YulExpr × Nat
  := match exprs with
    | [] => ([], 0)
    | expr :: rest =>
        let (expr', rewrittenHead) := rewriteElapsedCheckedSubExpr expr
        let (rest', rewrittenTail) := rewriteElapsedCheckedSubExprs rest
        (expr' :: rest', rewrittenHead + rewrittenTail)

private partial def rewriteElapsedCheckedSubStmt
    (stmt : YulStmt) : YulStmt × Nat
  := match stmt with
    | .comment text => (.comment text, 0)
    | .let_ name value =>
        let (value', rewritten) := rewriteElapsedCheckedSubExpr value
        (.let_ name value', rewritten)
    | .letMany names value =>
        let (value', rewritten) := rewriteElapsedCheckedSubExpr value
        (.letMany names value', rewritten)
    | .assign name value =>
        let (value', rewritten) := rewriteElapsedCheckedSubExpr value
        (.assign name value', rewritten)
    | .expr value =>
        let (value', rewritten) := rewriteElapsedCheckedSubExpr value
        (.expr value', rewritten)
    | .leave => (.leave, 0)
    | .if_ cond body =>
        let (cond', condRewritten) := rewriteElapsedCheckedSubExpr cond
        let (body', bodyRewritten) := rewriteElapsedCheckedSubStmts body
        (.if_ cond' body', condRewritten + bodyRewritten)
    | .for_ init cond post body =>
        let (init', initRewritten) := rewriteElapsedCheckedSubStmts init
        let (cond', condRewritten) := rewriteElapsedCheckedSubExpr cond
        let (post', postRewritten) := rewriteElapsedCheckedSubStmts post
        let (body', bodyRewritten) := rewriteElapsedCheckedSubStmts body
        (.for_ init' cond' post' body', initRewritten + condRewritten + postRewritten + bodyRewritten)
    | .switch expr cases default =>
        let (expr', exprRewritten) := rewriteElapsedCheckedSubExpr expr
        let rewriteCase := fun (entry : Nat × List YulStmt) =>
          let (tag, body) := entry
          let (body', rewritten) := rewriteElapsedCheckedSubStmts body
          ((tag, body'), rewritten)
        let rewrittenCases := cases.map rewriteCase
        let cases' := rewrittenCases.map Prod.fst
        let caseRewritten := rewrittenCases.foldl (fun acc entry => acc + entry.snd) 0
        let (default', defaultRewritten) :=
          match default with
          | some body =>
              let (body', rewritten) := rewriteElapsedCheckedSubStmts body
              (some body', rewritten)
          | none => (none, 0)
        (.switch expr' cases' default', exprRewritten + caseRewritten + defaultRewritten)
    | .block stmts =>
        let (stmts', rewritten) := rewriteElapsedCheckedSubStmts stmts
        (.block stmts', rewritten)
    | .funcDef name params rets body =>
        let (body', rewritten) := rewriteElapsedCheckedSubStmts body
        (.funcDef name params rets body', rewritten)

private partial def rewriteElapsedCheckedSubStmts
    (stmts : List YulStmt) : List YulStmt × Nat
  := match stmts with
    | [] => ([], 0)
    | stmt :: rest =>
        let (stmt', rewrittenHead) := rewriteElapsedCheckedSubStmt stmt
        let (rest', rewrittenTail) := rewriteElapsedCheckedSubStmts rest
        (stmt' :: rest', rewrittenHead + rewrittenTail)

end

mutual

private partial def rewriteAccrueInterestCheckedArithmeticExpr
    (expr : YulExpr) : YulExpr × Nat
  := match expr with
    | .lit value => (.lit value, 0)
    | .hex value => (.hex value, 0)
    | .str value => (.str value, 0)
    | .ident name => (.ident name, 0)
    | .call "mul" [.ident "borrowRate", .ident "elapsed"] =>
        (.call "checked_mul_uint256" [.ident "borrowRate", .ident "elapsed"], 1)
    | .call "mul" [.ident "firstTerm", .ident "firstTerm"] =>
        (.call "checked_mul_uint256" [.ident "firstTerm", .ident "firstTerm"], 1)
    | .call "mul" [.ident "secondTerm", .ident "firstTerm"] =>
        (.call "checked_mul_uint256" [.ident "secondTerm", .ident "firstTerm"], 1)
    | .call "mul" [.ident "firstTerm", .ident "secondTerm"] =>
        (.call "checked_mul_uint256" [.ident "firstTerm", .ident "secondTerm"], 1)
    | .call "mul" [.ident "totalBorrowAssets", .ident "growth"] =>
        (.call "checked_mul_uint256" [.ident "totalBorrowAssets", .ident "growth"], 1)
    | .call "mul" [.ident "interest", .ident "fee"] =>
        (.call "checked_mul_uint256" [.ident "interest", .ident "fee"], 1)
    | .call "div" [.call "mul" [.ident "firstTerm", .ident "firstTerm"], .lit 2000000000000000000] =>
        (.call "checked_div_uint256"
          [ .call "checked_mul_uint256" [.ident "firstTerm", .ident "firstTerm"]
          , .lit 2000000000000000000
          ], 1)
    | .call "div" [.call "checked_mul_uint256" [.ident "firstTerm", .ident "firstTerm"], .lit 2000000000000000000] =>
        (.call "checked_div_uint256"
          [ .call "checked_mul_uint256" [.ident "firstTerm", .ident "firstTerm"]
          , .lit 2000000000000000000
          ], 1)
    | .call "div" [.call "mul" [.ident "secondTerm", .ident "firstTerm"], .lit 3000000000000000000] =>
        (.call "checked_div_uint256"
          [ .call "checked_mul_uint256" [.ident "secondTerm", .ident "firstTerm"]
          , .lit 3000000000000000000
          ], 1)
    | .call "div" [.call "checked_mul_uint256" [.ident "secondTerm", .ident "firstTerm"], .lit 3000000000000000000] =>
        (.call "checked_div_uint256"
          [ .call "checked_mul_uint256" [.ident "secondTerm", .ident "firstTerm"]
          , .lit 3000000000000000000
          ], 1)
    | .call "div" [.call "mul" [.ident "totalBorrowAssets", .ident "growth"], .lit 1000000000000000000] =>
        (.call "checked_div_uint256"
          [ .call "checked_mul_uint256" [.ident "totalBorrowAssets", .ident "growth"]
          , .lit 1000000000000000000
          ], 1)
    | .call "div" [.call "checked_mul_uint256" [.ident "totalBorrowAssets", .ident "growth"], .lit 1000000000000000000] =>
        (.call "checked_div_uint256"
          [ .call "checked_mul_uint256" [.ident "totalBorrowAssets", .ident "growth"]
          , .lit 1000000000000000000
          ], 1)
    | .call "div" [.call "mul" [.ident "interest", .ident "fee"], .lit 1000000000000000000] =>
        (.call "checked_div_uint256"
          [ .call "checked_mul_uint256" [.ident "interest", .ident "fee"]
          , .lit 1000000000000000000
          ], 1)
    | .call "div" [.call "checked_mul_uint256" [.ident "interest", .ident "fee"], .lit 1000000000000000000] =>
        (.call "checked_div_uint256"
          [ .call "checked_mul_uint256" [.ident "interest", .ident "fee"]
          , .lit 1000000000000000000
          ], 1)
    | .call "add" [.ident "secondTerm", .ident "thirdTerm"] =>
        (.call "checked_add_uint256" [.ident "secondTerm", .ident "thirdTerm"], 1)
    | .call "add" [.ident "firstTerm", .call "add" [.ident "secondTerm", .ident "thirdTerm"]] =>
        (.call "checked_add_uint256"
          [ .ident "firstTerm"
          , .call "checked_add_uint256" [.ident "secondTerm", .ident "thirdTerm"]
          ], 1)
    | .call "add" [.ident "totalBorrowAssets", .ident "interest"] =>
        (.call "checked_add_uint128"
          [ .ident "totalBorrowAssets"
          , .call "fun_toUint128" [.ident "interest"]
          ], 1)
    | .call "add" [.ident "totalSupplyAssets", .ident "interest"] =>
        (.call "checked_add_uint128"
          [ .ident "totalSupplyAssets"
          , .call "fun_toUint128" [.ident "interest"]
          ], 1)
    | .call "checked_add_uint128" [.ident lhs, .ident rhs] =>
        if lhs = "totalBorrowAssets" && rhs = "interest" then
          (.call "checked_add_uint128"
            [ .ident "totalBorrowAssets"
            , .call "fun_toUint128" [.ident "interest"]
            ], 1)
        else if lhs = "totalSupplyAssets" && rhs = "interest" then
          (.call "checked_add_uint128"
            [ .ident "totalSupplyAssets"
            , .call "fun_toUint128" [.ident "interest"]
            ], 1)
        else if hasAccrueInterestCompatBaseName "totalSupplyShares" lhs &&
            hasAccrueInterestCompatBaseName "feeShares" rhs then
          (.call "checked_add_uint128"
            [ .ident lhs
            , .call "fun_toUint128" [.ident rhs]
            ], 1)
        else if hasAccrueInterestCompatBaseName "feeShares" lhs &&
            hasAccrueInterestCompatBaseName "totalSupplyShares" rhs then
          (.call "checked_add_uint128"
            [ .ident rhs
            , .call "fun_toUint128" [.ident lhs]
            ], 1)
        else
          (.call "checked_add_uint128" [.ident lhs, .ident rhs], 0)
    | .call "add" [.ident lhs, .ident rhs] =>
        if lhs = "feePosShares" && rhs = "feeShares" then
          (.call "checked_add_uint256" [.ident "feePosShares", .ident "feeShares"], 1)
        else if hasAccrueInterestCompatBaseName "totalSupplyShares" lhs &&
            hasAccrueInterestCompatBaseName "feeShares" rhs then
          (.call "checked_add_uint128"
            [ .ident lhs
            , .call "fun_toUint128" [.ident rhs]
            ], 1)
        else if hasAccrueInterestCompatBaseName "feeShares" lhs &&
            hasAccrueInterestCompatBaseName "totalSupplyShares" rhs then
          (.call "checked_add_uint128"
            [ .ident rhs
            , .call "fun_toUint128" [.ident lhs]
            ], 1)
        else
          (.call "add" [.ident lhs, .ident rhs], 0)
    | .call "sub" [.ident lhs, .ident rhs] =>
        if hasAccrueInterestCompatBaseName "newTotalSupplyAssets" lhs &&
            hasAccrueInterestCompatBaseName "feeAmount" rhs then
          (.call "checked_sub_uint128" [.ident lhs, .ident rhs], 1)
        else
          (.call "sub" [.ident lhs, .ident rhs], 0)
    | .call "checked_sub_uint256" [.ident lhs, .ident rhs] =>
        if hasAccrueInterestCompatBaseName "newTotalSupplyAssets" lhs &&
            hasAccrueInterestCompatBaseName "feeAmount" rhs then
          (.call "checked_sub_uint128" [.ident lhs, .ident rhs], 1)
        else
          (.call "checked_sub_uint256" [.ident lhs, .ident rhs], 0)
    | .call "sstore"
        [ .ident slot
        , .call "or" [.ident slotCleared, .call "shl" [.lit 128, .ident packedValue]]
        ] =>
        if slot.startsWith "__compat_mapping_slot_" &&
            slotCleared.startsWith "__compat_slot_cleared" &&
            packedValue.startsWith "__compat_packed" then
          (.call "update_storage_value_offsett_uint128_to_uint128" [.ident slot, .ident packedValue], 1)
        else
          (.call "sstore"
            [ .ident slot
            , .call "or" [.ident slotCleared, .call "shl" [.lit 128, .ident packedValue]]
            ], 0)
    | .call "div"
        [ .call "mul" [.ident feeAmount, .call "add" [.ident totalSupplyShares, .lit 1000000]]
        , .call "add" [.ident feeDenominator, .lit 1]
        ] =>
        if hasAccrueInterestCompatBaseName "feeAmount" feeAmount &&
            hasAccrueInterestCompatBaseName "totalSupplyShares" totalSupplyShares &&
            hasAccrueInterestCompatBaseName "feeDenominator" feeDenominator then
          (.call "fun_toSharesDown"
            [ .ident feeAmount
            , .ident feeDenominator
            , .ident totalSupplyShares
            ], 1)
        else
          (.call "div"
            [ .call "mul" [.ident feeAmount, .call "add" [.ident totalSupplyShares, .lit 1000000]]
            , .call "add" [.ident feeDenominator, .lit 1]
            ], 0)
    | .call "fun_accrueInterest"
        [ .ident idName
        , .ident loanTokenName
        , .ident collateralTokenName
        , .ident oracleName
        , .ident irmName
        , .ident lltvName
        ] =>
        if isAccrueInterestSixArgCompatCall
            idName loanTokenName collateralTokenName oracleName irmName lltvName then
          (.call "fun_accrueInterest" [.lit 0, .ident idName], 1)
        else
          (.call "fun_accrueInterest"
            [ .ident idName
            , .ident loanTokenName
            , .ident collateralTokenName
            , .ident oracleName
            , .ident irmName
            , .ident lltvName
            ], 0)
    | .call name args =>
        let (args', rewritten) := rewriteAccrueInterestCheckedArithmeticExprs args
        (.call name args', rewritten)

private partial def rewriteAccrueInterestCheckedArithmeticExprs
    (exprs : List YulExpr) : List YulExpr × Nat
  := match exprs with
    | [] => ([], 0)
    | expr :: rest =>
        let (expr', rewrittenHead) := rewriteAccrueInterestCheckedArithmeticExpr expr
        let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticExprs rest
        (expr' :: rest', rewrittenHead + rewrittenTail)

private partial def rewriteAccrueInterestCheckedArithmeticStmt
    (stmt : YulStmt) : YulStmt × Nat
  := match stmt with
    | .comment text => (.comment text, 0)
    | .let_ name value =>
        let (value', rewritten) := rewriteAccrueInterestCheckedArithmeticExpr value
        (.let_ name value', rewritten)
    | .letMany names value =>
        let (value', rewritten) := rewriteAccrueInterestCheckedArithmeticExpr value
        (.letMany names value', rewritten)
    | .assign name value =>
        let (value', rewritten) := rewriteAccrueInterestCheckedArithmeticExpr value
        (.assign name value', rewritten)
    | .expr value =>
        let (value', rewritten) := rewriteAccrueInterestCheckedArithmeticExpr value
        (.expr value', rewritten)
    | .leave => (.leave, 0)
    | .if_ cond body =>
        let (cond', condRewritten) := rewriteAccrueInterestCheckedArithmeticExpr cond
        let (body', bodyRewritten) := rewriteAccrueInterestCheckedArithmeticStmts body
        (.if_ cond' body', condRewritten + bodyRewritten)
    | .for_ init cond post body =>
        let (init', initRewritten) := rewriteAccrueInterestCheckedArithmeticStmts init
        let (cond', condRewritten) := rewriteAccrueInterestCheckedArithmeticExpr cond
        let (post', postRewritten) := rewriteAccrueInterestCheckedArithmeticStmts post
        let (body', bodyRewritten) := rewriteAccrueInterestCheckedArithmeticStmts body
        (.for_ init' cond' post' body', initRewritten + condRewritten + postRewritten + bodyRewritten)
    | .switch expr cases default =>
        let (expr', exprRewritten) := rewriteAccrueInterestCheckedArithmeticExpr expr
        let rewriteCase := fun (entry : Nat × List YulStmt) =>
          let (tag, body) := entry
          let (body', rewritten) := rewriteAccrueInterestCheckedArithmeticStmts body
          ((tag, body'), rewritten)
        let rewrittenCases := cases.map rewriteCase
        let cases' := rewrittenCases.map Prod.fst
        let caseRewritten := rewrittenCases.foldl (fun acc entry => acc + entry.snd) 0
        let (default', defaultRewritten) :=
          match default with
          | some body =>
              let (body', rewritten) := rewriteAccrueInterestCheckedArithmeticStmts body
              (some body', rewritten)
          | none => (none, 0)
        (.switch expr' cases' default', exprRewritten + caseRewritten + defaultRewritten)
    | .block stmts =>
        let (stmts', rewritten) := rewriteAccrueInterestCheckedArithmeticStmts stmts
        (.block stmts', rewritten)
    | .funcDef "fun_accrueInterest"
        [idName, loanTokenName, collateralTokenName, oracleName, irmName, lltvName]
        rets
        body =>
        let (body', rewritten) := rewriteAccrueInterestCheckedArithmeticStmts body
        let (body'', reordered) :=
          moveAccrueInterestTimestampWriteAfterIrmGuard idName irmName body'
        if namesAreDistinct
              [idName, loanTokenName, collateralTokenName, oracleName, irmName, lltvName] &&
            !hasAnyNestedDefinitionFor
              [idName, loanTokenName, collateralTokenName, oracleName, irmName, lltvName] body'' then
          ( .funcDef "fun_accrueInterest"
              ["var_marketParams_46531_mpos", "var_id"]
              rets
              (rewriteAccrueInterestMarketParamsStmts
                idName loanTokenName collateralTokenName oracleName irmName lltvName body'')
          , rewritten + reordered + 1)
        else
          (.funcDef "fun_accrueInterest"
            [idName, loanTokenName, collateralTokenName, oracleName, irmName, lltvName]
            rets
            body'', rewritten + reordered)
    | .funcDef name params rets body =>
        let (body', rewritten) := rewriteAccrueInterestCheckedArithmeticStmts body
        (.funcDef name params rets body', rewritten)

private partial def rewriteAccrueInterestPrologueTempsStmts
    (stmts : List YulStmt) : List YulStmt × Nat
  := match stmts with
    | [] => ([], 0)
    | .if_ cond body :: rest =>
        let (body', bodyRewritten) := rewriteAccrueInterestPrologueTempsStmts body
        let (rest', rewrittenTail) := rewriteAccrueInterestPrologueTempsStmts rest
        (.if_ cond body' :: rest', bodyRewritten + rewrittenTail)
    | .for_ init cond post body :: rest =>
        let (init', initRewritten) := rewriteAccrueInterestPrologueTempsStmts init
        let (post', postRewritten) := rewriteAccrueInterestPrologueTempsStmts post
        let (body', bodyRewritten) := rewriteAccrueInterestPrologueTempsStmts body
        let (rest', rewrittenTail) := rewriteAccrueInterestPrologueTempsStmts rest
        (.for_ init' cond post' body' :: rest', initRewritten + postRewritten + bodyRewritten + rewrittenTail)
    | .switch expr cases default :: rest =>
        let (cases', casesRewritten) :=
          cases.foldr
            (fun (entry : Nat × List YulStmt) (acc : List (Nat × List YulStmt) × Nat) =>
              let (tag, body) := entry
              let (body', rewritten) := rewriteAccrueInterestPrologueTempsStmts body
              ((tag, body') :: acc.1, acc.2 + rewritten))
            ([], 0)
        let (default', defaultRewritten) :=
          match default with
          | some body =>
              let (body', rewritten) := rewriteAccrueInterestPrologueTempsStmts body
              (some body', rewritten)
          | none => (none, 0)
        let (rest', rewrittenTail) := rewriteAccrueInterestPrologueTempsStmts rest
        (.switch expr cases' default' :: rest', casesRewritten + defaultRewritten + rewrittenTail)
    | .block inner :: rest =>
        let (inner', innerRewritten) := rewriteAccrueInterestPrologueTempsStmts inner
        let (rest', rewrittenTail) := rewriteAccrueInterestPrologueTempsStmts rest
        (.block inner' :: rest', innerRewritten + rewrittenTail)
    | .funcDef "fun_accrueInterest" ["var_marketParams_46531_mpos", "var_id"] rets body :: rest =>
        let (body', rewrittenHead) := rewriteAccrueInterestPrologueTemps "var_id" body
        let (body'', rewrittenBody) := rewriteAccrueInterestPrologueTempsStmts body'
        let (rest', rewrittenTail) := rewriteAccrueInterestPrologueTempsStmts rest
        (.funcDef "fun_accrueInterest" ["var_marketParams_46531_mpos", "var_id"] rets body'' :: rest',
          rewrittenHead + rewrittenBody + rewrittenTail)
    | .funcDef name params rets body :: rest =>
        let (body', rewritten) := rewriteAccrueInterestPrologueTempsStmts body
        let (rest', rewrittenTail) := rewriteAccrueInterestPrologueTempsStmts rest
        (.funcDef name params rets body' :: rest', rewritten + rewrittenTail)
    | stmt :: rest =>
        let (rest', rewrittenTail) := rewriteAccrueInterestPrologueTempsStmts rest
        (stmt :: rest', rewrittenTail)

private partial def rewriteAccrueInterestIrmGuardStmts
    (stmts : List YulStmt) : List YulStmt × Nat
  := match stmts with
    | [] => ([], 0)
    | .if_ (.call "iszero"
        [ .call "eq"
            [ .call "mload"
                [ .call "add"
                    [ .ident marketParamsName
                    , .lit 96
                    ]
                ]
            , .lit 0
            ]
        ]) body :: rest =>
        if hasAccrueInterestCompatBaseName "var_marketParams" marketParamsName then
          let (body', bodyRewritten) := rewriteAccrueInterestIrmGuardStmts body
          let (rest', rewrittenTail) := rewriteAccrueInterestIrmGuardStmts rest
          ( [ .let_ "cleaned"
                (.call "and"
                  [ .call "mload"
                      [ .call "add"
                          [ .ident marketParamsName
                          , .lit 96
                          ]
                      ]
                  , .lit 1461501637330902918203684832716283019655932542975
                  ])
            , .if_ (.call "iszero" [.call "iszero" [.ident "cleaned"]]) body'
            ] ++ rest'
          , bodyRewritten + rewrittenTail + 1)
        else
          let (body', bodyRewritten) := rewriteAccrueInterestIrmGuardStmts body
          let (rest', rewrittenTail) := rewriteAccrueInterestIrmGuardStmts rest
          (.if_ (.call "iszero"
              [ .call "eq"
                  [ .call "mload"
                      [ .call "add"
                          [ .ident marketParamsName
                          , .lit 96
                          ]
                      ]
                  , .lit 0
                  ]
              ]) body' :: rest',
            bodyRewritten + rewrittenTail)
    | .if_ cond body :: rest =>
        let (body', bodyRewritten) := rewriteAccrueInterestIrmGuardStmts body
        let (rest', rewrittenTail) := rewriteAccrueInterestIrmGuardStmts rest
        (.if_ cond body' :: rest', bodyRewritten + rewrittenTail)
    | .for_ init cond post body :: rest =>
        let (init', initRewritten) := rewriteAccrueInterestIrmGuardStmts init
        let (post', postRewritten) := rewriteAccrueInterestIrmGuardStmts post
        let (body', bodyRewritten) := rewriteAccrueInterestIrmGuardStmts body
        let (rest', rewrittenTail) := rewriteAccrueInterestIrmGuardStmts rest
        (.for_ init' cond post' body' :: rest', initRewritten + postRewritten + bodyRewritten + rewrittenTail)
    | .switch expr cases default :: rest =>
        let (cases', casesRewritten) :=
          cases.foldr
            (fun (entry : Nat × List YulStmt) (acc : List (Nat × List YulStmt) × Nat) =>
              let (tag, body) := entry
              let (body', rewritten) := rewriteAccrueInterestIrmGuardStmts body
              ((tag, body') :: acc.1, acc.2 + rewritten))
            ([], 0)
        let (default', defaultRewritten) :=
          match default with
          | some body =>
              let (body', rewritten) := rewriteAccrueInterestIrmGuardStmts body
              (some body', rewritten)
          | none => (none, 0)
        let (rest', rewrittenTail) := rewriteAccrueInterestIrmGuardStmts rest
        (.switch expr cases' default' :: rest', casesRewritten + defaultRewritten + rewrittenTail)
    | .block inner :: rest =>
        let (inner', innerRewritten) := rewriteAccrueInterestIrmGuardStmts inner
        let (rest', rewrittenTail) := rewriteAccrueInterestIrmGuardStmts rest
        (.block inner' :: rest', innerRewritten + rewrittenTail)
    | .funcDef name params rets body :: rest =>
        let (body', rewritten) := rewriteAccrueInterestIrmGuardStmts body
        let (rest', rewrittenTail) := rewriteAccrueInterestIrmGuardStmts rest
        (.funcDef name params rets body' :: rest', rewritten + rewrittenTail)
    | stmt :: rest =>
        let (rest', rewrittenTail) := rewriteAccrueInterestIrmGuardStmts rest
        (stmt :: rest', rewrittenTail)

private partial def rewriteAccrueInterestCheckedArithmeticStmts
    (stmts : List YulStmt) : List YulStmt × Nat
  := match stmts with
    | [] => ([], 0)
    | .let_ "__ecwr_success"
        (.call "call"
          [ .call "gas" []
          , .ident "irm"
          , .lit 0
          , .lit 0
          , .lit 356
          , .lit 0
          , .lit 32
          ]) ::
      (.if_ (.call "iszero" [.ident "__ecwr_success"])
        [ .let_ "__ecwr_rds" (.call "returndatasize" [])
        , .expr (.call "returndatacopy" [.lit 0, .lit 0, .ident "__ecwr_rds"])
        , .expr (.call "revert" [.lit 0, .ident "__ecwr_rds"])
        ]) ::
      (.if_ (.call "lt" [.call "returndatasize" [], .lit 32])
        [ .expr (.call "revert" [.lit 0, .lit 0]) ]) ::
      (.let_ "borrowRate" (.call "mload" [.lit 0])) :: rest =>
        let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
        ( [ .let_ "__compat_alloc_ptr" (.call "mload" [.lit 64])
          , .expr (.call "finalize_allocation_27020" [.ident "__compat_alloc_ptr"])
          , .expr (.call "finalize_allocation_27033" [.ident "__compat_alloc_ptr"])
          , .expr (.call "finalize_allocation" [.ident "__compat_alloc_ptr", .lit 32])
          , .let_ "__ecwr_success"
              (.call "call"
                [ .call "gas" []
                , .ident "irm"
                , .lit 0
                , .lit 0
                , .lit 356
                , .ident "__compat_alloc_ptr"
                , .lit 32
                ])
          , .if_ (.call "iszero" [.ident "__ecwr_success"])
              [ .let_ "__compat_returndata" (.call "extract_returndata" [])
              , .expr
                  (.call "revert"
                    [ .call "add" [.ident "__compat_returndata", .lit 32]
                    , .call "mload" [.ident "__compat_returndata"]
                    ])
              ]
          , .let_ "borrowRate" (.lit 0)
          , .if_ (.ident "__ecwr_success")
              [ .let_ "__compat_returndata_size" (.lit 32)
              , .if_ (.call "gt" [.lit 32, .call "returndatasize" []])
                  [ .assign "__compat_returndata_size" (.call "returndatasize" []) ]
              , .expr
                  (.call "finalize_allocation"
                    [ .ident "__compat_alloc_ptr"
                    , .ident "__compat_returndata_size"
                    ])
              , .if_
                  (.call "slt"
                    [ .call "sub"
                        [ .call "add"
                            [ .ident "__compat_alloc_ptr"
                            , .ident "__compat_returndata_size"
                            ]
                        , .ident "__compat_alloc_ptr"
                        ]
                    , .lit 32
                    ])
                  [ .expr (.call "revert" [.lit 0, .lit 0]) ]
              , .assign "borrowRate" (.call "mload" [.ident "__compat_alloc_ptr"])
              ]
          ] ++ rest'
        , rewrittenTail + 1)
    | .if_ (.call "gt" [.call "timestamp" [], .ident prevLastUpdate]) body :: rest =>
        if hasAccrueInterestCompatBaseName "prevLastUpdate" prevLastUpdate then
          let (body', bodyRewritten) := rewriteAccrueInterestCheckedArithmeticStmts body
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          ( [ .let_ "__compat_elapsed"
                (.call "checked_sub_uint256" [.call "timestamp" [], .ident prevLastUpdate])
            , .if_ (.call "iszero" [.ident "__compat_elapsed"]) [.leave]
            ] ++ body' ++ rest'
          , bodyRewritten + rewrittenTail + 1)
        else
          let (body', bodyRewritten) := rewriteAccrueInterestCheckedArithmeticStmts body
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          (.if_ (.call "gt" [.call "timestamp" [], .ident prevLastUpdate]) body' :: rest',
            bodyRewritten + rewrittenTail)
    | .let_ "__ecwr_success"
        (.call "call"
          [ .call "gas" []
          , .ident "irm"
          , .lit 0
          , .lit 0
          , .lit 356
          , .lit 0
          , .lit 32
          ]) :: rest =>
        let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
        ( [ .let_ "__compat_alloc_ptr" (.call "mload" [.lit 64])
          , .expr (.call "finalize_allocation_27020" [.ident "__compat_alloc_ptr"])
          , .expr (.call "finalize_allocation_27033" [.ident "__compat_alloc_ptr"])
          , .expr (.call "finalize_allocation" [.ident "__compat_alloc_ptr", .lit 32])
          , .let_ "__ecwr_success"
              (.call "call"
                [ .call "gas" []
                , .ident "irm"
                , .lit 0
                , .lit 0
                , .lit 356
                , .ident "__compat_alloc_ptr"
                , .lit 32
                ])
          , .expr (.call "mstore" [.lit 0, .call "mload" [.ident "__compat_alloc_ptr"]])
          ] ++ rest'
        , rewrittenTail + 1)
    | .if_ (.call "iszero" [.ident ecwrSuccess])
        [ .let_ "__ecwr_rds" (.call "returndatasize" [])
        , .expr (.call "returndatacopy" [.lit 0, .lit 0, .ident "__ecwr_rds"])
        , .expr (.call "revert" [.lit 0, .ident "__ecwr_rds"])
        ] :: rest =>
        if hasAccrueInterestCompatBaseName "__ecwr_success" ecwrSuccess then
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          ( [ .if_ (.call "iszero" [.ident ecwrSuccess])
                [ .let_ "__compat_returndata" (.call "extract_returndata" [])
                , .expr
                    (.call "revert"
                      [ .call "add" [.ident "__compat_returndata", .lit 32]
                      , .call "mload" [.ident "__compat_returndata"]
                      ])
                ]
            ] ++ rest'
          , rewrittenTail + 1)
        else
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          (.if_ (.call "iszero" [.ident ecwrSuccess])
              [ .let_ "__ecwr_rds" (.call "returndatasize" [])
              , .expr (.call "returndatacopy" [.lit 0, .lit 0, .ident "__ecwr_rds"])
              , .expr (.call "revert" [.lit 0, .ident "__ecwr_rds"])
              ] :: rest',
            rewrittenTail)
    | .if_ (.call "iszero" [.ident ecwrSuccess])
        [ .let_ posName (.call "mload" [posPtr])
        , .expr (.call "returndatacopy" [.ident copyPosName, .lit 0, .call "returndatasize" []])
        , .expr (.call "revert" [.ident revertPosName, .call "returndatasize" []])
        ] :: rest =>
        if hasAccrueInterestCompatBaseName "__ecwr_success" ecwrSuccess &&
            decide (posName = copyPosName) &&
            decide (posName = revertPosName) then
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          ( [ .if_ (.call "iszero" [.ident ecwrSuccess])
                [ .let_ "__compat_returndata" (.call "extract_returndata" [])
                , .expr
                    (.call "revert"
                      [ .call "add" [.ident "__compat_returndata", .lit 32]
                      , .call "mload" [.ident "__compat_returndata"]
                      ])
                ]
            ] ++ rest'
          , rewrittenTail + 1)
        else
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          (.if_ (.call "iszero" [.ident ecwrSuccess])
              [ .let_ posName (.call "mload" [posPtr])
              , .expr (.call "returndatacopy" [.ident copyPosName, .lit 0, .call "returndatasize" []])
              , .expr (.call "revert" [.ident revertPosName, .call "returndatasize" []])
              ] :: rest',
            rewrittenTail)
    | .expr (.call "mstore" [.lit 0, .call "mload" [.ident compatAllocPtrMstore]]) ::
      (.if_ (.call "iszero" [.ident ecwrSuccessIf])
        [ .let_ posNameIf (.call "mload" [posPtrIf])
        , .expr (.call "returndatacopy" [.ident copyPosNameIf, .lit 0, .call "returndatasize" []])
        , .expr (.call "revert" [.ident revertPosNameIf, .call "returndatasize" []])
        ]) ::
      (.if_ (.call "lt" [.call "returndatasize" [], .lit 32])
        [ .expr (.call "revert" [.lit 0, .lit 0]) ]) ::
      (.let_ "borrowRate" (.call "mload" [.lit 0])) :: rest =>
        if hasAccrueInterestCompatBaseName "__compat_alloc_ptr" compatAllocPtrMstore &&
            hasAccrueInterestCompatBaseName "__ecwr_success" ecwrSuccessIf &&
            decide (posNameIf = copyPosNameIf) &&
            decide (posNameIf = revertPosNameIf) then
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          ( [ .if_ (.call "iszero" [.ident ecwrSuccessIf])
                [ .let_ "__compat_returndata" (.call "extract_returndata" [])
                , .expr
                    (.call "revert"
                      [ .call "add" [.ident "__compat_returndata", .lit 32]
                      , .call "mload" [.ident "__compat_returndata"]
                      ])
                ]
            , .let_ "borrowRate" (.lit 0)
            , .if_ (.ident ecwrSuccessIf)
                [ .let_ "__compat_returndata_size" (.lit 32)
                , .if_ (.call "gt" [.lit 32, .call "returndatasize" []])
                    [ .assign "__compat_returndata_size" (.call "returndatasize" []) ]
                , .expr
                    (.call "finalize_allocation"
                      [ .ident compatAllocPtrMstore
                      , .ident "__compat_returndata_size"
                      ])
                , .if_
                    (.call "slt"
                      [ .call "sub"
                          [ .call "add"
                              [ .ident compatAllocPtrMstore
                              , .ident "__compat_returndata_size"
                              ]
                          , .ident compatAllocPtrMstore
                          ]
                      , .lit 32
                      ])
                    [ .expr (.call "revert" [.lit 0, .lit 0]) ]
                , .assign "borrowRate" (.call "mload" [.ident compatAllocPtrMstore])
                ]
            ] ++ rest'
          , rewrittenTail + 1)
        else
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          ( .expr (.call "mstore" [.lit 0, .call "mload" [.ident compatAllocPtrMstore]]) ::
            .if_ (.call "iszero" [.ident ecwrSuccessIf])
              [ .let_ posNameIf (.call "mload" [posPtrIf])
              , .expr (.call "returndatacopy" [.ident copyPosNameIf, .lit 0, .call "returndatasize" []])
              , .expr (.call "revert" [.ident revertPosNameIf, .call "returndatasize" []])
              ] ::
            .if_ (.call "lt" [.call "returndatasize" [], .lit 32])
              [ .expr (.call "revert" [.lit 0, .lit 0]) ] ::
            .let_ "borrowRate" (.call "mload" [.lit 0]) ::
            rest'
          , rewrittenTail)
    | .let_ compatAllocPtrLet (.call "mload" [.lit 64]) ::
      (.expr (.call "finalize_allocation_27020" [.ident compatAllocPtrFinalize20])) ::
      (.expr (.call "finalize_allocation_27033" [.ident compatAllocPtrFinalize33])) ::
      (.expr (.call "finalize_allocation" [.ident compatAllocPtrFinalize, .lit 32])) ::
      (.let_ ecwrSuccessLet
        (.call "call"
          [ .call "gas" []
          , .ident "irm"
          , .lit 0
          , .lit 0
          , .lit 356
          , .ident compatAllocPtrCall
          , .lit 32
          ])) ::
      (.expr (.call "mstore" [.lit 0, .call "mload" [.ident compatAllocPtrMstore]])) ::
      (.if_ (.call "iszero" [.ident ecwrSuccessIf])
        [ .let_ posNameIf (.call "mload" [posPtrIf])
        , .expr (.call "returndatacopy" [.ident copyPosNameIf, .lit 0, .call "returndatasize" []])
        , .expr (.call "revert" [.ident revertPosNameIf, .call "returndatasize" []])
        ]) ::
      (.if_ (.call "lt" [.call "returndatasize" [], .lit 32])
        [ .expr (.call "revert" [.lit 0, .lit 0]) ]) :: rest =>
        if hasAccrueInterestCompatBaseName "__compat_alloc_ptr" compatAllocPtrLet &&
            hasAccrueInterestCompatBaseName "__compat_alloc_ptr" compatAllocPtrFinalize20 &&
            hasAccrueInterestCompatBaseName "__compat_alloc_ptr" compatAllocPtrFinalize33 &&
            hasAccrueInterestCompatBaseName "__compat_alloc_ptr" compatAllocPtrFinalize &&
            hasAccrueInterestCompatBaseName "__compat_alloc_ptr" compatAllocPtrCall &&
            hasAccrueInterestCompatBaseName "__compat_alloc_ptr" compatAllocPtrMstore &&
            hasAccrueInterestCompatBaseName "__ecwr_success" ecwrSuccessLet &&
            hasAccrueInterestCompatBaseName "__ecwr_success" ecwrSuccessIf &&
            decide (posNameIf = copyPosNameIf) &&
            decide (posNameIf = revertPosNameIf) &&
            decide (compatAllocPtrLet = compatAllocPtrFinalize20) &&
            decide (compatAllocPtrLet = compatAllocPtrFinalize33) &&
            decide (compatAllocPtrLet = compatAllocPtrFinalize) &&
            decide (compatAllocPtrLet = compatAllocPtrCall) &&
            decide (compatAllocPtrLet = compatAllocPtrMstore) &&
            decide (ecwrSuccessLet = ecwrSuccessIf) then
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          ( [ .let_ compatAllocPtrLet (.call "mload" [.lit 64])
            , .expr (.call "finalize_allocation_27020" [.ident compatAllocPtrLet])
            , .expr (.call "finalize_allocation_27033" [.ident compatAllocPtrLet])
            , .expr (.call "finalize_allocation" [.ident compatAllocPtrLet, .lit 32])
            , .let_ ecwrSuccessLet
                (.call "call"
                  [ .call "gas" []
                  , .ident "irm"
                  , .lit 0
                  , .lit 0
                  , .lit 356
                  , .ident compatAllocPtrLet
                  , .lit 32
                  ])
            , .if_ (.call "iszero" [.ident ecwrSuccessLet])
                [ .let_ "__compat_returndata" (.call "extract_returndata" [])
                , .expr
                    (.call "revert"
                      [ .call "add" [.ident "__compat_returndata", .lit 32]
                      , .call "mload" [.ident "__compat_returndata"]
                      ])
                ]
            , .if_ (.call "lt" [.call "returndatasize" [], .lit 32])
                [ .expr (.call "revert" [.lit 0, .lit 0]) ]
            , .expr (.call "mstore" [.lit 0, .call "mload" [.ident compatAllocPtrLet]])
            ] ++ rest'
          , rewrittenTail + 1)
        else
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          ( .let_ compatAllocPtrLet (.call "mload" [.lit 64]) ::
            .expr (.call "finalize_allocation_27020" [.ident compatAllocPtrFinalize20]) ::
            .expr (.call "finalize_allocation_27033" [.ident compatAllocPtrFinalize33]) ::
            .expr (.call "finalize_allocation" [.ident compatAllocPtrFinalize, .lit 32]) ::
            .let_ ecwrSuccessLet
              (.call "call"
                [ .call "gas" []
                , .ident "irm"
                , .lit 0
                , .lit 0
                , .lit 356
                , .ident compatAllocPtrCall
                , .lit 32
                ]) ::
            .expr (.call "mstore" [.lit 0, .call "mload" [.ident compatAllocPtrMstore]]) ::
            .if_ (.call "iszero" [.ident ecwrSuccessIf])
              [ .let_ posNameIf (.call "mload" [posPtrIf])
              , .expr (.call "returndatacopy" [.ident copyPosNameIf, .lit 0, .call "returndatasize" []])
              , .expr (.call "revert" [.ident revertPosNameIf, .call "returndatasize" []])
              ] ::
            .if_ (.call "lt" [.call "returndatasize" [], .lit 32])
              [ .expr (.call "revert" [.lit 0, .lit 0]) ] ::
            rest'
          , rewrittenTail)
    | .let_ ecwrSuccessLet
        (.call "call"
          [ .call "gas" []
          , .ident "irm"
          , .lit 0
          , .lit 0
          , .lit 356
          , .ident compatAllocPtrCall
          , .lit 32
          ]) ::
      (.expr (.call "mstore" [.lit 0, .call "mload" [.ident compatAllocPtrMstore]])) ::
      (.if_ (.call "iszero" [.ident ecwrSuccessIf])
        [ .let_ posNameIf (.call "mload" [posPtrIf])
        , .expr (.call "returndatacopy" [.ident copyPosNameIf, .lit 0, .call "returndatasize" []])
        , .expr (.call "revert" [.ident revertPosNameIf, .call "returndatasize" []])
        ]) ::
      (.if_ (.call "lt" [.call "returndatasize" [], .lit 32])
        [ .expr (.call "revert" [.lit 0, .lit 0]) ]) :: rest =>
        if hasAccrueInterestCompatBaseName "__ecwr_success" ecwrSuccessLet &&
            hasAccrueInterestCompatBaseName "__ecwr_success" ecwrSuccessIf &&
            hasAccrueInterestCompatBaseName "__compat_alloc_ptr" compatAllocPtrCall &&
            hasAccrueInterestCompatBaseName "__compat_alloc_ptr" compatAllocPtrMstore &&
            decide (posNameIf = copyPosNameIf) &&
            decide (posNameIf = revertPosNameIf) &&
            decide (ecwrSuccessLet = ecwrSuccessIf) &&
            decide (compatAllocPtrCall = compatAllocPtrMstore) then
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          ( [ .let_ ecwrSuccessLet
                (.call "call"
                  [ .call "gas" []
                  , .ident "irm"
                  , .lit 0
                  , .lit 0
                  , .lit 356
                  , .ident compatAllocPtrCall
                  , .lit 32
                  ])
            , .if_ (.call "iszero" [.ident ecwrSuccessLet])
                [ .let_ "__compat_returndata" (.call "extract_returndata" [])
                , .expr
                    (.call "revert"
                      [ .call "add" [.ident "__compat_returndata", .lit 32]
                      , .call "mload" [.ident "__compat_returndata"]
                      ])
                ]
            , .if_ (.call "lt" [.call "returndatasize" [], .lit 32])
                [ .expr (.call "revert" [.lit 0, .lit 0]) ]
            , .expr (.call "mstore" [.lit 0, .call "mload" [.ident compatAllocPtrCall]])
            ] ++ rest'
          , rewrittenTail + 1)
        else
          let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
          ( .let_ ecwrSuccessLet
              (.call "call"
                [ .call "gas" []
                , .ident "irm"
                , .lit 0
                , .lit 0
                , .lit 356
                , .ident compatAllocPtrCall
                , .lit 32
                ]) ::
            .expr (.call "mstore" [.lit 0, .call "mload" [.ident compatAllocPtrMstore]]) ::
            .if_ (.call "iszero" [.ident ecwrSuccessIf])
              [ .let_ posNameIf (.call "mload" [posPtrIf])
              , .expr (.call "returndatacopy" [.ident copyPosNameIf, .lit 0, .call "returndatasize" []])
              , .expr (.call "revert" [.ident revertPosNameIf, .call "returndatasize" []])
              ] ::
            .if_ (.call "lt" [.call "returndatasize" [], .lit 32])
              [ .expr (.call "revert" [.lit 0, .lit 0]) ] ::
            rest'
          , rewrittenTail)
    | stmt :: rest =>
        let (stmt', rewrittenHead) := rewriteAccrueInterestCheckedArithmeticStmt stmt
        let (rest', rewrittenTail) := rewriteAccrueInterestCheckedArithmeticStmts rest
        (stmt' :: rest', rewrittenHead + rewrittenTail)

end

def solcCompatPruneUnreachableHelpersProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_prune_unreachable_helpers_preserves"

/-- Canonicalize Verity internal helper naming to `solc`-style `fun_*` names when collision-free. -/
def solcCompatCanonicalizeInternalFunNamesProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_canonicalize_internal_fun_names_preserves"

/-- Deduplicate top-level helper definitions that are structurally equivalent. -/
def solcCompatDedupeEquivalentHelpersProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_dedupe_equivalent_helpers_preserves"

/-- Inline dispatch wrapper case calls to top-level zero-arity `fun_*` helper definitions. -/
def solcCompatInlineDispatchWrapperCallsProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_inline_dispatch_wrapper_calls_preserves"

/-- Outline switch dispatch case bodies into explicit top-level `fun_*` helpers. -/
def solcCompatOutlineDispatchHelpersProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_outline_dispatch_helpers_preserves"

/-- Inline direct `keccakMarketParams(...)` helper calls into explicit memory writes + `keccak256`. -/
def solcCompatInlineKeccakMarketParamsCallsProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_inline_keccak_market_params_calls_preserves"

/-- Inline `mappingSlot(baseSlot, key)` helper calls into explicit scratch writes + `keccak256`. -/
def solcCompatInlineMappingSlotCallsProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_inline_mapping_slot_calls_preserves"

def solcCompatDropUnusedKeccakMarketParamsHelperProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_drop_unused_keccak_market_params_helper_preserves"

def solcCompatDropUnusedMappingSlotHelperProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_drop_unused_mapping_slot_helper_preserves"

def solcCompatPruneUnreachableDeployHelpersProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_prune_unreachable_deploy_helpers_preserves"

def solcCompatRewriteNonceIncrementProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_rewrite_nonce_increment_preserves"

def solcCompatRewriteElapsedCheckedSubProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_rewrite_elapsed_checked_sub_preserves"

def solcCompatRewriteAccrueInterestCheckedArithmeticProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_rewrite_accrue_interest_checked_arithmetic_preserves"

def solcCompatRewriteAccrueInterestPrologueTempsProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_rewrite_accrue_interest_prologue_temps_preserves"

def solcCompatRewriteAccrueInterestIrmGuardProofRef : Lean.Name :=
  proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_rewrite_accrue_interest_irm_guard_preserves"

private def findEquivalentTopLevelHelper?
    (seen : List (String × List String × List String × String))
    (params rets : List String)
    (body : List YulStmt) : Option String :=
  let bodyKey : String := reprStr body
  match seen.find? (fun entry =>
      decide (entry.2.1 = params) && decide (entry.2.2.1 = rets) && decide (entry.2.2.2 = bodyKey)) with
  | some entry => some entry.1
  | none => none

private def dedupeEquivalentTopLevelHelpers (stmts : List YulStmt) : List YulStmt × Nat :=
  let step := fun (acc : (List YulStmt × List (String × List String × List String × String) ×
      List (String × String) × Nat)) (stmt : YulStmt) =>
    let (keptRev, seen, renames, removed) := acc
    match stmt with
    | .funcDef name params rets body =>
        match findEquivalentTopLevelHelper? seen params rets body with
        | some canonical =>
            let renames' :=
              if canonical = name || renames.any (fun pair => pair.fst = name && pair.snd = canonical) then
                renames
              else
                renames ++ [(name, canonical)]
            (keptRev, seen, renames', removed + 1)
        | none =>
            (.funcDef name params rets body :: keptRev, (name, params, rets, reprStr body) :: seen, renames, removed)
    | _ =>
        (stmt :: keptRev, seen, renames, removed)
  let (keptRev, _, renames, removed) := stmts.foldl step ([], [], [], 0)
  let kept := keptRev.reverse
  if removed = 0 then
    (stmts, 0)
  else if renames.isEmpty then
    (kept, removed)
  else
    (renameCallsInStmts renames kept, removed)

private def dropUnusedTopLevelFunctionByName (stmts : List YulStmt) (name : String) : List YulStmt × Nat :=
  let (wrapped, topStmts) :=
    match stmts with
    | [.block inner] => (true, inner)
    | _ => (false, stmts)
  let (withoutTarget, removed) :=
    topStmts.foldr
      (fun stmt (accStmts, accRemoved) =>
        match stmt with
        | .funcDef defName params rets body =>
            if defName = name then
              (accStmts, accRemoved + 1)
            else
              (.funcDef defName params rets body :: accStmts, accRemoved)
        | _ => (stmt :: accStmts, accRemoved))
      ([], 0)
  if removed = 0 then
    (stmts, 0)
  else if (callNamesInStmts withoutTarget).any (fun called => called = name) then
    (stmts, 0)
  else if wrapped then
    ([.block withoutTarget], removed)
  else
    (withoutTarget, removed)

/-- Canonicalize `internal__*` helper names to `fun_*` and rewrite in-object call sites.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatCanonicalizeInternalFunNamesRule : ObjectPatchRule :=
  { patchName := "solc-compat-canonicalize-internal-fun-names"
    pattern := "function internal__X(...) with in-object call sites"
    rewrite := "function fun_X(...) with updated in-object call sites"
    sideConditions :=
      [ "only top-level function names with prefix internal__ are considered"
      , "target fun_* name must not already be defined in the same object code list"
      , "if two internal__ names map to the same target, only the first is renamed" ]
    proofId := solcCompatCanonicalizeInternalFunNamesProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 210
    applyObject := fun _ obj =>
      let (deployCode', deployRenamed) := canonicalizeInternalFunNames obj.deployCode
      let (runtimeCode', runtimeRenamed) := canonicalizeInternalFunNames obj.runtimeCode
      if deployRenamed + runtimeRenamed = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Outline labeled runtime switch cases as explicit `fun_*` helper defs and dispatch via calls.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatOutlineDispatchHelpersRule : ObjectPatchRule :=
  { patchName := "solc-compat-outline-dispatch-helpers"
    pattern := "runtime switch case body prefixed with comment `<name>()`"
    rewrite := "insert top-level `fun_<name>` helper and replace case body with helper call"
    sideConditions :=
      [ "only runtime code is transformed"
      , "labels `fallback()` and `receive()` are excluded"
      , "existing `fun_*` names are collision-safe and never overwritten"
      , "outlined helper parameters/returns are empty (dispatch shape only)" ]
    proofId := solcCompatOutlineDispatchHelpersProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 215
    applyObject := fun _ obj =>
      let (runtimeCode', outlined) := outlineRuntimeDispatchHelpers obj.runtimeCode
      if outlined = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Deduplicate top-level helper function defs that are structurally equivalent.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatDedupeEquivalentHelpersRule : ObjectPatchRule :=
  { patchName := "solc-compat-dedupe-equivalent-helpers"
    pattern := "duplicate top-level helper defs with equivalent params/returns/body"
    rewrite := "retain first helper def, rewrite call sites to retained helper"
    sideConditions :=
      [ "only top-level function definitions are considered"
      , "equivalence requires exact params/returns/body structural equality"
      , "the first encountered equivalent helper is canonical" ]
    proofId := solcCompatDedupeEquivalentHelpersProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 205
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := dedupeEquivalentTopLevelHelpers obj.deployCode
      let (runtimeCode', runtimeRemoved) := dedupeEquivalentTopLevelHelpers obj.runtimeCode
      if deployRemoved + runtimeRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Inline runtime switch case bodies of the form `fun_X()` to the corresponding zero-arity helper body.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatInlineDispatchWrapperCallsRule : ObjectPatchRule :=
  { patchName := "solc-compat-inline-dispatch-wrapper-calls"
    pattern := "runtime switch case body with a single call to `fun_*`"
    rewrite := "replace case body with the referenced top-level zero-arity helper body"
    sideConditions :=
      [ "only runtime code is transformed"
      , "case body must be exactly one statement: `fun_*()` call"
      , "target helper must be a top-level zero-arity definition in the same object" ]
    proofId := solcCompatInlineDispatchWrapperCallsProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 212
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := inlineRuntimeDispatchWrapperCalls obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Inline runtime direct `keccakMarketParams(...)` helper calls to `mstore`/`keccak256` sequence.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatInlineKeccakMarketParamsCallsRule : ObjectPatchRule :=
  { patchName := "solc-compat-inline-keccak-market-params-calls"
    pattern := "let/assign using direct call `keccakMarketParams(a,b,c,d,e)`"
    rewrite := "replace with explicit memory writes at [0,32,64,96,128] then `keccak256(0,160)`"
    sideConditions :=
      [ "only runtime code is transformed"
      , "only direct `.let_`/`.assign` calls are rewritten"
      , "exactly five arguments are required"
      , "scratch memory clobbering follows existing helper semantics" ]
    proofId := solcCompatInlineKeccakMarketParamsCallsProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := inlineRuntimeKeccakMarketParamsCalls obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Inline runtime `mappingSlot(baseSlot, key)` helper calls into explicit `mstore`/`keccak256`.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatInlineMappingSlotCallsRule : ObjectPatchRule :=
  { patchName := "solc-compat-inline-mapping-slot-calls"
    pattern := "expression call `mappingSlot(baseSlot, key)`"
    rewrite := "introduce scratch writes to [512,544] and replace call with a fresh slot temporary"
    sideConditions :=
      [ "only runtime code is transformed"
      , "only calls with exactly two arguments are rewritten"
      , "loop-condition expressions are intentionally not rewritten"
      , "fresh temporary names use reserved prefix `__compat_mapping_slot_`"
      , "scratch memory clobbering follows existing `mappingSlot` helper semantics (base 512)" ]
    proofId := solcCompatInlineMappingSlotCallsProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := inlineRuntimeMappingSlotCalls obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Drop top-level runtime `keccakMarketParams` helper when no call sites remain.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatDropUnusedKeccakMarketParamsHelperRule : ObjectPatchRule :=
  { patchName := "solc-compat-drop-unused-keccak-market-params-helper"
    pattern := "top-level helper definition `keccakMarketParams` with no remaining call sites"
    rewrite := "remove helper definition"
    sideConditions :=
      [ "deploy/runtime code is transformed"
      , "only top-level definitions named `keccakMarketParams` are considered"
      , "helper is removed only when no call site remains in the same object section" ]
    proofId := solcCompatDropUnusedKeccakMarketParamsHelperProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 210
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := dropUnusedTopLevelFunctionByName obj.deployCode "keccakMarketParams"
      let (runtimeCode', runtimeRemoved) := dropUnusedTopLevelFunctionByName obj.runtimeCode "keccakMarketParams"
      if deployRemoved + runtimeRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Drop top-level runtime `mappingSlot` helper when no call sites remain.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatDropUnusedMappingSlotHelperRule : ObjectPatchRule :=
  { patchName := "solc-compat-drop-unused-mapping-slot-helper"
    pattern := "top-level helper definition `mappingSlot` with no remaining call sites"
    rewrite := "remove helper definition"
    sideConditions :=
      [ "deploy/runtime code is transformed"
      , "only top-level definitions named `mappingSlot` are considered"
      , "helper is removed only when no call site remains in the same object section" ]
    proofId := solcCompatDropUnusedMappingSlotHelperProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 210
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := dropUnusedTopLevelFunctionByName obj.deployCode "mappingSlot"
      let (runtimeCode', runtimeRemoved) := dropUnusedTopLevelFunctionByName obj.runtimeCode "mappingSlot"
      if deployRemoved + runtimeRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Rewrite nonce increments from `add(currentNonce, 1)` to `increment_uint256(currentNonce)`.
    Insert `increment_uint256` helper only when referenced and absent.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatRewriteNonceIncrementRule : ObjectPatchRule :=
  { patchName := "solc-compat-rewrite-nonce-increment"
    pattern := "runtime expression `add(currentNonce, 1)`"
    rewrite := "replace with `increment_uint256(currentNonce)` and materialize helper if needed"
    sideConditions :=
      [ "only runtime code is transformed"
      , "rewrite is scoped to identifier name `currentNonce`"
      , "helper insertion is top-level, deterministic, and only when absent" ]
    proofId := solcCompatRewriteNonceIncrementProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := rewriteCurrentNonceIncrementStmts obj.runtimeCode
      let (runtimeCode'', inserted) := materializeIncrementUint256HelperIfCalled runtimeCode'
      if rewritten + inserted = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode'' } }

/-- Rewrite `sub(timestamp(), prevLastUpdate)` to `checked_sub_uint256(timestamp(), prevLastUpdate)`.
    Insert `checked_sub_uint256` helper only when referenced and absent.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatRewriteElapsedCheckedSubRule : ObjectPatchRule :=
  { patchName := "solc-compat-rewrite-elapsed-checked-sub"
    pattern := "runtime expression `sub(timestamp(), prevLastUpdate)`"
    rewrite := "replace with `checked_sub_uint256(timestamp(), prevLastUpdate)` and materialize helper if needed"
    sideConditions :=
      [ "only runtime code is transformed"
      , "rewrite is scoped to identifier name `prevLastUpdate`"
      , "helper insertion is top-level, deterministic, and only when absent" ]
    proofId := solcCompatRewriteElapsedCheckedSubProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := rewriteElapsedCheckedSubStmts obj.runtimeCode
      let (runtimeCode'', inserted) := materializeCheckedSubUint256HelperIfCalled runtimeCode'
      if rewritten + inserted = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode'' } }

/-- Rewrite selected runtime `accrueInterest` arithmetic patterns to
    Solidity-style checked helper calls (`checked_add_uint256` / `checked_add_uint128` /
    `checked_sub_uint128` / `checked_mul_uint256` / `checked_div_uint256`), plus
    explicit `fun_toUint128(...)` casts for selected uint128 add operands.
    Insert helpers only when referenced and absent.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatRewriteAccrueInterestCheckedArithmeticRule : ObjectPatchRule :=
  { patchName := "solc-compat-rewrite-accrue-interest-checked-arithmetic"
    pattern := "selected runtime arithmetic and structural `accrueInterest` patterns, including uint128 cast and compat timestamp-write shape"
    rewrite := "replace with checked helper calls, canonical `accrueInterest` structural forms, and `fun_toUint128` casts, then materialize referenced helpers if needed"
    sideConditions :=
      [ "only runtime code is transformed"
      , "rewrite is scoped to known identifier-shape arithmetic and guarded structural patterns in accrue-interest flow"
      , "helper insertion is top-level, deterministic, and only when absent" ]
    proofId := solcCompatRewriteAccrueInterestCheckedArithmeticProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := rewriteAccrueInterestCheckedArithmeticStmts obj.runtimeCode
      let (runtimeCode'', inserted) := materializeCheckedAddMulDivUint256HelpersIfCalled runtimeCode'
      if rewritten + inserted = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode'' } }

/-- Rewrite runtime two-arg `fun_accrueInterest(var_marketParams_46531_mpos, var_id)` prologue
    into Solidity-style scratch-slot temp bindings (`_1.._5`) for deterministic parity.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatRewriteAccrueInterestPrologueTempsRule : ObjectPatchRule :=
  { patchName := "solc-compat-rewrite-accrue-interest-prologue-temps"
    pattern := "runtime `fun_accrueInterest` prologue with direct `mstore(512, var_id)` / `mstore(544, 3)` and compat slot-0 elapsed check"
    rewrite := "materialize Solidity-style `_1.._5` temps and canonicalize prevLastUpdate source to `and(sload(add(keccak256(_1, _5), 2)), _4)`"
    sideConditions :=
      [ "only runtime code is transformed"
      , "rewrite is scoped to `fun_accrueInterest(var_marketParams_46531_mpos, var_id)`"
      , "compat elapsed-check shape must match exactly"
      , "rewrite is skipped when `_1.._5` names are already locally bound" ]
    proofId := solcCompatRewriteAccrueInterestPrologueTempsProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := rewriteAccrueInterestPrologueTempsStmts obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Rewrite runtime `accrueInterest` IRM non-zero guard shape to Solidity-style masked
    `cleaned` guard form. This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatRewriteAccrueInterestIrmGuardRule : ObjectPatchRule :=
  { patchName := "solc-compat-rewrite-accrue-interest-irm-guard"
    pattern := "runtime `if iszero(eq(mload(add(var_marketParams_*, 96)), 0))` guard"
    rewrite := "replace with masked `cleaned` temporary and `if iszero(iszero(cleaned))`"
    sideConditions :=
      [ "only runtime code is transformed"
      , "rewrite is scoped to `var_marketParams_*` pointer names"
      , "helper insertion remains unchanged" ]
    proofId := solcCompatRewriteAccrueInterestIrmGuardProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := rewriteAccrueInterestIrmGuardStmts obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Remove unreachable top-level helper function definitions in deploy/runtime code.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatPruneUnreachableHelpersRule : ObjectPatchRule :=
  { patchName := "solc-compat-prune-unreachable-helpers"
    pattern := "object-level top-level helper function defs"
    rewrite := "remove helpers not reachable from non-function statements"
    sideConditions :=
      [ "only top-level function definitions are considered"
      , "reachability is computed transitively from non-function statements"
      , "helpers called by reachable helpers are retained" ]
    proofId := solcCompatPruneUnreachableHelpersProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 200
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := pruneUnreachableTopLevelHelpers obj.deployCode
      let (runtimeCode', runtimeRemoved) := pruneUnreachableTopLevelHelpers obj.runtimeCode
      if deployRemoved + runtimeRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Remove unreachable top-level helper function definitions in deploy code only.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatPruneUnreachableDeployHelpersRule : ObjectPatchRule :=
  { patchName := "solc-compat-prune-unreachable-deploy-helpers"
    pattern := "deploy-level top-level helper function defs"
    rewrite := "remove deploy helpers not reachable from non-function deploy statements"
    sideConditions :=
      [ "only top-level function definitions in deploy code are considered"
      , "reachability is computed transitively from deploy non-function statements"
      , "runtime code is unchanged" ]
    proofId := solcCompatPruneUnreachableDeployHelpersProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 209
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := pruneUnreachableTopLevelHelpers obj.deployCode
      if deployRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode' } }

structure RewriteRuleBundle where
  id : String
  exprRules : List ExprPatchRule
  stmtRules : List StmtPatchRule
  blockRules : List BlockPatchRule
  objectRules : List ObjectPatchRule

private def rewriteBundleProofAllowlist (bundle : RewriteRuleBundle) : List Lean.Name :=
  let exprProofs := bundle.exprRules.map (fun rule => rule.proofId)
  let stmtProofs := bundle.stmtRules.map (fun rule => rule.proofId)
  let blockProofs := bundle.blockRules.map (fun rule => rule.proofId)
  let objectProofs := bundle.objectRules.map (fun rule => rule.proofId)
  let allProofs := exprProofs ++ stmtProofs ++ blockProofs ++ objectProofs
  allProofs.foldl
    (fun acc proofRef => if acc.any (fun seen => seen = proofRef) then acc else acc ++ [proofRef])
    []

def foundationRewriteBundleId : String := "foundation"

def solcCompatRewriteBundleId : String := "solc-compat-v0"

/-- Baseline, non-compat rewrite bundle. -/
def foundationRewriteBundle : RewriteRuleBundle :=
  { id := foundationRewriteBundleId
    exprRules := foundationExprPatchPack
    stmtRules := foundationStmtPatchPack
    blockRules := foundationBlockPatchPack
    objectRules := foundationObjectPatchPack }

/-- Opt-in `solc` compatibility rewrite bundle.
    Initially aliases foundation rules until dedicated compatibility rewrites land. -/
def solcCompatRewriteBundle : RewriteRuleBundle :=
  { id := solcCompatRewriteBundleId
    exprRules := foundationExprPatchPack
    stmtRules := foundationStmtPatchPack
    blockRules := foundationBlockPatchPack
    objectRules := foundationObjectPatchPack ++
      [ solcCompatCanonicalizeInternalFunNamesRule
      , solcCompatInlineDispatchWrapperCallsRule
      , solcCompatInlineMappingSlotCallsRule
      , solcCompatInlineKeccakMarketParamsCallsRule
      , solcCompatRewriteElapsedCheckedSubRule
      , solcCompatRewriteAccrueInterestIrmGuardRule
      , solcCompatRewriteAccrueInterestCheckedArithmeticRule
      , solcCompatRewriteAccrueInterestPrologueTempsRule
      , solcCompatRewriteNonceIncrementRule
      , solcCompatPruneUnreachableDeployHelpersRule
      , solcCompatDropUnusedMappingSlotHelperRule
      , solcCompatDropUnusedKeccakMarketParamsHelperRule
      , solcCompatDedupeEquivalentHelpersRule ] }

def allRewriteBundles : List RewriteRuleBundle :=
  [foundationRewriteBundle, solcCompatRewriteBundle]

def supportedRewriteBundleIds : List String :=
  allRewriteBundles.map (·.id)

def findRewriteBundle? (bundleId : String) : Option RewriteRuleBundle :=
  allRewriteBundles.find? (fun bundle => bundle.id = bundleId)

def rewriteBundleForId (bundleId : String) : RewriteRuleBundle :=
  match findRewriteBundle? bundleId with
  | some bundle => bundle
  | none => foundationRewriteBundle

def rewriteProofAllowlistForId (bundleId : String) : List Lean.Name :=
  rewriteBundleProofAllowlist (rewriteBundleForId bundleId)

/-- Activation-time proof allowlist for the shipped foundation patch packs. -/
def foundationProofAllowlist : List Lean.Name :=
  rewriteBundleProofAllowlist foundationRewriteBundle

/-- Activation-time proof allowlist for the shipped `solc` compatibility patch bundle. -/
def solcCompatProofAllowlist : List Lean.Name :=
  rewriteBundleProofAllowlist solcCompatRewriteBundle
