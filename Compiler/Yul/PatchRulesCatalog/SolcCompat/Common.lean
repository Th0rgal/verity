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

def materializeIncrementUint256HelperIfCalled (stmts : List YulStmt) : List YulStmt × Nat :=
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

def materializeCheckedSubUint256HelperIfCalled (stmts : List YulStmt) : List YulStmt × Nat :=
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

def materializeCheckedAddMulDivUint256HelpersIfCalled (stmts : List YulStmt) : List YulStmt × Nat :=
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
