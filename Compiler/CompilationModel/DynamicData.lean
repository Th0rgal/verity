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

def checkedArrayElementWordCalldataHelperName : String :=
  "__verity_array_element_word_calldata_checked"

def checkedArrayElementWordMemoryHelperName : String :=
  "__verity_array_element_word_memory_checked"

def checkedArrayElementDynamicWordCalldataHelperName : String :=
  "__verity_array_element_dynamic_word_calldata_checked"

def checkedArrayElementDynamicWordMemoryHelperName : String :=
  "__verity_array_element_dynamic_word_memory_checked"

def checkedParamDynamicHeadWordCalldataHelperName : String :=
  "__verity_param_dynamic_head_word_calldata_checked"

def checkedParamDynamicHeadWordMemoryHelperName : String :=
  "__verity_param_dynamic_head_word_memory_checked"

/-- Yul helper name for `Expr.mulDiv512Down` — OpenZeppelin/Solmate-style
    full-precision multiply-divide with round-toward-zero. (verity#1761) -/
def fullMulDivHelperName : String :=
  "__verity_full_mul_div"

/-- Yul helper name for `Expr.mulDiv512Up` — OpenZeppelin-style
    full-precision multiply-divide with round-away-from-zero. (verity#1761) -/
def fullMulDivUpHelperName : String :=
  "__verity_full_mul_div_up"

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

private def checkedArrayElementWordHelper (helperName loadOp : String) : YulStmt :=
  let elementWordIndex :=
    YulExpr.call "add" [
      YulExpr.call "mul" [YulExpr.ident "index", YulExpr.ident "element_words"],
      YulExpr.ident "word_offset"
    ]
  let byteOffset := YulExpr.call "mul" [elementWordIndex, YulExpr.lit 32]
  YulStmt.funcDef helperName ["data_offset", "length", "index", "element_words", "word_offset"] ["word"] [
    YulStmt.if_ (YulExpr.call "iszero" [
      YulExpr.call "lt" [YulExpr.ident "index", YulExpr.ident "length"]
    ]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ],
    YulStmt.assign "word" (YulExpr.call loadOp [
      YulExpr.call "add" [
        YulExpr.ident "data_offset",
        byteOffset
      ]
    ])
  ]

def checkedArrayElementWordCalldataHelper : YulStmt :=
  checkedArrayElementWordHelper checkedArrayElementWordCalldataHelperName "calldataload"

def checkedArrayElementWordMemoryHelper : YulStmt :=
  checkedArrayElementWordHelper checkedArrayElementWordMemoryHelperName "mload"

private def checkedArrayElementDynamicWordHelper (helperName loadOp : String) (sizeExpr? : Option YulExpr) : YulStmt :=
  let offsetTableBytes := YulExpr.call "mul" [YulExpr.ident "length", YulExpr.lit 32]
  let elementOffsetSlot := YulExpr.call "add" [
    YulExpr.ident "data_offset",
    YulExpr.call "mul" [YulExpr.ident "index", YulExpr.lit 32]
  ]
  let wordPos := YulExpr.call "add" [
    YulExpr.call "add" [YulExpr.ident "data_offset", YulExpr.ident "__element_rel_offset"],
    YulExpr.call "mul" [YulExpr.ident "word_offset", YulExpr.lit 32]
  ]
  let sizeCheck :=
    match sizeExpr? with
    | some sizeExpr =>
        [YulStmt.if_ (YulExpr.call "gt" [
          YulExpr.ident "__element_word_pos",
          YulExpr.call "sub" [sizeExpr, YulExpr.lit 32]
        ]) [
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
        ]]
    | none => []
  YulStmt.funcDef helperName ["data_offset", "length", "index", "word_offset"] ["word"] (
    [
      YulStmt.if_ (YulExpr.call "iszero" [
        YulExpr.call "lt" [YulExpr.ident "index", YulExpr.ident "length"]
      ]) [
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
      ],
      YulStmt.let_ "__element_rel_offset" (YulExpr.call loadOp [elementOffsetSlot]),
      YulStmt.if_ (YulExpr.call "lt" [YulExpr.ident "__element_rel_offset", offsetTableBytes]) [
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
      ],
      YulStmt.let_ "__element_word_pos" wordPos
    ] ++ sizeCheck ++ [
      YulStmt.assign "word" (YulExpr.call loadOp [YulExpr.ident "__element_word_pos"])
    ])

def checkedArrayElementDynamicWordCalldataHelper : YulStmt :=
  checkedArrayElementDynamicWordHelper checkedArrayElementDynamicWordCalldataHelperName "calldataload" (some (YulExpr.call "calldatasize" []))

def checkedArrayElementDynamicWordMemoryHelper : YulStmt :=
  checkedArrayElementDynamicWordHelper checkedArrayElementDynamicWordMemoryHelperName "mload" none

/-- Yul helper for `Expr.paramDynamicHeadWord` (verity#1832). Reads the
    word at `data_offset + word_offset * 32`, where `data_offset` is the
    `{name}_data_offset` produced by `genDynamicParamLoads` for a
    dynamic-tuple parameter (verity#1839 ensures this points at the
    first head word of the tuple, not 32 bytes past it). Reverts if the
    computed position would read past `calldatasize - 32` (calldata
    variant); the memory variant trusts its source. -/
private def checkedParamDynamicHeadWordHelper (helperName loadOp : String) (sizeExpr? : Option YulExpr) : YulStmt :=
  let wordPos := YulExpr.call "add" [
    YulExpr.ident "data_offset",
    YulExpr.call "mul" [YulExpr.ident "word_offset", YulExpr.lit 32]
  ]
  let sizeCheck :=
    match sizeExpr? with
    | some sizeExpr =>
        [YulStmt.if_ (YulExpr.call "gt" [
          YulExpr.ident "__head_word_pos",
          YulExpr.call "sub" [sizeExpr, YulExpr.lit 32]
        ]) [
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
        ]]
    | none => []
  YulStmt.funcDef helperName ["data_offset", "word_offset"] ["word"] (
    [YulStmt.let_ "__head_word_pos" wordPos] ++ sizeCheck ++ [
      YulStmt.assign "word" (YulExpr.call loadOp [YulExpr.ident "__head_word_pos"])
    ])

def checkedParamDynamicHeadWordCalldataHelper : YulStmt :=
  checkedParamDynamicHeadWordHelper checkedParamDynamicHeadWordCalldataHelperName "calldataload" (some (YulExpr.call "calldatasize" []))

def checkedParamDynamicHeadWordMemoryHelper : YulStmt :=
  checkedParamDynamicHeadWordHelper checkedParamDynamicHeadWordMemoryHelperName "mload" none

/-- OpenZeppelin/Solmate-style full-precision multiply-divide:
    `fullMulDiv(a, b, c)` returns `floor((a * b) / c)` where the
    intermediate product is computed at 512-bit precision. Reverts on
    division by zero (`Panic(0x12)` shape) and on quotient overflow
    (`Panic(0x11)` shape).

    Algorithm: compute the 512-bit product `[prod1 prod0] = a * b`
    using the mulmod identity; if the high word `prod1` is zero, fall
    back to the cheap 256-bit case; otherwise perform 512-by-256
    division via modular-inverse of the denominator's odd part after
    factoring out powers of two.

    Implementation mirrors `OpenZeppelin Math.mulDiv` /
    `Solmate FullMath.mulDiv`. (verity#1761) -/
def fullMulDivHelper : YulStmt :=
  YulStmt.funcDef fullMulDivHelperName ["a", "b", "denominator"] ["result"] [
    -- 512-bit multiply: prod0 = low 256 bits, prod1 = high 256 bits.
    YulStmt.let_ "mm" (YulExpr.call "mulmod" [
      YulExpr.ident "a", YulExpr.ident "b",
      YulExpr.call "not" [YulExpr.lit 0]
    ]),
    YulStmt.let_ "prod0" (YulExpr.call "mul" [YulExpr.ident "a", YulExpr.ident "b"]),
    YulStmt.let_ "prod1" (YulExpr.call "sub" [
      YulExpr.call "sub" [YulExpr.ident "mm", YulExpr.ident "prod0"],
      YulExpr.call "lt" [YulExpr.ident "mm", YulExpr.ident "prod0"]
    ]),
    -- Short-circuit when the product fits in 256 bits.
    YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "prod1"]) [
      YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "denominator"]) [
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
      ],
      YulStmt.assign "result" (YulExpr.call "div" [
        YulExpr.ident "prod0", YulExpr.ident "denominator"
      ]),
      YulStmt.leave
    ],
    -- Otherwise: prod1 != 0 → quotient fits iff denominator > prod1.
    YulStmt.if_ (YulExpr.call "iszero" [
      YulExpr.call "gt" [YulExpr.ident "denominator", YulExpr.ident "prod1"]
    ]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ],
    -- 512-by-256 division (Knuth Algorithm D / OpenZeppelin Math.mulDiv).
    -- Step 1: subtract the remainder from [prod1 prod0].
    YulStmt.let_ "remainder" (YulExpr.call "mulmod" [
      YulExpr.ident "a", YulExpr.ident "b", YulExpr.ident "denominator"
    ]),
    YulStmt.assign "prod1" (YulExpr.call "sub" [
      YulExpr.ident "prod1",
      YulExpr.call "lt" [YulExpr.ident "prod0", YulExpr.ident "remainder"]
    ]),
    YulStmt.assign "prod0" (YulExpr.call "sub" [
      YulExpr.ident "prod0", YulExpr.ident "remainder"
    ]),
    -- Step 2: factor powers of two out of the denominator.
    YulStmt.let_ "twos" (YulExpr.call "and" [
      YulExpr.call "sub" [YulExpr.lit 0, YulExpr.ident "denominator"],
      YulExpr.ident "denominator"
    ]),
    YulStmt.assign "denominator" (YulExpr.call "div" [
      YulExpr.ident "denominator", YulExpr.ident "twos"
    ]),
    YulStmt.assign "prod0" (YulExpr.call "div" [
      YulExpr.ident "prod0", YulExpr.ident "twos"
    ]),
    YulStmt.assign "twos" (YulExpr.call "add" [
      YulExpr.call "div" [
        YulExpr.call "sub" [YulExpr.lit 0, YulExpr.ident "twos"],
        YulExpr.ident "twos"
      ],
      YulExpr.lit 1
    ]),
    YulStmt.assign "prod0" (YulExpr.call "or" [
      YulExpr.ident "prod0",
      YulExpr.call "mul" [YulExpr.ident "prod1", YulExpr.ident "twos"]
    ]),
    -- Step 3: modular inverse of the (now-odd) denominator mod 2^256.
    -- Six Hensel-lifting rounds raise the 4-bit seed `xor(2, 3*denominator)`
    -- to full 256-bit precision (4 → 8 → 16 → 32 → 64 → 128 → 256).
    -- OpenZeppelin's `Math.mulDiv` and Uniswap V3's `FullMath.mulDiv` use the
    -- same six iterations; a seventh would lift to 512 bits, which is the
    -- same value mod 2^256.
    YulStmt.let_ "inverse" (YulExpr.call "xor" [
      YulExpr.lit 2,
      YulExpr.call "mul" [YulExpr.lit 3, YulExpr.ident "denominator"]
    ]),
    YulStmt.assign "inverse" (YulExpr.call "mul" [
      YulExpr.ident "inverse",
      YulExpr.call "sub" [
        YulExpr.lit 2,
        YulExpr.call "mul" [YulExpr.ident "denominator", YulExpr.ident "inverse"]
      ]
    ]),
    YulStmt.assign "inverse" (YulExpr.call "mul" [
      YulExpr.ident "inverse",
      YulExpr.call "sub" [
        YulExpr.lit 2,
        YulExpr.call "mul" [YulExpr.ident "denominator", YulExpr.ident "inverse"]
      ]
    ]),
    YulStmt.assign "inverse" (YulExpr.call "mul" [
      YulExpr.ident "inverse",
      YulExpr.call "sub" [
        YulExpr.lit 2,
        YulExpr.call "mul" [YulExpr.ident "denominator", YulExpr.ident "inverse"]
      ]
    ]),
    YulStmt.assign "inverse" (YulExpr.call "mul" [
      YulExpr.ident "inverse",
      YulExpr.call "sub" [
        YulExpr.lit 2,
        YulExpr.call "mul" [YulExpr.ident "denominator", YulExpr.ident "inverse"]
      ]
    ]),
    YulStmt.assign "inverse" (YulExpr.call "mul" [
      YulExpr.ident "inverse",
      YulExpr.call "sub" [
        YulExpr.lit 2,
        YulExpr.call "mul" [YulExpr.ident "denominator", YulExpr.ident "inverse"]
      ]
    ]),
    YulStmt.assign "inverse" (YulExpr.call "mul" [
      YulExpr.ident "inverse",
      YulExpr.call "sub" [
        YulExpr.lit 2,
        YulExpr.call "mul" [YulExpr.ident "denominator", YulExpr.ident "inverse"]
      ]
    ]),
    YulStmt.assign "result" (YulExpr.call "mul" [
      YulExpr.ident "prod0", YulExpr.ident "inverse"
    ])
  ]

/-- Round-up variant of `fullMulDiv`: `fullMulDivUp(a, b, c)` returns
    `ceil((a * b) / c)`. Computed as `fullMulDiv(a, b, c) + (remainder > 0)`
    where `remainder = mulmod(a, b, c)`. Reverts on division by zero
    and on quotient overflow.

    Note: when the floor quotient equals `2^256 - 1` and the remainder is
    non-zero, the rounded-up result overflows `uint256` and the add wraps
    to zero. OpenZeppelin's contemporary `Math.mulDiv` accepts that wrap;
    the caller can guard against it explicitly when needed. (verity#1761) -/
def fullMulDivUpHelper : YulStmt :=
  YulStmt.funcDef fullMulDivUpHelperName ["a", "b", "denominator"] ["result"] [
    YulStmt.assign "result" (YulExpr.call fullMulDivHelperName [
      YulExpr.ident "a", YulExpr.ident "b", YulExpr.ident "denominator"
    ]),
    YulStmt.if_ (YulExpr.call "iszero" [
      YulExpr.call "iszero" [
        YulExpr.call "mulmod" [
          YulExpr.ident "a", YulExpr.ident "b", YulExpr.ident "denominator"
        ]
      ]
    ]) [
      YulStmt.assign "result" (YulExpr.call "add" [YulExpr.ident "result", YulExpr.lit 1])
    ]
  ]

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
