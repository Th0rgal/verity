import Compiler.Yul.PatchRulesCatalog.SolcCompat.Common

namespace Compiler.Yul

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

partial def rewriteCurrentNonceIncrementStmts
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

partial def rewriteElapsedCheckedSubStmts
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

partial def rewriteAccrueInterestPrologueTempsStmts
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

partial def rewriteAccrueInterestIrmGuardStmts
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

partial def rewriteAccrueInterestCheckedArithmeticStmts
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
