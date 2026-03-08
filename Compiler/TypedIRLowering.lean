import Verity.Core.Free.TypedIR
import Compiler.Yul.Ast

namespace Verity.Core.Free
open Compiler.Yul

/-- Deterministic Yul identifier for a typed SSA variable. -/
def tVarName (v : TVar) : String :=
  s!"t{v.id}"

private def boolToWord (b : Bool) : Nat :=
  if b then 1 else 0

/-- Lower typed IR expressions into Yul expressions. -/
def lowerTExpr : {ty : Ty} → TExpr ty → YulExpr
  | _, .var v => .ident (tVarName v)
  | _, .uintLit value => .lit (value : Nat)
  | _, .addressLit value => .lit (value : Nat)
  | _, .boolLit value => .lit (boolToWord value)
  | _, .unitLit => .lit 0
  | _, .add lhs rhs => .call "add" [lowerTExpr lhs, lowerTExpr rhs]
  | _, .sub lhs rhs => .call "sub" [lowerTExpr lhs, lowerTExpr rhs]
  | _, .mul lhs rhs => .call "mul" [lowerTExpr lhs, lowerTExpr rhs]
  | _, .div lhs rhs => .call "div" [lowerTExpr lhs, lowerTExpr rhs]
  | _, .mod lhs rhs => .call "mod" [lowerTExpr lhs, lowerTExpr rhs]
  | _, .eq lhs rhs => .call "eq" [lowerTExpr lhs, lowerTExpr rhs]
  | _, .lt lhs rhs => .call "lt" [lowerTExpr lhs, lowerTExpr rhs]
  | _, .and lhs rhs => .call "and" [lowerTExpr lhs, lowerTExpr rhs]
  | _, .or lhs rhs => .call "or" [lowerTExpr lhs, lowerTExpr rhs]
  | _, .not value => .call "iszero" [lowerTExpr value]
  | _, .ite cond thenExpr elseExpr =>
      -- Yul has no expression-level if-else, so encode branchlessly.
      .call "add"
        [ .call "mul" [lowerTExpr cond, lowerTExpr thenExpr]
        , .call "mul" [.call "iszero" [lowerTExpr cond], lowerTExpr elseExpr]
        ]
  | _, .sender => .call "caller" []
  | _, .this => .call "address" []
  | _, .msgValue => .call "callvalue" []
  | _, .blockTimestamp => .call "timestamp" []
  | _, .blockNumber => .call "number" []
  | _, .getStorage slot => .call "sload" [.lit slot]
  | _, .getStorageAddr slot => .call "sload" [.lit slot]
  | _, .getMapping slot key =>
      .call "sload" [.call "mappingSlot" [.lit slot, lowerTExpr key]]
  | _, .getMapping2 slot key1 key2 =>
      let innerSlot := .call "mappingSlot" [.lit slot, lowerTExpr key1]
      .call "sload" [.call "mappingSlot" [innerSlot, lowerTExpr key2]]
  | _, .getMappingUint slot key =>
      .call "sload" [.call "mappingSlot" [.lit slot, lowerTExpr key]]
  | _, .addrToUint value => lowerTExpr value

/-- Lower a list of typed IR statements into Yul statements. -/
def lowerTStmts : List TStmt → List YulStmt
  | [] => []
  | stmt :: rest => lowerTStmt stmt ++ lowerTStmts rest
where
  lowerTStmt : TStmt → List YulStmt
    | .let_ dst rhs => [.let_ (tVarName dst) (lowerTExpr rhs)]
    | .assign dst rhs => [.assign (tVarName dst) (lowerTExpr rhs)]
    | .setStorage slot value => [.expr (.call "sstore" [.lit slot, lowerTExpr value])]
    | .setStorageAddr slot value => [.expr (.call "sstore" [.lit slot, lowerTExpr value])]
    | .setMapping slot key value =>
        [ .expr (.call "sstore"
            [.call "mappingSlot" [.lit slot, lowerTExpr key], lowerTExpr value])
        ]
    | .setMapping2 slot key1 key2 value =>
        let innerSlot := .call "mappingSlot" [.lit slot, lowerTExpr key1]
        [ .expr (.call "sstore"
            [.call "mappingSlot" [innerSlot, lowerTExpr key2], lowerTExpr value])
        ]
    | .setMappingUint slot key value =>
        [ .expr (.call "sstore"
            [.call "mappingSlot" [.lit slot, lowerTExpr key], lowerTExpr value])
        ]
    | .if_ cond thenBranch elseBranch =>
        -- Use switch to evaluate the condition exactly once.  The previous
        -- two-if pattern re-evaluated `cond` after the then-branch, which
        -- could observe state mutations (e.g. sstore) and incorrectly
        -- fall into the else-branch.
        [ .switch (lowerTExpr cond)
            [(1, lowerTStmts thenBranch)]
            (some (lowerTStmts elseBranch))
        ]
    | .stop => [.expr (.call "stop" [])]
    | .returnUint value =>
        [ .expr (.call "mstore" [.lit 0, lowerTExpr value])
        , .expr (.call "return" [.lit 0, .lit 32])
        ]
    | .returnAddr value =>
        [ .expr (.call "mstore" [.lit 0, lowerTExpr value])
        , .expr (.call "return" [.lit 0, .lit 32])
        ]
    | .expr value => [.expr (lowerTExpr value)]
    | .emit eventName topics =>
        [ .expr (.call s!"log{topics.length + 1}"
            ([.lit 0, .lit 0, .lit (typedEventNameTopicWord eventName)] ++ topics.map lowerTExpr))
        ]
    | .rawLog topics dataOffset dataSize =>
        [ .expr (.call s!"log{topics.length}" ([lowerTExpr dataOffset, lowerTExpr dataSize] ++ topics.map lowerTExpr))
        ]
    | .revert _reason => [.expr (.call "revert" [.lit 0, .lit 0])]

/-- Lower a typed IR block into Yul statements for the existing IR/Yul backend. -/
def lowerTBlock (block : TBlock) : List YulStmt :=
  lowerTStmts block.body

end Verity.Core.Free
