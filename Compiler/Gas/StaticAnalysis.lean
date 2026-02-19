import Compiler.Yul.Ast

namespace Compiler.Gas

open Compiler.Yul

/-- Configuration knobs for static upper-bound estimation. -/
structure GasConfig where
  /-- Upper bound for loop trip counts in `for` blocks. -/
  loopIterations : Nat := 8
  /-- Conservative fallback for unknown builtins. -/
  unknownCallCost : Nat := 50000
  deriving Repr

/-- Base cost model for a single builtin call, excluding argument evaluation. -/
def builtinBaseCost (cfg : GasConfig) (name : String) : Nat :=
  if name = "sstore" then 22100
  else if name = "sload" then 2100
  else if name = "keccak256" then 60
  else if name = "log0" then 375
  else if name = "log1" then 750
  else if name = "log2" then 1125
  else if name = "log3" then 1500
  else if name = "log4" then 1875
  /- Worst-case call upper bound:
     base call + cold account access + nonzero value transfer + new-account creation. -/
  else if name = "call" then 36700
  /- Delegate/static calls cannot transfer value but still pay base + cold access in worst case. -/
  else if name = "delegatecall" then 2700
  else if name = "staticcall" then 2700
  /- Creation costs are highly context dependent (initcode + memory expansion); use conservative fallback. -/
  else if name = "create" then cfg.unknownCallCost
  else if name = "create2" then cfg.unknownCallCost
  else if name = "selfdestruct" then 5000
  else if name = "return" then 0
  else if name = "revert" then 0
  else if name = "stop" then 0
  else if name = "pop" then 2
  else if name = "mstore" then 3
  else if name = "mload" then 3
  else if name = "calldataload" then 3
  else if name = "calldatasize" then 2
  else if name = "callvalue" then 2
  else if name = "caller" then 2
  else if name = "codesize" then 2
  /- Copy costs depend on payload length and memory expansion.
     Use conservative constants to avoid unknown-call fallback explosions. -/
  else if name = "codecopy" then 5000
  else if name = "datacopy" then 5000
  /- `dataoffset`/`datasize` compile to immediate constants; model as verylow. -/
  else if name = "dataoffset" then 3
  else if name = "datasize" then 3
  else if name = "mappingSlot" then 42
  else if name = "add" then 3
  else if name = "sub" then 3
  else if name = "mul" then 5
  else if name = "div" then 5
  else if name = "mod" then 5
  else if name = "eq" then 3
  else if name = "lt" then 3
  else if name = "gt" then 3
  else if name = "iszero" then 3
  else if name = "and" then 3
  else if name = "or" then 3
  else if name = "xor" then 3
  else if name = "not" then 3
  else if name = "shl" then 3
  else if name = "shr" then 3
  else cfg.unknownCallCost

mutual

/-- Upper bound for evaluating a Yul expression. -/
def exprUpperBound (cfg : GasConfig) : YulExpr → Nat
  | .lit _ => 0
  | .hex _ => 0
  | .str _ => 0
  | .ident _ => 0
  | .call name args =>
      argsUpperBound cfg args + builtinBaseCost cfg name

/-- Upper bound for evaluating a list of Yul expressions. -/
def argsUpperBound (cfg : GasConfig) : List YulExpr → Nat
  | [] => 0
  | arg :: rest => exprUpperBound cfg arg + argsUpperBound cfg rest

end

mutual

/-- Upper bound over switch cases using explicit fuel for totality. -/
def casesUpperBoundFuel (cfg : GasConfig) : Nat → List (Nat × List YulStmt) → Nat
  | 0, _ => 0
  | _, [] => 0
  | fuel + 1, (_, body) :: rest =>
      Nat.max (stmtsUpperBoundFuel cfg fuel body) (casesUpperBoundFuel cfg fuel rest)

/-- Upper bound for a single Yul statement using explicit fuel for totality. -/
def stmtUpperBoundFuel (cfg : GasConfig) : Nat → YulStmt → Nat
  | 0, _ => 0
  | _ + 1, .comment _ => 0
  | _ + 1, .let_ _ value => exprUpperBound cfg value
  | _ + 1, .assign _ value => exprUpperBound cfg value
  | _ + 1, .expr e => exprUpperBound cfg e
  | fuel + 1, .if_ cond body => exprUpperBound cfg cond + stmtsUpperBoundFuel cfg fuel body
  | fuel + 1, .for_ init cond post body =>
      let initCost := stmtsUpperBoundFuel cfg fuel init
      let loopBodyCost := exprUpperBound cfg cond + stmtsUpperBoundFuel cfg fuel body + stmtsUpperBoundFuel cfg fuel post
      let exitCheckCost := exprUpperBound cfg cond
      initCost + cfg.loopIterations * loopBodyCost + exitCheckCost
  | fuel + 1, .switch expr cases defaultCase =>
      let exprCost := exprUpperBound cfg expr
      let defaultCost := match defaultCase with
        | some body => stmtsUpperBoundFuel cfg fuel body
        | none => 0
      exprCost + Nat.max defaultCost (casesUpperBoundFuel cfg fuel cases)
  | fuel + 1, .block body => stmtsUpperBoundFuel cfg fuel body
  | fuel + 1, .funcDef _ _ _ body => stmtsUpperBoundFuel cfg fuel body

/-- Upper bound for a sequence of Yul statements using explicit fuel. -/
def stmtsUpperBoundFuel (cfg : GasConfig) : Nat → List YulStmt → Nat
  | 0, _ => 0
  | _, [] => 0
  | fuel + 1, stmt :: rest =>
      stmtUpperBoundFuel cfg fuel stmt + stmtsUpperBoundFuel cfg fuel rest

end

/-- Upper bound over switch cases. -/
def casesUpperBound (cfg : GasConfig) (fuel : Nat) (cases : List (Nat × List YulStmt)) : Nat :=
  casesUpperBoundFuel cfg fuel cases

/-- Upper bound for a single Yul statement. -/
def stmtUpperBound (cfg : GasConfig) (fuel : Nat) (stmt : YulStmt) : Nat :=
  stmtUpperBoundFuel cfg fuel stmt

/-- Upper bound for a sequence of Yul statements. -/
def stmtsUpperBound (cfg : GasConfig) (fuel : Nat) (stmts : List YulStmt) : Nat :=
  stmtsUpperBoundFuel cfg fuel stmts

/-- Default static gas upper bound used for quick checks. -/
def gasUpperBound (stmts : List YulStmt) : Nat :=
  stmtsUpperBound {} 4096 stmts

/-! ## Sanity checks -/

def simpleStoreProgram : List YulStmt :=
  [
    .expr (.call "sstore" [.lit 0, .lit 777]),
    .expr (.call "stop" [])
  ]

def boundedLoopProgram : List YulStmt :=
  [
    .for_
      [.let_ "i" (.lit 0)]
      (.call "lt" [.ident "i", .lit 3])
      [.assign "i" (.call "add" [.ident "i", .lit 1])]
      [
        .expr (.call "sload" [.lit 0]),
        .expr (.call "mstore" [.lit 0, .lit 1])
      ]
  ]

def externalCallProgram : List YulStmt :=
  [
    .expr (.call "call" [.lit 50000, .lit 1, .lit 1, .lit 0, .lit 0, .lit 0, .lit 0]),
    .expr (.call "stop" [])
  ]

example : gasUpperBound simpleStoreProgram = 22100 := rfl

example : stmtsUpperBound { loopIterations := 3 } 64 boundedLoopProgram = 6330 := rfl

example : gasUpperBound externalCallProgram = 36700 := rfl

end Compiler.Gas
