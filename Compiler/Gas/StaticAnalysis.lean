import Compiler.Yul.Ast

namespace Compiler.Gas

open Compiler.Yul

/-- Configuration knobs for static upper-bound estimation. -/
structure GasConfig where
  /-- Upper bound for loop trip counts in `for` blocks. -/
  loopIterations : Nat := 8
  /-- Conservative fallback for unknown builtins. -/
  unknownCallCost : Nat := 50000
  /-- Conservative fallback for unknown forwarded gas in CALL-like builtins. -/
  unknownForwardedGas : Nat := 50000
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
  else if name = "callcode" then 36700
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

/-- Extra cost for CALL-like opcodes from forwarded gas argument. -/
def forwardedGasCost (cfg : GasConfig) (name : String) (args : List YulExpr) : Nat :=
  if name = "call" || name = "callcode" || name = "delegatecall" || name = "staticcall" then
    match args.head? with
    | some (.lit n) => n
    | some (.hex n) => n
    | _ => cfg.unknownForwardedGas
  else
    0

abbrev FunctionEnv := List (String × List YulStmt)

/-- Collect user-defined function bodies from a Yul statement tree. -/
def collectFunctionDefs : List YulStmt → FunctionEnv
  | [] => []
  | .funcDef name _ _ body :: rest => (name, body) :: collectFunctionDefs rest
  | _ :: rest => collectFunctionDefs rest

/-- Return all matching user-defined function bodies for a call name. -/
def lookupFunctionBodies (env : FunctionEnv) (name : String) : List (List YulStmt) :=
  env.foldr (fun (entry : String × List YulStmt) acc =>
    if entry.fst = name then entry.snd :: acc else acc) []

mutual

/-- Upper bound for evaluating a Yul expression. -/
def exprUpperBoundFuel (cfg : GasConfig) (env : FunctionEnv) : Nat → YulExpr → Nat
  | 0, _ => 0
  | _ + 1, .lit _ => 0
  | _ + 1, .hex _ => 0
  | _ + 1, .str _ => 0
  | _ + 1, .ident _ => 0
  | fuel + 1, .call name args =>
      let argCost := argsUpperBoundFuel cfg env fuel args
      let fnBodies := lookupFunctionBodies env name
      if fnBodies.isEmpty then
        argCost + builtinBaseCost cfg name + forwardedGasCost cfg name args
      else
        argCost + maxFunctionCallCostFuel cfg env fuel fnBodies

/-- Upper bound for evaluating a list of Yul expressions. -/
def argsUpperBoundFuel (cfg : GasConfig) (env : FunctionEnv) : Nat → List YulExpr → Nat
  | 0, _ => 0
  | _, [] => 0
  | fuel + 1, arg :: rest => exprUpperBoundFuel cfg env fuel arg + argsUpperBoundFuel cfg env fuel rest

/-- Maximum user-defined function-call cost among matching function bodies. -/
def maxFunctionCallCostFuel (cfg : GasConfig) (env : FunctionEnv) : Nat → List (List YulStmt) → Nat
  | 0, _ => 0
  | _, [] => 0
  | fuel + 1, body :: rest =>
      Nat.max (stmtsUpperBoundFuel cfg env fuel body) (maxFunctionCallCostFuel cfg env fuel rest)

/-- Upper bound over switch cases using explicit fuel for totality. -/
def casesUpperBoundFuel (cfg : GasConfig) (env : FunctionEnv) : Nat → List (Nat × List YulStmt) → Nat
  | 0, _ => 0
  | _, [] => 0
  | fuel + 1, (_, body) :: rest =>
      Nat.max (stmtsUpperBoundFuel cfg env fuel body) (casesUpperBoundFuel cfg env fuel rest)

/-- Upper bound for a single Yul statement using explicit fuel for totality. -/
def stmtUpperBoundFuel (cfg : GasConfig) (env : FunctionEnv) : Nat → YulStmt → Nat
  | 0, _ => 0
  | _ + 1, .comment _ => 0
  | fuel + 1, .let_ _ value => exprUpperBoundFuel cfg env fuel value
  | fuel + 1, .assign _ value => exprUpperBoundFuel cfg env fuel value
  | fuel + 1, .expr e => exprUpperBoundFuel cfg env fuel e
  | fuel + 1, .if_ cond body => exprUpperBoundFuel cfg env fuel cond + stmtsUpperBoundFuel cfg env fuel body
  | fuel + 1, .for_ init cond post body =>
      let initCost := stmtsUpperBoundFuel cfg env fuel init
      let loopBodyCost := exprUpperBoundFuel cfg env fuel cond + stmtsUpperBoundFuel cfg env fuel body + stmtsUpperBoundFuel cfg env fuel post
      let exitCheckCost := exprUpperBoundFuel cfg env fuel cond
      initCost + cfg.loopIterations * loopBodyCost + exitCheckCost
  | fuel + 1, .switch expr cases defaultCase =>
      let exprCost := exprUpperBoundFuel cfg env fuel expr
      let defaultCost := match defaultCase with
        | some body => stmtsUpperBoundFuel cfg env fuel body
        | none => 0
      exprCost + Nat.max defaultCost (casesUpperBoundFuel cfg env fuel cases)
  | fuel + 1, .block body => stmtsUpperBoundFuel cfg env fuel body
  /- Function declarations do not execute at declaration site; they are accounted on call sites. -/
  | _ + 1, .funcDef _ _ _ _ => 0

/-- Upper bound for a sequence of Yul statements using explicit fuel. -/
def stmtsUpperBoundFuel (cfg : GasConfig) (env : FunctionEnv) : Nat → List YulStmt → Nat
  | 0, _ => 0
  | _, [] => 0
  | fuel + 1, stmt :: rest =>
      stmtUpperBoundFuel cfg env fuel stmt + stmtsUpperBoundFuel cfg env fuel rest

end

/-- Upper bound over switch cases. -/
def casesUpperBound (cfg : GasConfig) (fuel : Nat) (cases : List (Nat × List YulStmt)) : Nat :=
  casesUpperBoundFuel cfg [] fuel cases

/-- Upper bound for a single Yul statement. -/
def stmtUpperBound (cfg : GasConfig) (fuel : Nat) (stmt : YulStmt) : Nat :=
  stmtUpperBoundFuel cfg [] fuel stmt

/-- Upper bound for a sequence of Yul statements. -/
def stmtsUpperBound (cfg : GasConfig) (fuel : Nat) (stmts : List YulStmt) : Nat :=
  let env := collectFunctionDefs stmts
  stmtsUpperBoundFuel cfg env fuel stmts

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

def functionDeclAndCallProgram : List YulStmt :=
  [
    .funcDef "store" ["x"] [] [
      .expr (.call "sstore" [.lit 0, .ident "x"])
    ],
    .expr (.call "store" [.lit 777]),
    .expr (.call "stop" [])
  ]

example : gasUpperBound simpleStoreProgram = 22100 := rfl

example : stmtsUpperBound { loopIterations := 3 } 64 boundedLoopProgram = 6330 := rfl

example : gasUpperBound externalCallProgram = 86700 := rfl

example : gasUpperBound functionDeclAndCallProgram = 22100 := rfl

end Compiler.Gas
