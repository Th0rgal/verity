/-
  Verity.Intent.Eval: Reference evaluator for the intent DSL.

  This is the canonical semantics. Given an IntentSpec and parameter values,
  it evaluates an intent function and produces a list of emitted templates.

  Totality: structural recursion on a `fuel : Nat` parameter.
  Every recursive call passes strictly less fuel.
  Default fuel is generous (1024) so real programs never exhaust it.
-/
import Verity.Intent.Types

namespace Verity.Intent

/-! ## Value Domain -/

/-- Runtime values in the intent DSL. -/
inductive Value where
  | int (n : Int)
  | str (s : String)
  | bool (b : Bool)
  | addr (a : String)
  deriving Repr, BEq

/-! ## Evaluation Output -/

/-- A resolved hole: parameter name, format directive, and the actual value. -/
structure ResolvedHole where
  param : String
  format : Format
  value : Value
  deriving Repr

/-- An emitted template with all holes resolved to concrete values. -/
structure EmittedTemplate where
  text : String
  holes : List ResolvedHole
  deriving Repr

/-! ## Environment -/

/-- Evaluation environment: maps names to values. -/
abbrev Env := List (String × Value)

/-- Look up a name in the environment. -/
def Env.lookup (env : Env) (name : String) : Option Value :=
  match env with
  | [] => none
  | (k, v) :: rest => if k == name then some v else Env.lookup rest name

/-- Look up a function declaration by name. -/
def findFn (fns : List FnDecl) (name : String) : Option FnDecl :=
  match fns with
  | [] => none
  | f :: rest => if f.name == name then some f else findFn rest name

/-- Look up a constant by name, returning its expression. -/
def findConstExpr (consts : List ConstDef) (name : String) : Option Expr :=
  match consts with
  | [] => none
  | c :: rest => if c.name == name then some c.value else findConstExpr rest name

/-- Resolve a single hole: look up the parameter value in the environment. -/
def resolveHole (env : Env) (hole : Hole) : Option ResolvedHole := do
  let value ← env.lookup hole.param
  some { param := hole.param, format := hole.format, value }

/-- Resolve all holes in a template. -/
def resolveHoles (env : Env) : List Hole → Option (List ResolvedHole)
  | [] => some []
  | h :: hs => do
    let rh ← resolveHole env h
    let rhs ← resolveHoles env hs
    some (rh :: rhs)

/-! ## Combined Evaluator

Expression and statement evaluation in a single mutual block,
all structurally recursive on `fuel`.
-/

mutual

/-- Evaluate an expression. Structurally recursive on `fuel`. -/
def evalExpr (fns : List FnDecl) (consts : List ConstDef) (env : Env)
    (fuel : Nat) (expr : Expr) : Option Value :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match expr with
    | Expr.intLit n => some (.int n)
    | Expr.strLit s => some (.str s)
    | Expr.param name =>
      match env.lookup name with
      | some v => some v
      | none =>
        match findConstExpr consts name with
        | some cexpr => evalExpr fns consts env fuel' cexpr
        | none => none
    | Expr.eq a b => do
      let va ← evalExpr fns consts env fuel' a
      let vb ← evalExpr fns consts env fuel' b
      some (.bool (va == vb))
    | Expr.ne a b => do
      let va ← evalExpr fns consts env fuel' a
      let vb ← evalExpr fns consts env fuel' b
      some (.bool (va != vb))
    | Expr.lt a b => do
      let va ← evalExpr fns consts env fuel' a
      let vb ← evalExpr fns consts env fuel' b
      match va, vb with
      | .int x, .int y => some (.bool (x < y))
      | _, _ => none
    | Expr.gt a b => do
      let va ← evalExpr fns consts env fuel' a
      let vb ← evalExpr fns consts env fuel' b
      match va, vb with
      | .int x, .int y => some (.bool (x > y))
      | _, _ => none
    | Expr.le a b => do
      let va ← evalExpr fns consts env fuel' a
      let vb ← evalExpr fns consts env fuel' b
      match va, vb with
      | .int x, .int y => some (.bool (x ≤ y))
      | _, _ => none
    | Expr.ge a b => do
      let va ← evalExpr fns consts env fuel' a
      let vb ← evalExpr fns consts env fuel' b
      match va, vb with
      | .int x, .int y => some (.bool (x ≥ y))
      | _, _ => none
    | Expr.and a b => do
      let va ← evalExpr fns consts env fuel' a
      let vb ← evalExpr fns consts env fuel' b
      match va, vb with
      | .bool x, .bool y => some (.bool (x && y))
      | _, _ => none
    | Expr.or a b => do
      let va ← evalExpr fns consts env fuel' a
      let vb ← evalExpr fns consts env fuel' b
      match va, vb with
      | .bool x, .bool y => some (.bool (x || y))
      | _, _ => none
    | Expr.not a => do
      let va ← evalExpr fns consts env fuel' a
      match va with
      | .bool x => some (.bool (!x))
      | _ => none
    | Expr.call fnName args => do
      let fn ← findFn fns fnName
      let argVals ← evalExprList fns consts env fuel' args
      if fn.params.length != argVals.length then none
      else
        let callEnv : Env :=
          List.zipWith (fun (name, _) val => (name, val)) fn.params argVals
        match fn.returnKind with
        | .bool | .string =>
          match fn.expr with
          | some body => evalExpr fns consts callEnv fuel' body
          | none => none
        | .void => none

/-- Evaluate a list of expressions. Structurally recursive on `fuel`. -/
def evalExprList (fns : List FnDecl) (consts : List ConstDef) (env : Env)
    (fuel : Nat) : List Expr → Option (List Value)
  | [] => some []
  | e :: es => do
    let v ← evalExpr fns consts env fuel e
    let vs ← evalExprList fns consts env fuel es
    some (v :: vs)

/-- Evaluate a list of statements, collecting emitted templates.
    Structurally recursive on `fuel`. -/
def evalStmts (fns : List FnDecl) (consts : List ConstDef) (env : Env)
    (fuel : Nat) : List Stmt → Option (List EmittedTemplate)
  | [] => some []
  | stmts =>
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match stmts with
      | [] => some []  -- unreachable, but helps the termination checker
      | Stmt.emit tmpl :: rest => do
        let holes ← resolveHoles env tmpl.holes
        let et : EmittedTemplate := { text := tmpl.text, holes }
        let more ← evalStmts fns consts env fuel' rest
        some (et :: more)
      | Stmt.ite cond thenBranch elseBranch :: rest => do
        let cv ← evalExpr fns consts env fuel' cond
        match cv with
        | .bool true => do
          let thenResults ← evalStmts fns consts env fuel' thenBranch
          let more ← evalStmts fns consts env fuel' rest
          some (thenResults ++ more)
        | .bool false => do
          let elseResults ← evalStmts fns consts env fuel' elseBranch
          let more ← evalStmts fns consts env fuel' rest
          some (elseResults ++ more)
        | _ => none
      | Stmt.call fnName args :: rest => do
        let fn ← findFn fns fnName
        let argVals ← evalExprList fns consts env fuel' args
        if fn.params.length != argVals.length then none
        else
          let callEnv : Env :=
            List.zipWith (fun (name, _) val => (name, val)) fn.params argVals
          match fn.returnKind with
          | .void =>
            let callResults ← evalStmts fns consts callEnv fuel' fn.body
            let more ← evalStmts fns consts env fuel' rest
            some (callResults ++ more)
          | _ => none

end

/-! ## Top-Level Entry Point -/

/-- Default fuel for evaluation. -/
def defaultFuel : Nat := 1024

/-- Evaluate an intent binding against concrete parameter values.
    Returns the list of emitted templates, or `none` on error. -/
def evalIntent (spec : IntentSpec) (binding : IntentBinding)
    (params : List (String × Value)) (fuel : Nat := defaultFuel)
    : Option (List EmittedTemplate) := do
  let fn ← findFn spec.fns binding.intentFn
  if fn.params.length != params.length then none
  else
    let env : Env := params
    evalStmts spec.fns spec.constants env fuel fn.body

end Verity.Intent
