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

/-! ## Circuit-Compatible Output

The Circom circuit commits to `Poseidon(templateId, holeValues...)`.
`evalIntentCircuitOutput` computes the same `(templateId, holeValues)`
using the reference evaluator so we can cross-check agreement.

Template indices are assigned sequentially (0, 1, 2, ...) in the order
emit statements appear in the program AST — the same order the Circom
compiler uses. The active emit's index becomes the `templateId`.

Hole values for the circuit commitment are the **union** of all hole
signals across all emit paths (deduplicated, in order), matching the
Circom generator's `allHoleSignals` computation.
-/

open Compiler.CompilationModel (ParamType)

/-- Split a uint256 Value into (lo, hi) 128-bit limbs as Nat. -/
def splitUint256Value (v : Value) : Option (Nat × Nat) :=
  match v with
  | .int n =>
    let mask128 : Nat := (2 ^ 128) - 1
    let nn : Nat := if n < 0 then ((2 ^ 256 : Nat) - n.natAbs) else n.natAbs
    some (nn &&& mask128, (nn >>> 128) &&& mask128)
  | _ => none

/-- Get the circuit signal values for a parameter, splitting uint256 into lo/hi.
    Returns the values as a list of Nats (field elements). -/
def paramCircuitValues (env : Env) (paramName : String) (ty : ParamType) : Option (List Nat) :=
  match env.lookup paramName with
  | none => none
  | some v =>
    match ty with
    | .uint256 | .int256 =>
      match splitUint256Value v with
      | some (lo, hi) => some [lo, hi]
      | none => none
    | .address =>
      match v with
      | .addr a =>
        -- Parse hex address to Nat
        let stripped := if a.startsWith "0x" then a.drop 2 else a
        some [stripped.foldl (fun acc c =>
          acc * 16 + (if c.isDigit then c.toNat - '0'.toNat
                      else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
                      else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
                      else 0)) 0]
      | .int n => some [n.natAbs]
      | _ => none
    | .bool =>
      match v with
      | .bool b => some [if b then 1 else 0]
      | .int n => some [if n != 0 then 1 else 0]
      | _ => none
    | _ =>
      match v with
      | .int n => some [n.natAbs]
      | _ => none

/-- Dedup preserving first-occurrence order (same as Circom.dedup). -/
private def dedup : List String → List String
  | [] => []
  | x :: xs => if xs.contains x then dedup xs else x :: dedup xs

/-- Circuit output: the values that the Circom circuit commits to. -/
structure CircuitOutput where
  /-- The numeric template index (0-based, sequential per emit). -/
  templateIdx : Nat
  /-- The hole values as field elements (Nats), in the same order
      as the Circom output commitment: Poseidon(templateIdx, vals...). -/
  holeValues : List Nat
  deriving Repr

mutual

/-- Count total emit paths in an expression (for void function calls).
    Same traversal as Circom's compileStmts — needed for index agreement. -/
def countEmitsExpr (fns : List FnDecl) (consts : List ConstDef)
    (fuel : Nat) (expr : Expr) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    match expr with
    | .call fnName _args =>
      match findFn fns fnName with
      | some fn =>
        match fn.returnKind with
        | .void => countEmitsStmts fns consts fuel' fn.body
        | _ => 0
      | none => 0
    | _ => 0

/-- Count total emit paths in a statement list (same traversal as Circom's compileStmts).
    Counts ALL paths, not just the one taken — needed for consistent index assignment. -/
def countEmitsStmts (fns : List FnDecl) (consts : List ConstDef)
    (fuel : Nat) : List Stmt → Nat
  | [] => 0
  | stmts =>
    match fuel with
    | 0 => 0
    | fuel' + 1 =>
      match stmts with
      | [] => 0
      | .emit _ :: rest => 1 + countEmitsStmts fns consts fuel' rest
      | .ite _cond thenBr elseBr :: rest =>
        countEmitsStmts fns consts fuel' thenBr +
        countEmitsStmts fns consts fuel' elseBr +
        countEmitsStmts fns consts fuel' rest
      | .call fnName _args :: rest =>
        match findFn fns fnName with
        | some fn =>
          countEmitsStmts fns consts fuel' fn.body +
          countEmitsStmts fns consts fuel' rest
        | none => countEmitsStmts fns consts fuel' rest

end

/-- Evaluate an intent and return the circuit-compatible output.
    This computes the same `(templateId, holeValues)` that the Circom
    circuit commits to via Poseidon, enabling cross-validation.

    The template index is assigned by walking the AST in the same order
    as the Circom compiler, counting all emit paths (not just taken ones). -/
def evalIntentCircuitOutput (spec : IntentSpec) (binding : IntentBinding)
    (params : List (String × Value)) (fuel : Nat := defaultFuel)
    : Option CircuitOutput := do
  let fn ← findFn spec.fns binding.intentFn
  if fn.params.length != params.length then none
  else
    let env : Env := params
    let templates ← evalStmts spec.fns spec.constants env fuel fn.body
    -- We need exactly one emitted template for circuit output
    match templates with
    | [tmpl] =>
      -- Compute template index: walk the AST counting emit positions,
      -- find which one matches the emitted template
      let templateIdx ← findEmitIndex spec fn env fuel fn.body tmpl 0
      -- Collect all hole params across ALL possible emit paths (not just the active one)
      -- by walking the AST structure. This matches Circom's allHoleSignals.
      let allHoleParams := collectAllHoleParamsFromAST fn.body fn.params
      -- Resolve hole values from the environment
      let holeValues ← resolveHoleValuesForCircuit env allHoleParams
      some { templateIdx, holeValues }
    | _ => none  -- Multi-emit not yet supported for circuit output
where
  /-- Walk the AST to find which emit index the given template corresponds to.
      Returns the 0-based index matching Circom's sequential assignment. -/
  findEmitIndex (spec : IntentSpec) (fn : FnDecl) (env : Env) (fuel : Nat)
      (stmts : List Stmt) (target : EmittedTemplate) (startIdx : Nat)
      : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match stmts with
      | [] => none
      | .emit tmpl :: rest =>
        -- Check if this emit matches the target
        match resolveHoles env tmpl.holes with
        | some resolvedHoles =>
          if tmpl.text == target.text && resolvedHoles.length == target.holes.length then
            some startIdx
          else
            findEmitIndex spec fn env fuel' rest target (startIdx + 1)
        | none => findEmitIndex spec fn env fuel' rest target (startIdx + 1)
      | .ite cond thenBranch elseBranch :: rest =>
        let thenCount := countEmitsStmts spec.fns spec.constants fuel' thenBranch
        let elseCount := countEmitsStmts spec.fns spec.constants fuel' elseBranch
        match evalExpr spec.fns spec.constants env fuel' cond with
        | some (.bool true) =>
          match findEmitIndex spec fn env fuel' thenBranch target startIdx with
          | some idx => some idx
          | none => findEmitIndex spec fn env fuel' rest target (startIdx + thenCount + elseCount)
        | some (.bool false) =>
          match findEmitIndex spec fn env fuel' elseBranch target (startIdx + thenCount) with
          | some idx => some idx
          | none => findEmitIndex spec fn env fuel' rest target (startIdx + thenCount + elseCount)
        | _ => none
      | .call fnName args :: rest =>
        match findFn spec.fns fnName with
        | some calledFn =>
          let argVals := evalExprList spec.fns spec.constants env fuel' args
          match argVals with
          | some vals =>
            let callEnv := List.zipWith (fun (name, _) val => (name, val)) calledFn.params vals
            let callCount := countEmitsStmts spec.fns spec.constants fuel' calledFn.body
            match findEmitIndex spec calledFn callEnv fuel' calledFn.body target startIdx with
            | some idx => some idx
            | none => findEmitIndex spec fn env fuel' rest target (startIdx + callCount)
          | none => none
        | none => findEmitIndex spec fn env fuel' rest target startIdx

  /-- Collect all hole param names from the AST across ALL emit paths
      (matching Circom's allHoleSignals = dedup(paths.flatMap(_.holeSignals))). -/
  collectAllHoleParamsFromAST (stmts : List Stmt) (fnParams : List (String × ParamType))
      : List (String × ParamType) :=
    let allNames := dedup (collectHoleNamesFromStmts stmts)
    allNames.filterMap fun name =>
      match fnParams.find? (fun (n, _) => n == name) with
      | some (_, ty) => some (name, ty)
      | none => none

  /-- Recursively collect hole parameter names from all emit statements. -/
  collectHoleNamesFromStmts : List Stmt → List String
    | [] => []
    | .emit tmpl :: rest =>
      tmpl.holes.map (·.param) ++ collectHoleNamesFromStmts rest
    | .ite _ thenBr elseBr :: rest =>
      collectHoleNamesFromStmts thenBr ++
      collectHoleNamesFromStmts elseBr ++
      collectHoleNamesFromStmts rest
    | .call _ _ :: rest =>
      -- For simplicity, skip inlined call bodies in hole collection.
      -- The top-level function's direct body covers the ERC-20 case.
      collectHoleNamesFromStmts rest

  /-- Resolve hole values from the environment to field elements. -/
  resolveHoleValuesForCircuit (env : Env) (holeParams : List (String × ParamType))
      : Option (List Nat) :=
    match holeParams with
    | [] => some []
    | (name, ty) :: rest => do
      let vals ← paramCircuitValues env name ty
      let moreVals ← resolveHoleValuesForCircuit env rest
      some (vals ++ moreVals)

end Verity.Intent
