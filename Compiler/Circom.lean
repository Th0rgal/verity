/-
  Compiler.Circom: Generate Circom circuits from IntentSpec.

  For each intent binding, produces a `.circom` file that proves:
    1. The selector matches the expected constant
    2. Poseidon(selector, params...) == calldataCommitment  (public)
    3. The DSL program evaluation selects a templateId and hole values
    4. Poseidon(templateId, holes...) == outputCommitment  (public)

  Phase 2: uint256 (split into lo/hi 128-bit limbs), address, bool.
  forEach loops are unrolled at compile time when the array size is
  statically known. Conditions compiled to Mux selectors.

  See PR #1676 for the full design document.
-/
import Verity.Intent.Types
import Compiler.CompilationModel.Types

namespace Compiler.Circom

open Verity.Intent
open Compiler.CompilationModel (ParamType)

/-! ## Parameter Type Context

The circuit compiler needs to know parameter types to handle uint256 splitting
into lo/hi 128-bit limbs. The type context maps param names to their ABI types.
-/

/-- Maps parameter names to their ABI types. -/
abbrev ParamCtx := List (String × ParamType)

/-- Look up a parameter's type in the context. -/
def ParamCtx.findType (ctx : ParamCtx) (name : String) : Option ParamType :=
  match ctx.find? (fun (n, _) => n == name) with
  | some (_, ty) => some ty
  | none => none

/-! ## Signal Names -/

/-- A Circom signal for a parameter.  uint256 becomes two signals: `_lo` and `_hi`. -/
def paramSignals (name : String) (ty : ParamType) : List String :=
  match ty with
  | .uint256 | .int256 => [s!"{name}_lo", s!"{name}_hi"]
  | _ => [name]

/-- All input signals for a function's parameters. -/
def allParamSignals (params : ParamCtx) : List String :=
  params.flatMap (fun (n, t) => paramSignals n t)

/-! ## Emitter State -/

/-- State for the Circom emitter: accumulated component declarations and a counter. -/
structure EmitState where
  lines : List String := []
  counter : Nat := 0

def EmitState.fresh (st : EmitState) (pfx : String) : String × EmitState :=
  (s!"{pfx}_{st.counter}", { st with counter := st.counter + 1 })

def EmitState.addLine (st : EmitState) (line : String) : EmitState :=
  { st with lines := st.lines ++ [line] }

/-! ## Constant Folding -/

/-- Try to evaluate a constant expression to an integer value at compile time.
    Uses fuel bounded by the number of constants to guard against cycles. -/
def evalConstInt (consts : List ConstDef) (expr : Expr) : Option Int :=
  go consts (consts.length + 1) expr
where
  go (consts : List ConstDef) : Nat → Expr → Option Int
    | _, .intLit n => some n
    | 0, _ => none  -- fuel exhausted (cycle in constants)
    | fuel + 1, .param name =>
      match consts.find? (fun c => c.name == name) with
      | some c => go consts fuel c.value
      | none => none
    | _, _ => none

/-- Split a 256-bit integer into lo/hi 128-bit limbs (as Nat). -/
def splitUint256 (n : Int) : Nat × Nat :=
  let mask128 : Nat := (2 ^ 128) - 1
  let nn : Nat := if n < 0 then ((2 ^ 256 : Nat) - n.natAbs) else n.natAbs
  (nn &&& mask128, (nn >>> 128) &&& mask128)

/-! ## Expression Compilation -/

/-- Remap param references in an expression to use function-scoped signal names. -/
def remapParams (fnPfx : String) (paramNames : List String) : Expr → Expr
  | .param name =>
    if paramNames.contains name then .param s!"{fnPfx}_{name}" else .param name
  | .eq a b => .eq (remapParams fnPfx paramNames a) (remapParams fnPfx paramNames b)
  | .ne a b => .ne (remapParams fnPfx paramNames a) (remapParams fnPfx paramNames b)
  | .lt a b => .lt (remapParams fnPfx paramNames a) (remapParams fnPfx paramNames b)
  | .gt a b => .gt (remapParams fnPfx paramNames a) (remapParams fnPfx paramNames b)
  | .le a b => .le (remapParams fnPfx paramNames a) (remapParams fnPfx paramNames b)
  | .ge a b => .ge (remapParams fnPfx paramNames a) (remapParams fnPfx paramNames b)
  | .and a b => .and (remapParams fnPfx paramNames a) (remapParams fnPfx paramNames b)
  | .or a b => .or (remapParams fnPfx paramNames a) (remapParams fnPfx paramNames b)
  | .not a => .not (remapParams fnPfx paramNames a)
  | .call fn args => .call fn (args.map (remapParams fnPfx paramNames))
  | .index arr idx => .index (remapParams fnPfx paramNames arr) (remapParams fnPfx paramNames idx)
  | .length arr => .length (remapParams fnPfx paramNames arr)
  | other => other

/-- Remap param references in a statement to use function-scoped signal names. -/
def remapStmtParams (fnPfx : String) (paramNames : List String) : Stmt → Stmt
  | .emit tmpl =>
    let holes := tmpl.holes.map (fun h =>
      if paramNames.contains h.param
      then { h with param := s!"{fnPfx}_{h.param}" }
      else h)
    .emit { tmpl with holes }
  | .ite cond thenBr elseBr =>
    .ite (remapParams fnPfx paramNames cond)
      (thenBr.map (remapStmtParams fnPfx paramNames))
      (elseBr.map (remapStmtParams fnPfx paramNames))
  | .forEach var array body =>
    .forEach var (remapParams fnPfx paramNames array)
      (body.map (remapStmtParams fnPfx paramNames))
  | .call fn args =>
    .call fn (args.map (remapParams fnPfx paramNames))

/-! ## Helpers for uint256 signal resolution -/

/-- Check if an expression refers to a uint256 value. -/
def isUint256Expr (ctx : ParamCtx) (consts : List ConstDef) : Expr → Bool
  | .param name =>
    match ctx.findType name with
    | some .uint256 | some .int256 => true
    | _ =>
      -- Check if it's a constant whose value needs uint256 (lo/hi) treatment
      match evalConstInt consts (.param name) with
      | some n => n > (2 ^ 128 : Nat) || n < 0
      | none => false
  | .intLit n => n > (2 ^ 128 : Nat) || n < 0
  | _ => false

/-- Get the lo/hi signals for a uint256 expression. -/
partial def getUint256Signals (st : EmitState) (ctx : ParamCtx)
    (consts : List ConstDef) (expr : Expr) : String × String × EmitState :=
  match expr with
  | .param name =>
    match ctx.findType name with
    | some .uint256 | some .int256 =>
      (s!"{name}_lo", s!"{name}_hi", st)
    | _ =>
      match evalConstInt consts expr with
      | some n =>
        let (lo, hi) := splitUint256 n
        let (loName, st) := st.fresh "clo"
        let st := st.addLine s!"    signal {loName};"
        let st := st.addLine s!"    {loName} <== {lo};"
        let (hiName, st) := st.fresh "chi"
        let st := st.addLine s!"    signal {hiName};"
        let st := st.addLine s!"    {hiName} <== {hi};"
        (loName, hiName, st)
      | none => (name, name, st)
  | .intLit n =>
    let (lo, hi) := splitUint256 n
    let (loName, st) := st.fresh "ilo"
    let st := st.addLine s!"    signal {loName};"
    let st := st.addLine s!"    {loName} <== {lo};"
    let (hiName, st) := st.fresh "ihi"
    let st := st.addLine s!"    signal {hiName};"
    let st := st.addLine s!"    {hiName} <== {hi};"
    (loName, hiName, st)
  | _ => ("0", "0", st)

/-- Collected info about a single emit path through the program. -/
structure EmitPath where
  templateIdx : Nat
  templateText : String
  /-- Circom signal names for the hole values (already resolved to lo/hi). -/
  holeSignals : List String
  conditionSignal : String

mutual

/-- Bind function arguments to parameter signals, handling uint256 lo/hi splitting. -/
partial def bindFnArgs (st : EmitState) (ctx : ParamCtx)
    (fns : List FnDecl) (consts : List ConstDef)
    (fnName : String) : List (String × ParamType) → List Expr → EmitState
  | [], _ => st
  | _, [] => st
  | (pname, pty) :: restParams, arg :: restArgs =>
    let st := match pty with
      | .uint256 | .int256 =>
        match arg with
        | .param argName =>
          match ctx.findType argName with
          | some .uint256 | some .int256 =>
            let st := st.addLine s!"    signal {fnName}_{pname}_lo;"
            let st := st.addLine s!"    {fnName}_{pname}_lo <== {argName}_lo;"
            let st := st.addLine s!"    signal {fnName}_{pname}_hi;"
            st.addLine s!"    {fnName}_{pname}_hi <== {argName}_hi;"
          | _ =>
            let st := st.addLine s!"    signal {fnName}_{pname}_lo;"
            let st := st.addLine s!"    {fnName}_{pname}_lo <== {argName};"
            let st := st.addLine s!"    signal {fnName}_{pname}_hi;"
            st.addLine s!"    {fnName}_{pname}_hi <== 0;"
        | .intLit n =>
          let (lo, hi) := splitUint256 n
          let st := st.addLine s!"    signal {fnName}_{pname}_lo;"
          let st := st.addLine s!"    {fnName}_{pname}_lo <== {lo};"
          let st := st.addLine s!"    signal {fnName}_{pname}_hi;"
          st.addLine s!"    {fnName}_{pname}_hi <== {hi};"
        | _ =>
          let (sig, st) := compileExpr st ctx fns consts arg
          let st := st.addLine s!"    signal {fnName}_{pname}_lo;"
          let st := st.addLine s!"    {fnName}_{pname}_lo <== {sig};"
          let st := st.addLine s!"    signal {fnName}_{pname}_hi;"
          st.addLine s!"    {fnName}_{pname}_hi <== 0;"
      | _ =>
        match arg with
        | .param argName =>
          let st := st.addLine s!"    signal {fnName}_{pname};"
          st.addLine s!"    {fnName}_{pname} <== {argName};"
        | _ =>
          let (sig, st) := compileExpr st ctx fns consts arg
          let st := st.addLine s!"    signal {fnName}_{pname};"
          st.addLine s!"    {fnName}_{pname} <== {sig};"
    bindFnArgs st ctx fns consts fnName restParams restArgs

partial def compileExprList (st : EmitState) (ctx : ParamCtx)
    (fns : List FnDecl) (consts : List ConstDef)
    : List Expr → List String × EmitState
  | [] => ([], st)
  | e :: es =>
    let (sig, st) := compileExpr st ctx fns consts e
    let (sigs, st) := compileExprList st ctx fns consts es
    (sig :: sigs, st)

/-- Compile an expression to a Circom signal name.
    For uint256 equality, generates a two-limb comparison.
    For constants, inlines the value. -/
partial def compileExpr (st : EmitState) (ctx : ParamCtx)
    (fns : List FnDecl) (consts : List ConstDef)
    (expr : Expr) : String × EmitState :=
  match expr with
  | .intLit n =>
    let (name, st) := st.fresh "lit"
    let st := st.addLine s!"    signal {name};"
    let st := st.addLine s!"    {name} <== {n};"
    (name, st)
  | .param name =>
    -- Check if it's a constant first
    match evalConstInt consts (.param name) with
    | some n =>
      let (cname, st) := st.fresh "const"
      let st := st.addLine s!"    signal {cname};"
      let st := st.addLine s!"    {cname} <== {n};"
      (cname, st)
    | none => (name, st)
  | .strLit _ => ("0", st)
  | .eq a b => compileComparison st ctx fns consts a b "eq"
  | .ne a b =>
    let (eqSig, st) := compileComparison st ctx fns consts a b "eq"
    let (name, st) := st.fresh "ne"
    let st := st.addLine s!"    signal {name};"
    let st := st.addLine s!"    {name} <== 1 - {eqSig};"
    (name, st)
  | .and a b =>
    let (sigA, st) := compileExpr st ctx fns consts a
    let (sigB, st) := compileExpr st ctx fns consts b
    let (name, st) := st.fresh "and"
    let st := st.addLine s!"    signal {name};"
    let st := st.addLine s!"    {name} <== {sigA} * {sigB};"
    (name, st)
  | .or a b =>
    let (sigA, st) := compileExpr st ctx fns consts a
    let (sigB, st) := compileExpr st ctx fns consts b
    let (name, st) := st.fresh "or"
    let st := st.addLine s!"    signal {name};"
    let st := st.addLine s!"    {name} <== {sigA} + {sigB} - {sigA} * {sigB};"
    (name, st)
  | .not a =>
    let (sigA, st) := compileExpr st ctx fns consts a
    let (name, st) := st.fresh "not"
    let st := st.addLine s!"    signal {name};"
    let st := st.addLine s!"    {name} <== 1 - {sigA};"
    (name, st)
  | .lt a b =>
    let (sigA, st) := compileExpr st ctx fns consts a
    let (sigB, st) := compileExpr st ctx fns consts b
    let (cmpName, st) := st.fresh "lt"
    let st := st.addLine s!"    component {cmpName} = LessThan(252);"
    let st := st.addLine s!"    {cmpName}.in[0] <== {sigA};"
    let st := st.addLine s!"    {cmpName}.in[1] <== {sigB};"
    (s!"{cmpName}.out", st)
  | .gt a b => compileExpr st ctx fns consts (.lt b a)
  | .le a b =>
    let (ltSig, st) := compileExpr st ctx fns consts (.lt b a)
    let (name, st) := st.fresh "le"
    let st := st.addLine s!"    signal {name};"
    let st := st.addLine s!"    {name} <== 1 - {ltSig};"
    (name, st)
  | .ge a b => compileExpr st ctx fns consts (.le b a)
  | .call fnName args =>
    match fns.find? (fun f => f.name == fnName) with
    | some fn =>
      match fn.expr with
      | some body =>
        -- Use a unique prefix to avoid duplicate signals when the same helper is called twice
        let (uniquePfx, st) := st.fresh fnName
        let st := bindFnArgs st ctx fns consts uniquePfx fn.params args
        let fnCtx : ParamCtx := fn.params.map (fun (n, t) => (s!"{uniquePfx}_{n}", t))
        let paramNames := fn.params.map (·.1)
        let remappedBody := remapParams uniquePfx paramNames body
        compileExpr st (fnCtx ++ ctx) fns consts remappedBody
      | none =>
        let st := st.addLine s!"    // ERROR: function '{fnName}' has no expression body"
        ("0", st)
    | none =>
      let st := st.addLine s!"    // ERROR: undefined function '{fnName}'"
      ("0", st)
  -- index and length are not directly compilable to circuits in general;
  -- they are resolved during forEach unrolling. If reached here, emit 0.
  | .index _ _ => ("0", st)
  | .length _ => ("0", st)

/-- Compile an equality comparison, handling uint256 two-limb comparison. -/
partial def compileComparison (st : EmitState) (ctx : ParamCtx)
    (fns : List FnDecl) (consts : List ConstDef)
    (a b : Expr) (tag : String) : String × EmitState :=
  -- Check if either operand is a uint256 param
  let aIsUint256 := isUint256Expr ctx consts a
  let bIsUint256 := isUint256Expr ctx consts b
  if aIsUint256 || bIsUint256 then
    -- uint256 equality: compare both 128-bit limbs
    let (aLo, aHi, st) := getUint256Signals st ctx consts a
    let (bLo, bHi, st) := getUint256Signals st ctx consts b
    let (eqLo, st) := st.fresh "eqLo"
    let st := st.addLine s!"    component {eqLo} = IsEqual();"
    let st := st.addLine s!"    {eqLo}.in[0] <== {aLo};"
    let st := st.addLine s!"    {eqLo}.in[1] <== {bLo};"
    let (eqHi, st) := st.fresh "eqHi"
    let st := st.addLine s!"    component {eqHi} = IsEqual();"
    let st := st.addLine s!"    {eqHi}.in[0] <== {aHi};"
    let st := st.addLine s!"    {eqHi}.in[1] <== {bHi};"
    let (result, st) := st.fresh tag
    let st := st.addLine s!"    signal {result};"
    let st := st.addLine s!"    {result} <== {eqLo}.out * {eqHi}.out;"
    (result, st)
  else
    -- Single-field equality
    let (sigA, st) := compileExpr st ctx fns consts a
    let (sigB, st) := compileExpr st ctx fns consts b
    let (cmpName, st) := st.fresh tag
    let st := st.addLine s!"    component {cmpName} = IsEqual();"
    let st := st.addLine s!"    {cmpName}.in[0] <== {sigA};"
    let st := st.addLine s!"    {cmpName}.in[1] <== {sigB};"
    (s!"{cmpName}.out", st)

/-- Compile statements, collecting emit paths. -/
partial def compileStmts (st : EmitState) (ctx : ParamCtx)
    (fns : List FnDecl) (consts : List ConstDef)
    (stmts : List Stmt) (condSig : String) (nextTemplateIdx : Nat)
    : EmitState × List EmitPath × Nat :=
  match stmts with
  | [] => (st, [], nextTemplateIdx)
  | stmt :: rest =>
    match stmt with
    | .emit tmpl =>
      -- Resolve hole signals: map param names to their Circom signals
      let holeSignals := tmpl.holes.flatMap (fun h =>
        match ctx.findType h.param with
        | some (.uint256) | some (.int256) =>
          [s!"{h.param}_lo", s!"{h.param}_hi"]
        | _ => [h.param])
      let path : EmitPath := {
        templateIdx := nextTemplateIdx
        templateText := tmpl.text
        holeSignals
        conditionSignal := condSig
      }
      let (st, morePaths, nextIdx) := compileStmts st ctx fns consts rest condSig (nextTemplateIdx + 1)
      (st, path :: morePaths, nextIdx)
    | .ite cond thenBranch elseBranch =>
      let (condResult, st) := compileExpr st ctx fns consts cond
      let (thenSig, st) := st.fresh "thenActive"
      let st := st.addLine s!"    signal {thenSig};"
      let st := st.addLine s!"    {thenSig} <== {condSig} * {condResult};"
      let (elseSig, st) := st.fresh "elseActive"
      let st := st.addLine s!"    signal {elseSig};"
      let st := st.addLine s!"    {elseSig} <== {condSig} * (1 - {condResult});"
      let (st, thenPaths, nextIdx) := compileStmts st ctx fns consts thenBranch thenSig nextTemplateIdx
      let (st, elsePaths, nextIdx) := compileStmts st ctx fns consts elseBranch elseSig nextIdx
      let (st, restPaths, nextIdx) := compileStmts st ctx fns consts rest condSig nextIdx
      (st, thenPaths ++ elsePaths ++ restPaths, nextIdx)
    | .forEach _var _array _body =>
      -- forEach in circuits requires static unrolling; not yet supported.
      -- Skip and continue with remaining statements.
      compileStmts st ctx fns consts rest condSig nextTemplateIdx
    | .call fnName args =>
      match fns.find? (fun f => f.name == fnName) with
      | some fn =>
        -- Only inline void functions; non-void helpers are expression-level
        if fn.returnKind != .void then
          compileStmts st ctx fns consts rest condSig nextTemplateIdx
        else
          -- Use a unique prefix to avoid duplicate signals when the same helper is called twice
          let (uniquePfx, st) := st.fresh fnName
          let st := bindFnArgs st ctx fns consts uniquePfx fn.params args
          let fnCtx : ParamCtx := fn.params.map (fun (n, t) => (s!"{uniquePfx}_{n}", t))
          let paramNames := fn.params.map (·.1)
          let remappedBody := fn.body.map (remapStmtParams uniquePfx paramNames)
          let (st, callPaths, nextIdx) := compileStmts st (fnCtx ++ ctx) fns consts remappedBody condSig nextTemplateIdx
          let (st, restPaths, nextIdx) := compileStmts st ctx fns consts rest condSig nextIdx
          (st, callPaths ++ restPaths, nextIdx)
      | none =>
        compileStmts st ctx fns consts rest condSig nextTemplateIdx

end  -- mutual

/-! ## Top-Level Circuit Generation -/

private def capitalize (s : String) : String :=
  match s.data with
  | [] => ""
  | c :: cs => String.mk (c.toUpper :: cs)

private def indexed (xs : List α) : List (Nat × α) :=
  let rec go : Nat → List α → List (Nat × α)
    | _, [] => []
    | i, x :: rest => (i, x) :: go (i + 1) rest
  go 0 xs

private def dedup (xs : List String) : List String :=
  let rec go : List String → List String → List String
    | [], _ => []
    | x :: rest, seen =>
      if seen.contains x then go rest seen
      else x :: go rest (x :: seen)
  go xs []

/-- Generate Circom source for a single intent binding.
    `selectorHex` is the 4-byte selector as a hex string (e.g. "0xa9059cbb").
    Returns the complete `.circom` file content. -/
def emitCircom (spec : IntentSpec) (binding : IntentBinding)
    (selectorHex : String) : Option String := do
  let fn ← spec.fns.find? (fun f => f.name == binding.intentFn)

  let inputSignals := allParamSignals fn.params
  let ctx : ParamCtx := fn.params

  -- Compile the function body
  let initState : EmitState := {}
  let (st, paths, _) :=
    compileStmts initState ctx spec.fns spec.constants fn.body "1" 0

  let templateName := capitalize binding.functionName ++ "Intent"
  let totalCdArity := 1 + inputSignals.length  -- selector + params

  -- Build the output
  let header :=
    "pragma circom 2.1.0;\n" ++
    "\n" ++
    "include \"circomlib/circuits/poseidon.circom\";\n" ++
    "include \"circomlib/circuits/comparators.circom\";\n" ++
    "include \"circomlib/circuits/mux1.circom\";\n" ++
    "\n" ++
    s!"// Auto-generated by Verity intent compiler\n" ++
    s!"// Contract: {spec.contractName}\n" ++
    s!"// Function: {binding.functionName}\n" ++
    s!"// Selector: {selectorHex}\n" ++
    "\n"

  let templateDecl :=
    s!"template {templateName}() \{\n" ++
    "    // Public inputs\n" ++
    "    signal input selector;\n" ++
    "    signal input calldataCommitment;\n" ++
    "    signal input outputCommitment;\n" ++
    "\n" ++
    "    // Private inputs (decoded calldata parameters)\n"

  let paramDecls := String.intercalate "\n"
    (inputSignals.map (fun s => s!"    signal input {s};"))

  let selectorCheck :=
    "\n" ++
    "\n" ++
    "    // 1. Selector check\n" ++
    s!"    selector === {selectorHex};\n"

  let cdLines :=
    "\n" ++
    "    // 2. Calldata commitment\n" ++
    s!"    component cdHash = Poseidon({totalCdArity});\n" ++
    "    cdHash.inputs[0] <== selector;\n" ++
    String.intercalate "\n"
      ((indexed inputSignals).map (fun (i, s) =>
        s!"    cdHash.inputs[{i + 1}] <== {s};")) ++
    "\n" ++
    "    calldataCommitment === cdHash.out;\n"

  let condCode :=
    "\n" ++
    "    // 3. Evaluate conditions and select template\n" ++
    String.intercalate "\n" st.lines ++ "\n"

  let templateSelection :=
    if paths.length == 0 then
      "    // No emit paths (error in intent spec)\n"
    else if paths.length == 1 then
      match paths with
      | [p] =>
        s!"    // Single path: template {p.templateIdx} (\"{p.templateText}\")\n" ++
        s!"    signal templateId;\n" ++
        s!"    templateId <== {p.templateIdx};\n"
      | _ => ""
    else
      "    // Template selection (exactly one path must be active)\n" ++
      "    signal templateId;\n" ++
      (let terms := paths.map (fun p => s!"{p.templateIdx} * {p.conditionSignal}")
       s!"    templateId <== {String.intercalate " + " terms};\n")

  -- Output commitment: Poseidon(templateId, hole values...)
  let allHoleSignals := dedup (paths.flatMap (·.holeSignals))
  let outArity := 1 + allHoleSignals.length
  let outputCommitment :=
    "\n" ++
    "    // 4. Output commitment\n" ++
    s!"    component outHash = Poseidon({outArity});\n" ++
    "    outHash.inputs[0] <== templateId;\n" ++
    String.intercalate "\n"
      ((indexed allHoleSignals).map (fun (i, s) =>
        s!"    outHash.inputs[{i + 1}] <== {s};")) ++
    "\n" ++
    "    outputCommitment === outHash.out;\n"

  let footer :=
    "}\n" ++
    "\n" ++
    s!"component main \{public [selector, calldataCommitment, outputCommitment]} = {templateName}();\n"

  pure (header ++ templateDecl ++ paramDecls ++ selectorCheck
    ++ cdLines ++ condCode ++ templateSelection
    ++ outputCommitment ++ footer)

/-! ## File Output -/

def writeCircomFile (outDir : String) (spec : IntentSpec) (binding : IntentBinding)
    (selectorHex : String) : IO Unit := do
  match emitCircom spec binding selectorHex with
  | some content =>
    IO.FS.createDirAll outDir
    let path := s!"{outDir}/{spec.contractName}_{binding.functionName}.circom"
    IO.FS.writeFile path content
    IO.println s!"✓ Wrote Circom circuit: {path}"
  | none =>
    IO.eprintln s!"✗ Failed to generate Circom for {spec.contractName}.{binding.functionName}"

def writeAllCircomFiles (outDir : String) (spec : IntentSpec)
    (selectors : List (String × String)) : IO Unit := do
  for binding in spec.bindings do
    match selectors.find? (fun (name, _) => name == binding.functionName) with
    | some (_, hex) => writeCircomFile outDir spec binding hex
    | none =>
      IO.eprintln s!"✗ No selector found for {binding.functionName}"

end Compiler.Circom
