import Compiler.Yul.Ast
import Lean

namespace Compiler.Yul

/-- Phase at which a patch rule runs. -/
inductive PatchPhase
  | postCodegen
  deriving Repr, DecidableEq

/-- Scope in which a patch rule is allowed to run. -/
inductive RewriteScope
  | runtime
  | deploy
  | object
  deriving Repr, DecidableEq

/-- Typed rewrite execution context carried through one pass iteration. -/
structure RewriteCtx where
  scope : RewriteScope
  passPhase : PatchPhase
  iteration : Nat
  packId : String := ""
  deriving Repr

/-- Audit metadata + executable rewrite for one expression patch rule. -/
structure ExprPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : Lean.Name
  packAllowlist : List String := []
  scope : RewriteScope
  passPhase : PatchPhase
  priority : Nat
  applyExpr : RewriteCtx → YulExpr → Option YulExpr

/-- Audit metadata + executable rewrite for one statement patch rule. -/
structure StmtPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : Lean.Name
  packAllowlist : List String := []
  scope : RewriteScope
  passPhase : PatchPhase
  priority : Nat
  applyStmt : RewriteCtx → YulStmt → Option YulStmt

/-- Audit metadata + executable rewrite for one block patch rule. -/
structure BlockPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : Lean.Name
  packAllowlist : List String := []
  scope : RewriteScope
  passPhase : PatchPhase
  priority : Nat
  applyBlock : RewriteCtx → List YulStmt → Option (List YulStmt)

/-- Audit metadata + executable rewrite for one object-level patch rule. -/
structure ObjectPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : Lean.Name
  packAllowlist : List String := []
  scope : RewriteScope
  passPhase : PatchPhase
  priority : Nat
  applyObject : RewriteCtx → YulObject → Option YulObject

/-- Deterministic patch pass settings. -/
structure PatchPassConfig where
  enabled : Bool := true
  maxIterations : Nat := 2
  passPhase : PatchPhase := .postCodegen
  packId : String := ""
  /-- Selected rewrite bundle ID (e.g., `foundation`, `solc-compat-v0`). -/
  rewriteBundleId : String := "foundation"
  /-- Optional activation-time proof registry for fail-closed rule filtering.
      When non-empty, only rules whose `proofId` appears in this list can run. -/
  requiredProofRefs : List Lean.Name := []

/-- Per-rule usage entry emitted by the patch pass. -/
structure PatchManifestEntry where
  patchName : String
  matchCount : Nat
  changedNodes : Nat
  proofRef : String
  deriving Repr

/-- Result of running a patch pass over Yul statements. -/
structure PatchPassReport where
  patched : List YulStmt
  iterations : Nat
  manifest : List PatchManifestEntry
  deriving Repr

/-- Result of running a patch pass over a full Yul object. -/
structure ObjectPatchPassReport where
  patched : YulObject
  iterations : Nat
  manifest : List PatchManifestEntry
  deriving Repr

private structure PatchRuleMeta where
  patchName : String
  proofRef : Lean.Name

private class PatchRuleLike (α : Type) where
  patchName : α → String
  proofId : α → Lean.Name
  sideConditions : α → List String
  packAllowlist : α → List String
  scope : α → RewriteScope
  passPhase : α → PatchPhase
  priority : α → Nat

private def proofRefPresent (proofRef : Lean.Name) : Bool :=
  proofRef != .anonymous

/-- Parse a dotted declaration name into `Lean.Name` metadata without requiring the
    declaration to be imported at the call site. -/
def proofRefName (ref : String) : Lean.Name :=
  ref.splitOn "." |>.foldl Lean.Name.str .anonymous

private def isRuleAuditable [PatchRuleLike α] (r : α) : Bool :=
  !(PatchRuleLike.patchName r).isEmpty &&
    proofRefPresent (PatchRuleLike.proofId r) &&
    !(PatchRuleLike.sideConditions r).isEmpty

private instance : PatchRuleLike ExprPatchRule where
  patchName := fun r => r.patchName
  proofId := fun r => r.proofId
  sideConditions := fun r => r.sideConditions
  packAllowlist := fun r => r.packAllowlist
  scope := fun r => r.scope
  passPhase := fun r => r.passPhase
  priority := fun r => r.priority

private instance : PatchRuleLike StmtPatchRule where
  patchName := fun r => r.patchName
  proofId := fun r => r.proofId
  sideConditions := fun r => r.sideConditions
  packAllowlist := fun r => r.packAllowlist
  scope := fun r => r.scope
  passPhase := fun r => r.passPhase
  priority := fun r => r.priority

private instance : PatchRuleLike BlockPatchRule where
  patchName := fun r => r.patchName
  proofId := fun r => r.proofId
  sideConditions := fun r => r.sideConditions
  packAllowlist := fun r => r.packAllowlist
  scope := fun r => r.scope
  passPhase := fun r => r.passPhase
  priority := fun r => r.priority

private instance : PatchRuleLike ObjectPatchRule where
  patchName := fun r => r.patchName
  proofId := fun r => r.proofId
  sideConditions := fun r => r.sideConditions
  packAllowlist := fun r => r.packAllowlist
  scope := fun r => r.scope
  passPhase := fun r => r.passPhase
  priority := fun r => r.priority

private def ruleAllowsPack [PatchRuleLike α] (rule : α) (packId : String) : Bool :=
  let allowlist := PatchRuleLike.packAllowlist rule
  allowlist.isEmpty || allowlist.any (fun allowed => allowed = packId)

private def ruleActiveInCtx [PatchRuleLike α] (rule : α) (ctx : RewriteCtx) : Bool :=
  PatchRuleLike.scope rule == ctx.scope &&
    PatchRuleLike.passPhase rule == ctx.passPhase &&
    ruleAllowsPack rule ctx.packId

private def ruleHasRegisteredProof [PatchRuleLike α] (config : PatchPassConfig) (rule : α) : Bool :=
  config.requiredProofRefs.isEmpty ||
    config.requiredProofRefs.any (fun proofRef => proofRef = PatchRuleLike.proofId rule)

/-- Fail-closed metadata guard: a runnable rule must carry audit/proof linkage. -/
def ExprPatchRule.isAuditable (rule : ExprPatchRule) : Bool :=
  isRuleAuditable rule

/-- Fail-closed metadata guard: a runnable statement rule must carry audit/proof linkage. -/
def StmtPatchRule.isAuditable (rule : StmtPatchRule) : Bool :=
  isRuleAuditable rule

/-- Fail-closed metadata guard: a runnable block rule must carry audit/proof linkage. -/
def BlockPatchRule.isAuditable (rule : BlockPatchRule) : Bool :=
  isRuleAuditable rule

/-- Fail-closed metadata guard: a runnable object rule must carry audit/proof linkage. -/
def ObjectPatchRule.isAuditable (rule : ObjectPatchRule) : Bool :=
  isRuleAuditable rule

private def insertByPriority [PatchRuleLike α] (r : α) : List α → List α
  | [] => [r]
  | head :: tail =>
      if PatchRuleLike.priority r > PatchRuleLike.priority head then
        r :: head :: tail
      else
        head :: insertByPriority r tail

private def orderByPriority [PatchRuleLike α] (rules : List α) : List α :=
  rules.foldl (fun acc r => insertByPriority r acc) []

private def applyFirstPatchRule [PatchRuleLike α]
    (orderedRules : List α)
    (applyRule : α → RewriteCtx → target → Option target)
    (ctx : RewriteCtx)
    (targetNode : target) : Option (target × String) :=
  let rec go : List α → Option (target × String)
    | [] => none
    | r :: rest =>
        if !(ruleActiveInCtx r ctx) then
          go rest
        else
          match applyRule r ctx targetNode with
          | some rewritten => some (rewritten, PatchRuleLike.patchName r)
          | none => go rest
  go orderedRules

/-- Stable, deterministic ordering: priority descending, declaration order as tie-break. -/
def orderRulesByPriority (rules : List ExprPatchRule) : List ExprPatchRule :=
  orderByPriority rules

/-- Stable, deterministic ordering for statement rules. -/
def orderStmtRulesByPriority (rules : List StmtPatchRule) : List StmtPatchRule :=
  orderByPriority rules

/-- Stable, deterministic ordering for block rules. -/
def orderBlockRulesByPriority (rules : List BlockPatchRule) : List BlockPatchRule :=
  orderByPriority rules

/-- Stable, deterministic ordering for object rules. -/
def orderObjectRulesByPriority (rules : List ObjectPatchRule) : List ObjectPatchRule :=
  orderByPriority rules

private def applyFirstRule
    (orderedRules : List ExprPatchRule)
    (ctx : RewriteCtx)
    (expr : YulExpr) : Option (YulExpr × String) :=
  applyFirstPatchRule orderedRules (fun rule ruleCtx node => rule.applyExpr ruleCtx node) ctx expr

private def applyFirstStmtRule
    (orderedRules : List StmtPatchRule)
    (ctx : RewriteCtx)
    (stmt : YulStmt) : Option (YulStmt × String) :=
  applyFirstPatchRule orderedRules (fun rule ruleCtx node => rule.applyStmt ruleCtx node) ctx stmt

private def applyFirstBlockRule
    (orderedRules : List BlockPatchRule)
    (ctx : RewriteCtx)
    (block : List YulStmt) : Option (List YulStmt × String) :=
  applyFirstPatchRule orderedRules (fun rule ruleCtx node => rule.applyBlock ruleCtx node) ctx block

private def applyAllObjectRulesOnce
    (orderedRules : List ObjectPatchRule)
    (ctx : RewriteCtx)
    (obj : YulObject) : YulObject × List String :=
  orderedRules.foldl
    (fun (state : YulObject × List String) rule =>
      let (currentObj, hits) := state
      if ¬ruleActiveInCtx rule ctx then
        (currentObj, hits)
      else
        match rule.applyObject ctx currentObj with
        | some rewritten => (rewritten, hits ++ [rule.patchName])
        | none => (currentObj, hits))
    (obj, [])

mutual

private def rewriteExprOnce
    (orderedRules : List ExprPatchRule)
    (ctx : RewriteCtx) : YulExpr → (YulExpr × List String)
  | .call func args =>
      let (rewrittenArgs, argHits) := rewriteExprListOnce orderedRules ctx args
      let candidate := YulExpr.call func rewrittenArgs
      match applyFirstRule orderedRules ctx candidate with
      | some (rewritten, patchName) => (rewritten, patchName :: argHits)
      | none => (candidate, argHits)
  | expr =>
      match applyFirstRule orderedRules ctx expr with
      | some (rewritten, patchName) => (rewritten, [patchName])
      | none => (expr, [])

private def rewriteExprListOnce
    (orderedRules : List ExprPatchRule)
    (ctx : RewriteCtx) : List YulExpr → (List YulExpr × List String)
  | [] => ([], [])
  | expr :: rest =>
      let (expr', hitsHead) := rewriteExprOnce orderedRules ctx expr
      let (rest', hitsTail) := rewriteExprListOnce orderedRules ctx rest
      (expr' :: rest', hitsHead ++ hitsTail)

end

private def applyStmtRulesToCandidate
    (orderedStmtRules : List StmtPatchRule)
    (ctx : RewriteCtx)
    (candidate : YulStmt)
    (hits : List String) : YulStmt × List String :=
  match applyFirstStmtRule orderedStmtRules ctx candidate with
  | some (rewritten, patchName) => (rewritten, hits ++ [patchName])
  | none => (candidate, hits)

mutual

private def rewriteStmtOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (ctx : RewriteCtx) : YulStmt → (YulStmt × List String)
  | .comment txt =>
      applyStmtRulesToCandidate orderedStmtRules ctx (.comment txt) []
  | .let_ name value =>
      let (value', hits) := rewriteExprOnce orderedExprRules ctx value
      applyStmtRulesToCandidate orderedStmtRules ctx (.let_ name value') hits
  | .letMany names value =>
      let (value', hits) := rewriteExprOnce orderedExprRules ctx value
      applyStmtRulesToCandidate orderedStmtRules ctx (.letMany names value') hits
  | .assign name value =>
      let (value', hits) := rewriteExprOnce orderedExprRules ctx value
      applyStmtRulesToCandidate orderedStmtRules ctx (.assign name value') hits
  | .expr expr =>
      let (expr', hits) := rewriteExprOnce orderedExprRules ctx expr
      applyStmtRulesToCandidate orderedStmtRules ctx (.expr expr') hits
  | .leave =>
      applyStmtRulesToCandidate orderedStmtRules ctx .leave []
  | .if_ cond body =>
      let (cond', condHits) := rewriteExprOnce orderedExprRules ctx cond
      let (body', bodyHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx body
      applyStmtRulesToCandidate orderedStmtRules ctx (.if_ cond' body') (condHits ++ bodyHits)
  | .for_ init cond post body =>
      let (init', initHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx init
      let (cond', condHits) := rewriteExprOnce orderedExprRules ctx cond
      let (post', postHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx post
      let (body', bodyHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx body
      applyStmtRulesToCandidate
        orderedStmtRules
        ctx
        (.for_ init' cond' post' body')
        (initHits ++ condHits ++ postHits ++ bodyHits)
  | .switch expr cases default =>
      let (expr', exprHits) := rewriteExprOnce orderedExprRules ctx expr
      let (cases', caseHits) := rewriteSwitchCasesOnce orderedExprRules orderedStmtRules orderedBlockRules ctx cases
      let (default', defaultHits) := rewriteOptionalStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx default
      applyStmtRulesToCandidate orderedStmtRules ctx (.switch expr' cases' default') (exprHits ++ caseHits ++ defaultHits)
  | .block stmts =>
      let (stmts', hits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx stmts
      applyStmtRulesToCandidate orderedStmtRules ctx (.block stmts') hits
  | .funcDef name params rets body =>
      let (body', hits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx body
      applyStmtRulesToCandidate orderedStmtRules ctx (.funcDef name params rets body') hits

private def rewriteStmtListOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (ctx : RewriteCtx) : List YulStmt → (List YulStmt × List String)
  | [] => ([], [])
  | stmt :: rest =>
      let (stmt', headHits) := rewriteStmtOnce orderedExprRules orderedStmtRules orderedBlockRules ctx stmt
      let (rest', tailHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx rest
      let candidate := stmt' :: rest'
      let hits := headHits ++ tailHits
      match applyFirstBlockRule orderedBlockRules ctx candidate with
      | some (rewritten, patchName) => (rewritten, hits ++ [patchName])
      | none => (candidate, hits)

private def rewriteOptionalStmtListOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (ctx : RewriteCtx) : Option (List YulStmt) → (Option (List YulStmt) × List String)
  | none => (none, [])
  | some stmts =>
      let (stmts', hits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx stmts
      (some stmts', hits)

private def rewriteSwitchCasesOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (ctx : RewriteCtx) : List (Nat × List YulStmt) → (List (Nat × List YulStmt) × List String)
  | [] => ([], [])
  | (tag, body) :: rest =>
      let (body', bodyHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules ctx body
      let (rest', restHits) := rewriteSwitchCasesOnce orderedExprRules orderedStmtRules orderedBlockRules ctx rest
      ((tag, body') :: rest', bodyHits ++ restHits)

end

private def countHitsForPatch (patchName : String) (hits : List String) : Nat :=
  hits.foldl (fun acc hit => if hit = patchName then acc + 1 else acc) 0

private def metaListFromRules
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (blockRules : List BlockPatchRule)
    (objectRules : List ObjectPatchRule) : List PatchRuleMeta :=
  let exprMeta := exprRules.map (fun rule => { patchName := rule.patchName, proofRef := rule.proofId })
  let stmtMeta := stmtRules.map (fun rule => { patchName := rule.patchName, proofRef := rule.proofId })
  let blockMeta := blockRules.map (fun rule => { patchName := rule.patchName, proofRef := rule.proofId })
  let objectMeta := objectRules.map (fun rule => { patchName := rule.patchName, proofRef := rule.proofId })
  let allMeta := exprMeta ++ stmtMeta ++ blockMeta ++ objectMeta
  allMeta.foldl
    (fun acc m =>
      if acc.any (fun seen => seen.patchName = m.patchName) then acc else acc ++ [m])
    []

private def manifestFromHits (ruleMeta : List PatchRuleMeta) (hits : List String) : List PatchManifestEntry :=
  (ruleMeta.foldr (fun m acc =>
    let hitCount := countHitsForPatch m.patchName hits
    if hitCount = 0 then
      acc
    else
      { patchName := m.patchName
        matchCount := hitCount
        changedNodes := hitCount
        proofRef := toString m.proofRef } :: acc) [])

private def runPatchPassLoop
    (config : PatchPassConfig)
    (scope : RewriteScope)
    (fuel : Nat)
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (current : List YulStmt)
    (iterations : Nat)
    (allHits : List String) : List YulStmt × Nat × List String :=
  match fuel with
  | 0 => (current, iterations, allHits)
  | Nat.succ fuel' =>
      let loopCtx : RewriteCtx :=
        { scope := scope
          passPhase := config.passPhase
          iteration := iterations
          packId := config.packId }
      let (next, stepHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules loopCtx current
      if stepHits.isEmpty then
        (current, iterations, allHits)
      else
        runPatchPassLoop config scope fuel' orderedExprRules orderedStmtRules orderedBlockRules next (iterations + 1) (allHits ++ stepHits)

private def rewriteObjectOnce
    (config : PatchPassConfig)
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (orderedObjectRules : List ObjectPatchRule)
    (iteration : Nat)
    (obj : YulObject) : YulObject × List String :=
  let deployCtx : RewriteCtx :=
    { scope := .deploy
      passPhase := config.passPhase
      iteration := iteration
      packId := config.packId }
  let runtimeCtx : RewriteCtx :=
    { scope := .runtime
      passPhase := config.passPhase
      iteration := iteration
      packId := config.packId }
  let objectCtx : RewriteCtx :=
    { scope := .object
      passPhase := config.passPhase
      iteration := iteration
      packId := config.packId }
  let (deployCode', deployHits) :=
    rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules deployCtx obj.deployCode
  let (runtimeCode', runtimeHits) :=
    rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules runtimeCtx obj.runtimeCode
  let candidate := { obj with deployCode := deployCode', runtimeCode := runtimeCode' }
  let (afterObjectRules, objectHits) := applyAllObjectRulesOnce orderedObjectRules objectCtx candidate
  (afterObjectRules, deployHits ++ runtimeHits ++ objectHits)

private def runObjectPatchPassLoop
    (config : PatchPassConfig)
    (fuel : Nat)
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (orderedObjectRules : List ObjectPatchRule)
    (current : YulObject)
    (iterations : Nat)
    (allHits : List String) : YulObject × Nat × List String :=
  match fuel with
  | 0 => (current, iterations, allHits)
  | Nat.succ fuel' =>
      let (next, stepHits) :=
        rewriteObjectOnce config orderedExprRules orderedStmtRules orderedBlockRules orderedObjectRules iterations current
      if stepHits.isEmpty then
        (current, iterations, allHits)
      else
        runObjectPatchPassLoop
          config
          fuel'
          orderedExprRules
          orderedStmtRules
          orderedBlockRules
          orderedObjectRules
          next
          (iterations + 1)
          (allHits ++ stepHits)

/-- Run one deterministic patch pass over expression/statement/block rules with bounded fixpoint iterations.
    The pass defaults to runtime scope but can target deploy scope explicitly. -/
def runPatchPassWithBlocks
    (config : PatchPassConfig)
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (blockRules : List BlockPatchRule)
    (stmts : List YulStmt)
    (scope : RewriteScope := .runtime) : PatchPassReport :=
  if ¬config.enabled then
    { patched := stmts, iterations := 0, manifest := [] }
  else
    let orderedExprRules :=
      orderRulesByPriority
        (exprRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let orderedStmtRules :=
      orderStmtRulesByPriority
        (stmtRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let orderedBlockRules :=
      orderBlockRulesByPriority
        (blockRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let ruleMeta := metaListFromRules orderedExprRules orderedStmtRules orderedBlockRules []
    let (patched, iterations, hits) :=
      runPatchPassLoop config scope config.maxIterations orderedExprRules orderedStmtRules orderedBlockRules stmts 0 []
    { patched := patched
      iterations := iterations
      manifest := manifestFromHits ruleMeta hits }

/-- Run one deterministic patch pass over a full Yul object with bounded fixpoint iterations. -/
def runPatchPassWithObjects
    (config : PatchPassConfig)
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (blockRules : List BlockPatchRule)
    (objectRules : List ObjectPatchRule)
    (obj : YulObject) : ObjectPatchPassReport :=
  if ¬config.enabled then
    { patched := obj, iterations := 0, manifest := [] }
  else
    let orderedExprRules :=
      orderRulesByPriority
        (exprRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let orderedStmtRules :=
      orderStmtRulesByPriority
        (stmtRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let orderedBlockRules :=
      orderBlockRulesByPriority
        (blockRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let orderedObjectRules :=
      orderObjectRulesByPriority
        (objectRules.filter (fun rule => rule.isAuditable && ruleHasRegisteredProof config rule))
    let ruleMeta := metaListFromRules orderedExprRules orderedStmtRules orderedBlockRules orderedObjectRules
    let (patched, iterations, hits) :=
      runObjectPatchPassLoop
        config
        config.maxIterations
        orderedExprRules
        orderedStmtRules
        orderedBlockRules
        orderedObjectRules
        obj
        0
        []
    { patched := patched
      iterations := iterations
      manifest := manifestFromHits ruleMeta hits }

/-- Run one deterministic patch pass over expression and statement rules with bounded fixpoint iterations.
    Defaults to runtime scope. -/
def runPatchPass
    (config : PatchPassConfig)
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (stmts : List YulStmt)
    (scope : RewriteScope := .runtime) : PatchPassReport :=
  runPatchPassWithBlocks config exprRules stmtRules [] stmts scope

/-- Run one deterministic expression patch pass on statements with bounded fixpoint iterations.
    Defaults to runtime scope. -/
def runExprPatchPass
    (config : PatchPassConfig)
    (rules : List ExprPatchRule)
    (stmts : List YulStmt)
    (scope : RewriteScope := .runtime) : PatchPassReport :=
  runPatchPassWithBlocks config rules [] [] stmts scope

/-- Run one deterministic patch pass over a full Yul object with expression/statement/block rules. -/
def runPatchPassOnObject
    (config : PatchPassConfig)
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (blockRules : List BlockPatchRule)
    (obj : YulObject) : ObjectPatchPassReport :=
  runPatchPassWithObjects config exprRules stmtRules blockRules [] obj

end Compiler.Yul
