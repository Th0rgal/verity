import Compiler.Yul.Ast

namespace Compiler.Yul

/-- Phase at which a patch rule runs. -/
inductive PatchPhase
  | postCodegen
  deriving Repr, DecidableEq

/-- Audit metadata + executable rewrite for one expression patch rule. -/
structure ExprPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : String
  passPhase : PatchPhase
  priority : Nat
  applyExpr : YulExpr → Option YulExpr

/-- Fail-closed metadata guard: a runnable rule must carry audit/proof linkage. -/
def ExprPatchRule.isAuditable (rule : ExprPatchRule) : Bool :=
  !rule.patchName.isEmpty && !rule.proofId.isEmpty && !rule.sideConditions.isEmpty

/-- Deterministic patch pass settings. -/
structure PatchPassConfig where
  enabled : Bool := true
  maxIterations : Nat := 2
  passPhase : PatchPhase := .postCodegen

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

private def insertRuleByPriority (rule : ExprPatchRule) : List ExprPatchRule → List ExprPatchRule
  | [] => [rule]
  | head :: tail =>
      if rule.priority > head.priority then
        rule :: head :: tail
      else
        head :: insertRuleByPriority rule tail

/-- Stable, deterministic ordering: priority descending, declaration order as tie-break. -/
def orderRulesByPriority (rules : List ExprPatchRule) : List ExprPatchRule :=
  rules.foldl (fun acc rule => insertRuleByPriority rule acc) []

private def applyFirstRule (orderedRules : List ExprPatchRule) (expr : YulExpr) : Option (YulExpr × String) :=
  let rec go : List ExprPatchRule → Option (YulExpr × String)
    | [] => none
    | rule :: rest =>
        match rule.applyExpr expr with
        | some rewritten => some (rewritten, rule.patchName)
        | none => go rest
  go orderedRules

mutual

private def rewriteExprOnce (orderedRules : List ExprPatchRule) : YulExpr → (YulExpr × List String)
  | .call func args =>
      let (rewrittenArgs, argHits) := rewriteExprListOnce orderedRules args
      let candidate := YulExpr.call func rewrittenArgs
      match applyFirstRule orderedRules candidate with
      | some (rewritten, patchName) => (rewritten, patchName :: argHits)
      | none => (candidate, argHits)
  | expr =>
      match applyFirstRule orderedRules expr with
      | some (rewritten, patchName) => (rewritten, [patchName])
      | none => (expr, [])

private def rewriteExprListOnce (orderedRules : List ExprPatchRule) : List YulExpr → (List YulExpr × List String)
  | [] => ([], [])
  | expr :: rest =>
      let (expr', hitsHead) := rewriteExprOnce orderedRules expr
      let (rest', hitsTail) := rewriteExprListOnce orderedRules rest
      (expr' :: rest', hitsHead ++ hitsTail)

end

mutual

private def rewriteStmtOnce (orderedRules : List ExprPatchRule) : YulStmt → (YulStmt × List String)
  | .comment txt => (.comment txt, [])
  | .let_ name value =>
      let (value', hits) := rewriteExprOnce orderedRules value
      (.let_ name value', hits)
  | .assign name value =>
      let (value', hits) := rewriteExprOnce orderedRules value
      (.assign name value', hits)
  | .expr expr =>
      let (expr', hits) := rewriteExprOnce orderedRules expr
      (.expr expr', hits)
  | .if_ cond body =>
      let (cond', condHits) := rewriteExprOnce orderedRules cond
      let (body', bodyHits) := rewriteStmtListOnce orderedRules body
      (.if_ cond' body', condHits ++ bodyHits)
  | .for_ init cond post body =>
      let (init', initHits) := rewriteStmtListOnce orderedRules init
      let (cond', condHits) := rewriteExprOnce orderedRules cond
      let (post', postHits) := rewriteStmtListOnce orderedRules post
      let (body', bodyHits) := rewriteStmtListOnce orderedRules body
      (.for_ init' cond' post' body', initHits ++ condHits ++ postHits ++ bodyHits)
  | .switch expr cases default =>
      let (expr', exprHits) := rewriteExprOnce orderedRules expr
      let (cases', caseHits) := rewriteSwitchCasesOnce orderedRules cases
      let (default', defaultHits) := rewriteOptionalStmtListOnce orderedRules default
      (.switch expr' cases' default', exprHits ++ caseHits ++ defaultHits)
  | .block stmts =>
      let (stmts', hits) := rewriteStmtListOnce orderedRules stmts
      (.block stmts', hits)
  | .funcDef name params rets body =>
      let (body', hits) := rewriteStmtListOnce orderedRules body
      (.funcDef name params rets body', hits)

private def rewriteStmtListOnce (orderedRules : List ExprPatchRule) : List YulStmt → (List YulStmt × List String)
  | [] => ([], [])
  | stmt :: rest =>
      let (stmt', headHits) := rewriteStmtOnce orderedRules stmt
      let (rest', tailHits) := rewriteStmtListOnce orderedRules rest
      (stmt' :: rest', headHits ++ tailHits)

private def rewriteOptionalStmtListOnce (orderedRules : List ExprPatchRule) : Option (List YulStmt) → (Option (List YulStmt) × List String)
  | none => (none, [])
  | some stmts =>
      let (stmts', hits) := rewriteStmtListOnce orderedRules stmts
      (some stmts', hits)

private def rewriteSwitchCasesOnce
    (orderedRules : List ExprPatchRule) : List (Nat × List YulStmt) → (List (Nat × List YulStmt) × List String)
  | [] => ([], [])
  | (tag, body) :: rest =>
      let (body', bodyHits) := rewriteStmtListOnce orderedRules body
      let (rest', restHits) := rewriteSwitchCasesOnce orderedRules rest
      ((tag, body') :: rest', bodyHits ++ restHits)

end

private def countHitsForPatch (patchName : String) (hits : List String) : Nat :=
  hits.foldl (fun acc hit => if hit = patchName then acc + 1 else acc) 0

private def manifestFromHits (rules : List ExprPatchRule) (hits : List String) : List PatchManifestEntry :=
  (rules.foldr (fun rule acc =>
    let hitCount := countHitsForPatch rule.patchName hits
    if hitCount = 0 then
      acc
    else
      { patchName := rule.patchName
        matchCount := hitCount
        changedNodes := hitCount
        proofRef := rule.proofId } :: acc) [])

private def runPatchPassLoop
    (fuel : Nat)
    (orderedRules : List ExprPatchRule)
    (current : List YulStmt)
    (iterations : Nat)
    (allHits : List String) : List YulStmt × Nat × List String :=
  match fuel with
  | 0 => (current, iterations, allHits)
  | Nat.succ fuel' =>
      let (next, stepHits) := rewriteStmtListOnce orderedRules current
      if stepHits.isEmpty then
        (current, iterations, allHits)
      else
        runPatchPassLoop fuel' orderedRules next (iterations + 1) (allHits ++ stepHits)

/-- Run one deterministic patch pass on statements with bounded fixpoint iterations. -/
def runExprPatchPass
    (config : PatchPassConfig)
    (rules : List ExprPatchRule)
    (stmts : List YulStmt) : PatchPassReport :=
  if ¬config.enabled then
    { patched := stmts, iterations := 0, manifest := [] }
  else
    let orderedRules :=
      orderRulesByPriority (rules.filter (fun rule =>
        rule.passPhase == config.passPhase && rule.isAuditable))
    let (patched, iterations, hits) := runPatchPassLoop config.maxIterations orderedRules stmts 0 []
    { patched := patched
      iterations := iterations
      manifest := manifestFromHits orderedRules hits }

end Compiler.Yul
