import Compiler.Yul.PatchFramework

namespace Compiler.Yul

/-- `or(x, 0) -> x` -/
def orZeroRightRule : ExprPatchRule :=
  { patchName := "or-zero-right"
    pattern := "or(x, 0)"
    rewrite := "x"
    sideConditions := ["second argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.or_zero_right_preserves"
    passPhase := .postCodegen
    priority := 100
    applyExpr := fun expr =>
      match expr with
      | .call "or" [lhs, .lit 0] => some lhs
      | _ => none }

/-- `or(0, x) -> x` -/
def orZeroLeftRule : ExprPatchRule :=
  { patchName := "or-zero-left"
    pattern := "or(0, x)"
    rewrite := "x"
    sideConditions := ["first argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.or_zero_left_preserves"
    passPhase := .postCodegen
    priority := 95
    applyExpr := fun expr =>
      match expr with
      | .call "or" [.lit 0, rhs] => some rhs
      | _ => none }

/-- `xor(x, 0) -> x` -/
def xorZeroRightRule : ExprPatchRule :=
  { patchName := "xor-zero-right"
    pattern := "xor(x, 0)"
    rewrite := "x"
    sideConditions := ["second argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.xor_zero_right_preserves"
    passPhase := .postCodegen
    priority := 90
    applyExpr := fun expr =>
      match expr with
      | .call "xor" [lhs, .lit 0] => some lhs
      | _ => none }

/-- Initial deterministic, proven-safe expression patch pack (Issue #582 foundation). -/
def foundationExprPatchPack : List ExprPatchRule :=
  [orZeroRightRule, orZeroLeftRule, xorZeroRightRule]

/-- Smoke test: higher-priority rule wins deterministically. -/
example :
    (let rules := orderRulesByPriority [xorZeroRightRule, orZeroRightRule, orZeroLeftRule]
     rules.map (fun r => r.patchName)) =
    ["or-zero-right", "or-zero-left", "xor-zero-right"] := by
  native_decide

/-- Smoke test: one rewrite pass catches nested expression occurrences. -/
example :
    let stmt : YulStmt :=
      .expr (.call "or" [.call "xor" [.ident "x", .lit 0], .lit 0])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } foundationExprPatchPack [stmt]
    (match report.patched with
    | [.expr (.ident "x")] => true
    | _ => false) = true := by
  native_decide

/-- Smoke test: manifest emits rule usage with proof refs. -/
example :
    let stmt : YulStmt := .expr (.call "or" [.ident "x", .lit 0])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } foundationExprPatchPack [stmt]
    report.manifest.map (fun m => (m.patchName, m.matchCount, m.proofRef)) =
      [("or-zero-right", 1,
        "Compiler.Proofs.YulGeneration.PatchRulesProofs.or_zero_right_preserves")] := by
  native_decide

/-- Smoke test: fail-closed metadata gate skips non-auditable rules. -/
example :
    let unsafeRule : ExprPatchRule :=
      { patchName := "unsafe-without-proof"
        pattern := "or(x, 0)"
        rewrite := "x"
        sideConditions := []
        proofId := ""
        passPhase := .postCodegen
        priority := 999
        applyExpr := fun expr =>
          match expr with
          | .call "or" [lhs, .lit 0] => some lhs
          | _ => none }
    let stmt : YulStmt := .expr (.call "or" [.ident "x", .lit 0])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } [unsafeRule] [stmt]
    (match report.patched, report.iterations, report.manifest with
    | [.expr (.call "or" [.ident "x", .lit 0])], 0, [] => true
    | _, _, _ => false) = true := by
  native_decide

end Compiler.Yul
