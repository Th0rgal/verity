import Compiler.Yul.PatchRules

namespace Compiler.Proofs.YulGeneration.PatchRulesProofs

open Compiler.Yul

/-- Abstract expression evaluator used to state backend-agnostic preservation obligations. -/
abbrev EvalExpr := YulExpr → Option Nat

/-- Proof hook contract: a rewrite must preserve evaluation under a chosen semantics. -/
def ExprPatchPreservesUnder (eval : EvalExpr) (rule : ExprPatchRule) : Prop :=
  ∀ (expr rewritten : YulExpr),
    rule.applyExpr expr = some rewritten →
    eval expr = eval rewritten

/-- Minimal evaluator laws needed to discharge the foundation bitwise patch pack. -/
structure FoundationEvaluatorLaws (eval : EvalExpr) : Prop where
  or_zero_right : ∀ lhs, eval (.call "or" [lhs, .lit 0]) = eval lhs
  or_zero_left : ∀ rhs, eval (.call "or" [.lit 0, rhs]) = eval rhs
  xor_zero_right : ∀ lhs, eval (.call "xor" [lhs, .lit 0]) = eval lhs

/-- Obligation for `or(x, 0) -> x`. -/
def or_zero_right_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.orZeroRightRule

/-- Obligation for `or(0, x) -> x`. -/
def or_zero_left_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.orZeroLeftRule

/-- Obligation for `xor(x, 0) -> x`. -/
def xor_zero_right_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.xorZeroRightRule

/-- Registry hook: each shipped foundation patch has an explicit proof obligation. -/
def foundation_patch_pack_obligations (eval : EvalExpr) : Prop :=
  or_zero_right_preserves eval ∧
  or_zero_left_preserves eval ∧
  xor_zero_right_preserves eval

end Compiler.Proofs.YulGeneration.PatchRulesProofs
