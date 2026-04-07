import Compiler.Yul.PatchRules

namespace Compiler.Proofs.YulGeneration.PatchRulesProofs

open Compiler.Yul

/-- Abstract expression evaluator used to state backend-agnostic preservation obligations. -/
abbrev EvalExpr := YulExpr → Option Nat

/-- Proof hook contract: a rewrite must preserve evaluation under a chosen semantics. -/
def ExprPatchPreservesUnder (eval : EvalExpr) (rule : ExprPatchRule) : Prop :=
  ∀ (ctx : RewriteCtx) (expr rewritten : YulExpr),
    rule.applyExpr ctx expr = some rewritten →
    eval expr = eval rewritten

/-- Minimal evaluator laws needed to discharge the foundation patch pack. -/
structure FoundationEvaluatorLaws (eval : EvalExpr) : Prop where
  or_zero_right : ∀ lhs, eval (.call "or" [lhs, .lit 0]) = eval lhs
  or_zero_left : ∀ rhs, eval (.call "or" [.lit 0, rhs]) = eval rhs
  xor_zero_right : ∀ lhs, eval (.call "xor" [lhs, .lit 0]) = eval lhs
  xor_zero_left : ∀ rhs, eval (.call "xor" [.lit 0, rhs]) = eval rhs
  and_zero_right : ∀ lhs, eval (.call "and" [lhs, .lit 0]) = eval (.lit 0)
  add_zero_right : ∀ lhs, eval (.call "add" [lhs, .lit 0]) = eval lhs
  add_zero_left : ∀ rhs, eval (.call "add" [.lit 0, rhs]) = eval rhs
  sub_zero_right : ∀ lhs, eval (.call "sub" [lhs, .lit 0]) = eval lhs
  mul_one_right : ∀ lhs, eval (.call "mul" [lhs, .lit 1]) = eval lhs
  mul_one_left : ∀ rhs, eval (.call "mul" [.lit 1, rhs]) = eval rhs
  div_one_right : ∀ lhs, eval (.call "div" [lhs, .lit 1]) = eval lhs
  mod_one_right : ∀ lhs, eval (.call "mod" [lhs, .lit 1]) = eval (.lit 0)

/-- Obligation for `or(x, 0) -> x`. -/
def or_zero_right_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.orZeroRightRule

/-- Obligation for `or(0, x) -> x`. -/
def or_zero_left_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.orZeroLeftRule

/-- Obligation for `xor(x, 0) -> x`. -/
def xor_zero_right_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.xorZeroRightRule

/-- Obligation for `xor(0, x) -> x`. -/
def xor_zero_left_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.xorZeroLeftRule

/-- Obligation for `and(x, 0) -> 0`. -/
def and_zero_right_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.andZeroRightRule

/-- Obligation for `add(x, 0) -> x`. -/
def add_zero_right_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.addZeroRightRule

/-- Obligation for `add(0, x) -> x`. -/
def add_zero_left_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.addZeroLeftRule

/-- Obligation for `sub(x, 0) -> x`. -/
def sub_zero_right_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.subZeroRightRule

/-- Obligation for `mul(x, 1) -> x`. -/
def mul_one_right_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.mulOneRightRule

/-- Obligation for `mul(1, x) -> x`. -/
def mul_one_left_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.mulOneLeftRule

/-- Obligation for `div(x, 1) -> x`. -/
def div_one_right_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.divOneRightRule

/-- Obligation for `mod(x, 1) -> 0`. -/
def mod_one_right_preserves (eval : EvalExpr) : Prop :=
  FoundationEvaluatorLaws eval → ExprPatchPreservesUnder eval Compiler.Yul.modOneRightRule

/-- Registry hook: each shipped foundation patch has an explicit proof obligation. -/
def foundation_patch_pack_obligations (eval : EvalExpr) : Prop :=
  or_zero_right_preserves eval ∧
  or_zero_left_preserves eval ∧
  xor_zero_right_preserves eval ∧
  xor_zero_left_preserves eval ∧
  and_zero_right_preserves eval ∧
  add_zero_right_preserves eval ∧
  add_zero_left_preserves eval ∧
  sub_zero_right_preserves eval ∧
  mul_one_right_preserves eval ∧
  mul_one_left_preserves eval ∧
  div_one_right_preserves eval ∧
  mod_one_right_preserves eval

/-- Placeholder object-level proof hook until object semantics preservation is stated directly.
    External parity packs define their own object-rule obligations using this hook. -/
def ObjectPatchPreserves (_rule : ObjectPatchRule) : Prop :=
  True

end Compiler.Proofs.YulGeneration.PatchRulesProofs
