import Compiler.TypedIRCompilerCorrectness

/-!
Current generic Layer-2 theorem surface for the supported statement fragment.

This module does not prove generic `CompilationModel.compile` correctness for
arbitrary specs. It exposes the existing structural theorem from
`Compiler.TypedIRCompilerCorrectness` under the compiler-proof namespace so the
current generic boundary is explicit and documented where Layer 2 proofs live.
-/

namespace Compiler.Proofs.IRGeneration

open Verity.Core.Free

/-- Proof-layer compositional witness for lists assembled from the legacy
supported statement fragments. This removes the raw existential list encoding
from the public IR-generation interfaces while staying definitionally aligned
with the current core fragment inventory. -/
inductive SupportedStmtList (fields : List CompilationModel.Field) : List CompilationModel.Stmt → Prop where
  | nil : SupportedStmtList fields []
  | cons
      (fragment : SupportedStmtFragment fields)
      {rest : List CompilationModel.Stmt} :
      SupportedStmtList fields rest →
      SupportedStmtList fields (fragment.toStmts ++ rest)

theorem SupportedStmtList.toLegacy
    {fields : List CompilationModel.Field}
    {stmts : List CompilationModel.Stmt}
    (hSupported : SupportedStmtList fields stmts) :
    Verity.Core.Free.SupportedStmtList fields stmts := by
  induction hSupported with
  | nil =>
      refine ⟨[], by simp [Verity.Core.Free.supportedStmtFragmentsToStmts]⟩
  | @cons fragment rest htail ih =>
      rcases ih with ⟨fragments, hfragments⟩
      refine ⟨fragment :: fragments, ?_⟩
      simp [Verity.Core.Free.supportedStmtFragmentsToStmts, hfragments]

/-- Current generic Layer-2 theorem: for any raw statement list admitted by the
supported statement fragment witness, the compiled and source semantics agree.

This is the reusable structural theorem available today. It is narrower than a
future whole-contract `CompilationModel.compile` theorem because it ranges over
statement lists plus an explicit `SupportedStmtList` witness, rather than over
arbitrary `CompilationModel` values and dispatch compilation. -/
theorem supported_stmt_list_preserves_semantics
    (fields : List CompilationModel.Field)
    (init : TExecState)
    (stmts : List CompilationModel.Stmt)
    (hSupported : SupportedStmtList fields stmts) :
    Verity.Core.Free.execCompiledSupportedStmtList fields init stmts hSupported.toLegacy =
      Verity.Core.Free.execSourceSupportedStmtList fields init stmts hSupported.toLegacy :=
  Verity.Core.Free.compile_supported_stmt_list_direct_semantics fields init stmts
    hSupported.toLegacy

end Compiler.Proofs.IRGeneration
