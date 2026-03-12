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

end Compiler.Proofs.IRGeneration
