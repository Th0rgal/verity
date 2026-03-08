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

/-- Alias for the current generic supported statement fragment witness. -/
abbrev SupportedStmtList := Verity.Core.Free.SupportedStmtList

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
    Verity.Core.Free.execCompiledSupportedStmtList fields init stmts hSupported =
      Verity.Core.Free.execSourceSupportedStmtList fields init stmts hSupported :=
  Verity.Core.Free.compile_supported_stmt_list_direct_semantics fields init stmts hSupported

end Compiler.Proofs.IRGeneration
