import Compiler.CompilationModel

namespace Compiler.Lowering

open Compiler.CompilationModel

/-- Explicit core input artifact for the compiler lowering boundary.
Today this wraps `CompilationModel`; the CLI exposes only the EDSL-driven path. -/
structure ContractCore where
  model : CompilationModel
  deriving Repr

/-- Deterministic diagnostics for unsupported EDSL-input lowering. -/
inductive LoweringError where
  | unsupported (details : String)
  deriving Repr

def LoweringError.message : LoweringError → String
  | .unsupported details =>
      "Unsupported EDSL lowering input. " ++
      "Use the generalized EDSL/macro path for compiler input. " ++
      details

/-- Helper: embed compiler-facing contract data into the lowering boundary. -/
def liftModel (model : CompilationModel) : ContractCore :=
  { model := model }

/-- Lower core compiler input to `CompilationModel`.
For the current stage this is structurally the wrapped model. -/
def lowerContractCore (core : ContractCore) : CompilationModel :=
  core.model

def findDuplicateRawContract? (seen : List String) (remaining : List String) : Option String :=
  match remaining with
  | [] => none
  | raw :: rest =>
      if raw ∈ seen then
        some raw
      else
        findDuplicateRawContract? (raw :: seen) rest

/-- Lowering path routed through the shared lowering boundary. -/
def lowerModelPath (model : CompilationModel) : Except LoweringError CompilationModel :=
  .ok (lowerContractCore (liftModel model))

def edslInputReservedMessage : String :=
  LoweringError.message (.unsupported "(pending extended verified EDSL elaboration/lowering)")

end Compiler.Lowering
