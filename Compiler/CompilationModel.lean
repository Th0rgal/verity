/-
  Compiler.CompilationModel: Declarative compilation-model facade

  This top-level module re-exports the focused CompilationModel submodules.
  Implementation details now live under `Compiler/CompilationModel/*`.
-/
import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.EcmAxiomCollection
import Compiler.CompilationModel.InternalNaming
import Compiler.CompilationModel.LayoutValidation
import Compiler.CompilationModel.MappingWrites
import Compiler.CompilationModel.UsageAnalysis
import Compiler.CompilationModel.ValidationHelpers
import Compiler.CompilationModel.SelectorInteropHelpers
import Compiler.CompilationModel.ExpressionCompile
import Compiler.CompilationModel.Validation
import Compiler.CompilationModel.Compile
import Compiler.CompilationModel.Dispatch
