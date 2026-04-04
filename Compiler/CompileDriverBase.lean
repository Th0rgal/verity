import Std
import Compiler.Selector
import Compiler.CodegenBase
import Compiler.CompileDriverCommon
import Compiler.Yul.PrettyPrint
import Compiler.Linker
import Compiler.ABI
import Compiler.ModuleInput
import Compiler.CompilationModel.LayoutCompatibilityReport
import Compiler.CompilationModel.LayoutReport
import Compiler.CompilationModel.TrustSurface

namespace Compiler.Base

open Compiler.CompilationModel

private def backend : Compiler.CompileDriverCommon.CodegenBackend :=
  { emitYulWithOptionsReport := emitYulWithOptionsReport }

def compileSpecsWithOptions
    (specs : List CompilationModel)
    (outDir : String)
    (verbose : Bool)
    (libraryPaths : List String)
    (options : YulEmitOptions)
    (patchReportPath : Option String)
    (trustReportPath : Option String)
    (assumptionReportPath : Option String)
    (abiOutDir : Option String)
    (circomOutDir : Option String := none)
    (erc7730OutDir : Option String := none)
    (intentSpecs : List (Lean.Name × Verity.Intent.IntentSpec) := [])
    (denyUncheckedDependencies : Bool := false)
    (denyAssumedDependencies : Bool := false)
    (denyAxiomatizedPrimitives : Bool := false)
    (denyLocalObligations : Bool := false)
    (denyLinearMemoryMechanics : Bool := false)
    (denyEventEmission : Bool := false)
    (denyLowLevelMechanics : Bool := false)
    (denyRuntimeIntrospection : Bool := false)
    (denyProxyUpgradeability : Bool := false)
    (layoutReportPath : Option String := none)
    (layoutCompatibilityReportPath : Option String := none)
    (denyLayoutIncompatibility : Bool := false) : IO Unit :=
  Compiler.CompileDriverCommon.compileSpecsWithOptions
    backend specs outDir verbose libraryPaths options patchReportPath trustReportPath assumptionReportPath abiOutDir
    circomOutDir erc7730OutDir intentSpecs
    denyUncheckedDependencies denyAssumedDependencies denyAxiomatizedPrimitives denyLocalObligations denyLinearMemoryMechanics
    denyEventEmission denyLowLevelMechanics denyRuntimeIntrospection denyProxyUpgradeability layoutReportPath
    layoutCompatibilityReportPath denyLayoutIncompatibility

unsafe def compileModulesWithOptions
    (outDir : String)
    (modules : List String)
    (verbose : Bool := false)
    (libraryPaths : List String := [])
    (options : YulEmitOptions := {})
    (patchReportPath : Option String := none)
    (trustReportPath : Option String := none)
    (assumptionReportPath : Option String := none)
    (abiOutDir : Option String := none)
    (circomOutDir : Option String := none)
    (erc7730OutDir : Option String := none)
    (denyUncheckedDependencies : Bool := false)
    (denyAssumedDependencies : Bool := false)
    (denyAxiomatizedPrimitives : Bool := false)
    (denyLocalObligations : Bool := false)
    (denyLinearMemoryMechanics : Bool := false)
    (denyEventEmission : Bool := false)
    (denyLowLevelMechanics : Bool := false)
    (denyRuntimeIntrospection : Bool := false)
    (denyProxyUpgradeability : Bool := false)
    (layoutReportPath : Option String := none)
    (layoutCompatibilityReportPath : Option String := none)
    (denyLayoutIncompatibility : Bool := false) : IO Unit := do
  Compiler.CompileDriverCommon.compileModulesWithOptions
    backend outDir modules verbose libraryPaths options patchReportPath trustReportPath assumptionReportPath
    abiOutDir circomOutDir erc7730OutDir denyUncheckedDependencies denyAssumedDependencies denyAxiomatizedPrimitives denyLocalObligations
    denyLinearMemoryMechanics denyEventEmission denyLowLevelMechanics denyRuntimeIntrospection
    denyProxyUpgradeability layoutReportPath layoutCompatibilityReportPath denyLayoutIncompatibility

end Compiler.Base
