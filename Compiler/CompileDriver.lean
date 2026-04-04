import Std
import Compiler.Selector
import Compiler.Codegen
import Compiler.CompileDriverCommon
import Compiler.Yul.PrettyPrint
import Compiler.Linker
import Compiler.ABI
import Compiler.ModuleInput
import Compiler.CompilationModel.LayoutCompatibilityReport
import Compiler.CompilationModel.LayoutReport
import Compiler.CompilationModel.TrustSurface

namespace Compiler

open Compiler.CompilationModel

private def backend : Compiler.CompileDriverCommon.CodegenBackend :=
  { emitYulWithOptionsReport := Compiler.emitYulWithOptionsReport }

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
    (denyUncheckedDependencies := denyUncheckedDependencies) (denyAssumedDependencies := denyAssumedDependencies)
    (denyAxiomatizedPrimitives := denyAxiomatizedPrimitives) (denyLocalObligations := denyLocalObligations)
    (denyLinearMemoryMechanics := denyLinearMemoryMechanics) (denyEventEmission := denyEventEmission)
    (denyLowLevelMechanics := denyLowLevelMechanics) (denyRuntimeIntrospection := denyRuntimeIntrospection)
    (denyProxyUpgradeability := denyProxyUpgradeability) (layoutReportPath := layoutReportPath)
    (layoutCompatibilityReportPath := layoutCompatibilityReportPath) (denyLayoutIncompatibility := denyLayoutIncompatibility)

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
    abiOutDir (denyUncheckedDependencies := denyUncheckedDependencies) (denyAssumedDependencies := denyAssumedDependencies)
    (denyAxiomatizedPrimitives := denyAxiomatizedPrimitives) (denyLocalObligations := denyLocalObligations)
    (denyLinearMemoryMechanics := denyLinearMemoryMechanics) (denyEventEmission := denyEventEmission)
    (denyLowLevelMechanics := denyLowLevelMechanics) (denyRuntimeIntrospection := denyRuntimeIntrospection)
    (denyProxyUpgradeability := denyProxyUpgradeability) (layoutReportPath := layoutReportPath)
    (layoutCompatibilityReportPath := layoutCompatibilityReportPath) (denyLayoutIncompatibility := denyLayoutIncompatibility)

end Compiler
