import Compiler.CodegenCommon
import Compiler.Yul.PatchRules

namespace Compiler

open Yul

abbrev BackendProfile := Compiler.CodegenCommon.BackendProfile
abbrev YulEmitOptions := Compiler.CodegenCommon.YulEmitOptions

def mappingSlotFuncAt := Compiler.CodegenCommon.mappingSlotFuncAt
def callvalueGuard := Compiler.CodegenCommon.callvalueGuard
def calldatasizeGuard := Compiler.CodegenCommon.calldatasizeGuard
def dispatchBody := Compiler.CodegenCommon.dispatchBody
def defaultDispatchCase := Compiler.CodegenCommon.defaultDispatchCase
def buildSwitch := Compiler.CodegenCommon.buildSwitch
def runtimeCode := Compiler.CodegenCommon.runtimeCode
def emitYul := Compiler.CodegenCommon.emitYul

private def patchBackend : Compiler.CodegenCommon.PatchBackend :=
  { apply := fun base options =>
      let rewriteBundle := Yul.rewriteBundleForId options.patchConfig.rewriteBundleId
      let requiredProofRefs :=
        if options.patchConfig.requiredProofRefs.isEmpty then
          Yul.rewriteProofAllowlistForId rewriteBundle.id
        else
          options.patchConfig.requiredProofRefs
      let patchConfig :=
        { options.patchConfig with
          requiredProofRefs := requiredProofRefs }
      let runtimePatchReport := Yul.runPatchPassWithBlocks
        patchConfig
        rewriteBundle.exprRules
        rewriteBundle.stmtRules
        rewriteBundle.blockRules
        base.runtimeCode
      let runtimePatched := { base with runtimeCode := runtimePatchReport.patched }
      let objectReport := Yul.runPatchPassWithObjects
        patchConfig
        []
        []
        []
        rewriteBundle.objectRules
        runtimePatched
      let mergedPatchReport : Yul.PatchPassReport :=
        { patched := objectReport.patched.runtimeCode
          iterations := runtimePatchReport.iterations + objectReport.iterations
          manifest := runtimePatchReport.manifest ++ objectReport.manifest }
      { patched := objectReport.patched
        patchReport := mergedPatchReport } }

def emitYulWithOptions (contract : IRContract) (options : YulEmitOptions) : YulObject :=
  Compiler.CodegenCommon.emitYulWithOptions patchBackend contract options

def emitYulWithOptionsReport (contract : IRContract) (options : YulEmitOptions) :
    YulObject × Yul.PatchPassReport :=
  Compiler.CodegenCommon.emitYulWithOptionsReport patchBackend contract options

/-- Regression guard:
    expression/statement/block patching remains runtime-scoped (deploy is unchanged),
    and runtime patch reporting excludes deploy-only candidates. -/
example :
    let deployMarker := "__deploy_marker"
    let runtimeMarker := "__runtime_marker"
    let contract : IRContract :=
      { name := "ScopeRegression"
        deploy := [.expr (.call "add" [.ident deployMarker, .lit 0])]
        constructorPayable := true
        functions :=
          [{ name := "f"
             selector := 1
             params := []
             ret := .unit
             payable := false
             body := [.expr (.call "add" [.ident runtimeMarker, .lit 0])] }]
        usesMapping := false }
    let options : YulEmitOptions := { patchConfig := { enabled := true, maxIterations := 2 } }
    let report := emitYulWithOptionsReport contract options
    let rendered := Yul.render report.1
    let deployStillHasMarker := Compiler.CodegenCommon.contains rendered s!"add({deployMarker}, 0)"
    let runtimeNoLongerHasMarker := !(Compiler.CodegenCommon.contains rendered s!"add({runtimeMarker}, 0)")
    let runtimeMatchCount :=
      report.2.manifest.foldl
        (fun acc entry =>
          if entry.patchName = "add-zero-right" then acc + entry.matchCount else acc)
        0
    deployStillHasMarker && runtimeNoLongerHasMarker && runtimeMatchCount == 1 := by
  native_decide

/-- Regression guard: active `solc-compat` object rewrites are included in emitted patch report manifests. -/
example :
    let contract : IRContract :=
      { name := "ObjectManifestRegression"
        deploy := []
        constructorPayable := true
        functions :=
          [{ name := "f"
             selector := 1
             params := []
             ret := .unit
             payable := false
             body := [.expr (.call "liveHelper" [])] }]
        usesMapping := false
        internalFunctions :=
          [ .funcDef "liveHelper" [] [] [.leave]
          , .funcDef "mappingSlot" ["baseSlot", "key"] ["slot"]
              [ .expr (.call "mstore" [.lit 512, .ident "key"])
              , .expr (.call "mstore" [.lit 544, .ident "baseSlot"])
              , .assign "slot" (.call "keccak256" [.lit 512, .lit 64])
              ]
          ] }
    let options : YulEmitOptions :=
      { patchConfig :=
          { enabled := true
            maxIterations := 6
            rewriteBundleId := Yul.solcCompatRewriteBundleId
            requiredProofRefs := Yul.solcCompatProofAllowlist } }
    let report := emitYulWithOptionsReport contract options
    let hasMappingDropRule :=
      report.2.manifest.any (fun entry => entry.patchName = "solc-compat-drop-unused-mapping-slot-helper")
    hasMappingDropRule = true := by
  native_decide

end Compiler
