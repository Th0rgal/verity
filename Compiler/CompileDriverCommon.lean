import Std
import Compiler.Selector
import Compiler.ABI
import Compiler.ModuleInput
import Compiler.Yul.PrettyPrint
import Compiler.Linker
import Compiler.CompilationModel.LayoutCompatibilityReport
import Compiler.CompilationModel.LayoutReport
import Compiler.CompilationModel.TrustSurface
import Compiler.CodegenCommon

namespace Compiler.CompileDriverCommon

open Compiler
open Compiler.CompilationModel
open Compiler.Linker
open Compiler.Selector
open Compiler.Yul

abbrev YulEmitOptions := Compiler.CodegenCommon.YulEmitOptions

structure CodegenBackend where
  emitYulWithOptionsReport : IRContract → YulEmitOptions → YulObject × Yul.PatchPassReport

private def orThrow (r : Except String Unit) : IO Unit :=
  match r with
  | .error err => throw (IO.userError err)
  | .ok () => pure ()

private def reportRow (contractName : String) (report : Yul.PatchPassReport) : List String :=
  match report.manifest with
  | [] =>
      [s!"{contractName}\t{report.iterations}\t-\t0\t0\t-"]
  | entries =>
      entries.map (fun entry =>
        s!"{contractName}\t{report.iterations}\t{entry.patchName}\t{entry.matchCount}\t{entry.changedNodes}\t{entry.proofRef}")

private def renderPatchReportTsv (rows : List (String × Yul.PatchPassReport)) : String :=
  let header := "contract\titerations\tpatch_name\tmatch_count\tchanged_nodes\tproof_ref"
  let body := rows.foldr (fun (contractName, report) acc => reportRow contractName report ++ acc) []
  String.intercalate "\n" (header :: body) ++ "\n"

private def parentDir? (path : String) : Option String :=
  match path.splitOn "/" |>.reverse with
  | [] | [_] => none
  | _file :: revParents =>
      let parent := String.intercalate "/" revParents.reverse
      if parent.isEmpty then
        if path.startsWith "/" then some "/" else none
      else
        some parent

private def ensureParentDirExists (path : String) : IO Unit := do
  match parentDir? path with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()

private def writePatchReport (path : String) (rows : List (String × Yul.PatchPassReport)) : IO Unit := do
  ensureParentDirExists path
  IO.FS.writeFile path (renderPatchReportTsv rows)

private def writeTrustReport (path : String) (specs : List CompilationModel) : IO Unit := do
  ensureParentDirExists path
  IO.FS.writeFile path (emitTrustReportJson specs ++ "\n")

private def writeAssumptionReport (path : String) (specs : List CompilationModel) : IO Unit := do
  ensureParentDirExists path
  IO.FS.writeFile path (emitAssumptionReportJson specs ++ "\n")

private def writeLayoutReport (path : String) (specs : List CompilationModel) : IO Unit := do
  ensureParentDirExists path
  IO.FS.writeFile path (emitLayoutReportJson specs ++ "\n")

private def requireLayoutCompatibilityPair
    (specs : List CompilationModel) : IO (CompilationModel × CompilationModel) :=
  match specs with
  | [baseline, candidate] => pure (baseline, candidate)
  | _ =>
      throw (IO.userError
        "Layout compatibility comparison requires exactly 2 selected contracts (baseline first, candidate second)")

private def writeLayoutCompatibilityReport
    (path : String)
    (specs : List CompilationModel) : IO Unit := do
  let (baseline, candidate) ← requireLayoutCompatibilityPair specs
  ensureParentDirExists path
  IO.FS.writeFile path (emitLayoutCompatibilityReportJson baseline candidate ++ "\n")

private def ensureNoUncheckedDependencies (specs : List CompilationModel) : IO Unit := do
  let uncheckedSites := emitUncheckedUsageSiteLines specs
  if !uncheckedSites.isEmpty then
    throw (IO.userError
      s!"Unchecked foreign dependencies remain:\n{String.intercalate "\n" uncheckedSites}")

private def ensureNoAssumedDependencies (specs : List CompilationModel) : IO Unit := do
  let assumedSites := emitAssumedUsageSiteLines specs
  if !assumedSites.isEmpty then
    throw (IO.userError
      s!"Assumed or unchecked foreign dependencies remain:\n{String.intercalate "\n" assumedSites}")

private def ensureNoAxiomatizedPrimitives (specs : List CompilationModel) : IO Unit := do
  let primitiveSites := emitAxiomatizedPrimitiveUsageSiteLines specs
  if !primitiveSites.isEmpty then
    throw (IO.userError
      s!"Axiomatized primitives remain:\n{String.intercalate "\n" primitiveSites}")

private def ensureNoLocalObligations (specs : List CompilationModel) : IO Unit := do
  let localObligationSites := emitLocalObligationUsageSiteLines specs
  if !localObligationSites.isEmpty then
    throw (IO.userError
      s!"Undischarged local obligations remain:\n{String.intercalate "\n" localObligationSites}")

private def ensureNoLinearMemoryMechanics (specs : List CompilationModel) : IO Unit := do
  let linearMemorySites := emitLinearMemoryUsageSiteLines specs
  if !linearMemorySites.isEmpty then
    throw (IO.userError
      s!"Partially modeled linear-memory mechanics remain:\n{String.intercalate "\n" linearMemorySites}")

private def ensureNoEventEmission (specs : List CompilationModel) : IO Unit := do
  let eventEmissionSites := emitEventEmissionUsageSiteLines specs
  if !eventEmissionSites.isEmpty then
    throw (IO.userError
      s!"Not-modeled event emission remains:\n{String.intercalate "\n" eventEmissionSites}")

private def ensureNoProxyUpgradeability (specs : List CompilationModel) : IO Unit := do
  let proxySites := emitProxyUpgradeabilityUsageSiteLines specs
  if !proxySites.isEmpty then
    throw (IO.userError
      s!"Not-modeled proxy / upgradeability mechanics remain:\n{String.intercalate "\n" proxySites}")

private def ensureNoRuntimeIntrospection (specs : List CompilationModel) : IO Unit := do
  let runtimeIntrospectionSites := emitRuntimeIntrospectionUsageSiteLines specs
  if !runtimeIntrospectionSites.isEmpty then
    throw (IO.userError
      s!"Partially modeled runtime-introspection mechanics remain:\n{String.intercalate "\n" runtimeIntrospectionSites}")

private def ensureNoLowLevelMechanics (specs : List CompilationModel) : IO Unit := do
  let lowLevelSites := emitLowLevelMechanicsUsageSiteLines specs
  if !lowLevelSites.isEmpty then
    throw (IO.userError
      s!"Low-level mechanics remain:\n{String.intercalate "\n" lowLevelSites}")

private def ensureLayoutCompatible (specs : List CompilationModel) : IO Unit := do
  let (baseline, candidate) ← requireLayoutCompatibilityPair specs
  let incompatibilities := emitIncompatibleLayoutChangeLines baseline candidate
  if !incompatibilities.isEmpty then
    throw (IO.userError
      s!"Layout incompatibilities remain:\n{String.intercalate "\n" incompatibilities}")

private def writeContract
    (backend : CodegenBackend)
    (outDir : String)
    (contract : IRContract)
    (libraryPaths : List String)
    (verbose : Bool)
    (options : YulEmitOptions) : IO Yul.PatchPassReport := do
  let (yulObj, patchReport) := backend.emitYulWithOptionsReport contract options

  let libraries ← libraryPaths.mapM fun path => do
    if verbose then
      IO.println s!"  Loading library: {path}"
    loadLibrary path

  let allLibFunctions := libraries.flatten
  if !allLibFunctions.isEmpty then
    orThrow (validateNoDuplicateNames allLibFunctions)
    orThrow (validateNoNameCollisions yulObj allLibFunctions)
  orThrow (validateExternalReferences yulObj allLibFunctions)
  if !allLibFunctions.isEmpty then
    orThrow (validateCallArity yulObj allLibFunctions)

  let text ←
    if allLibFunctions.isEmpty then
      pure (Yul.render yulObj)
    else
      match renderWithLibraries yulObj allLibFunctions with
      | .error err => throw (IO.userError err)
      | .ok rendered => pure rendered

  let path := s!"{outDir}/{contract.name}.yul"
  IO.FS.writeFile path text
  pure patchReport

def compileSpecsWithOptions
    (backend : CodegenBackend)
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
    (denyLayoutIncompatibility : Bool := false) : IO Unit := do
  IO.FS.createDirAll outDir
  match abiOutDir with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()

  if !libraryPaths.isEmpty then
    if verbose then
      IO.println s!"Loading {libraryPaths.length} external libraries..."

  let mut patchRows : List (String × Yul.PatchPassReport) := []
  for spec in specs do
    let selectors ← computeSelectors spec
    match compile spec selectors with
    | .ok contract =>
        let contractLibs := if spec.externals.isEmpty then [] else libraryPaths
        let patchReport ← writeContract backend outDir contract contractLibs verbose options
        match abiOutDir with
        | some dir =>
            Compiler.ABI.writeContractABIFile dir spec
            if verbose then
              IO.println s!"✓ Wrote ABI {dir}/{spec.name}.abi.json"
        | none => pure ()
        patchRows := (contract.name, patchReport) :: patchRows
        if verbose then
          IO.println s!"✓ Compiled {contract.name}"
    | .error err =>
        throw (IO.userError err)
  match patchReportPath with
  | some path =>
      writePatchReport path patchRows.reverse
      if verbose then
        IO.println s!"✓ Wrote patch report: {path}"
  | none => pure ()
  match trustReportPath with
  | some path =>
      writeTrustReport path specs
      if verbose then
        IO.println s!"✓ Wrote trust report: {path}"
  | none => pure ()
  match assumptionReportPath with
  | some path =>
      writeAssumptionReport path specs
      if verbose then
        IO.println s!"✓ Wrote assumption report: {path}"
  | none => pure ()
  match layoutReportPath with
  | some path =>
      writeLayoutReport path specs
      if verbose then
        IO.println s!"✓ Wrote layout report: {path}"
  | none => pure ()
  match layoutCompatibilityReportPath with
  | some path =>
      writeLayoutCompatibilityReport path specs
      if verbose then
        IO.println s!"✓ Wrote layout compatibility report: {path}"
  | none => pure ()
  if denyLocalObligations then
    ensureNoLocalObligations specs
  if denyAxiomatizedPrimitives then
    ensureNoAxiomatizedPrimitives specs
  if denyLinearMemoryMechanics then
    ensureNoLinearMemoryMechanics specs
  if denyEventEmission then
    ensureNoEventEmission specs
  if denyLowLevelMechanics then
    ensureNoLowLevelMechanics specs
  if denyRuntimeIntrospection then
    ensureNoRuntimeIntrospection specs
  if denyProxyUpgradeability then
    ensureNoProxyUpgradeability specs
  if denyLayoutIncompatibility then
    ensureLayoutCompatible specs
  if denyAssumedDependencies then
    ensureNoAssumedDependencies specs
  if denyUncheckedDependencies then
    ensureNoUncheckedDependencies specs
  if verbose then
    IO.println ""
    IO.println "Linear memory mechanics report:"
    let mut anyLinearMemory := false
    for spec in specs do
      let mechanics := collectLinearMemoryMechanics spec
      if !mechanics.isEmpty then
        anyLinearMemory := true
        IO.println s!"  {spec.name}: {String.intercalate ", " mechanics}"
    if !anyLinearMemory then
      IO.println "  (no partially modeled linear-memory primitives used)"
    IO.println "  Proof boundary: these mechanics rely on linear memory / ABI movement that is still only partially modeled by current proof interpreters."
    IO.println ""
    IO.println "Event-emission report:"
    let mut anyEventEmission := false
    for spec in specs do
      let mechanics := collectEventEmissionMechanics spec
      if !mechanics.isEmpty then
        anyEventEmission := true
        IO.println s!"  {spec.name}: {String.intercalate ", " mechanics}"
    if !anyEventEmission then
      IO.println "  (no raw event-emission primitives used)"
    IO.println "  Proof boundary: raw LOG-style event emission is compiler-supported, but current proof interpreters still treat `rawLog` as a not-modeled feature."
    IO.println ""
    IO.println "Proxy / upgradeability report:"
    let mut anyProxyUpgradeability := false
    for spec in specs do
      let mechanics := collectProxyUpgradeabilityMechanics spec
      if !mechanics.isEmpty then
        anyProxyUpgradeability := true
        IO.println s!"  {spec.name}: {String.intercalate ", " mechanics}"
    if !anyProxyUpgradeability then
      IO.println "  (no proxy / upgradeability mechanics used)"
    IO.println "  Proof boundary: `delegatecall` still lacks native proxy / upgradeability semantics in the proof interpreters; treat these sites as explicit trust boundaries tracked under issue #1420."
    IO.println ""
    IO.println "Runtime introspection report:"
    let mut anyRuntimeIntrospection := false
    for spec in specs do
      let mechanics := collectRuntimeIntrospectionMechanics spec
      if !mechanics.isEmpty then
        anyRuntimeIntrospection := true
        IO.println s!"  {spec.name}: {String.intercalate ", " mechanics}"
    if !anyRuntimeIntrospection then
      IO.println "  (no partially modeled runtime-introspection primitives used)"
    IO.println "  Proof boundary: these context-sensitive primitives are compiler-supported, but current proof interpreters still model them only partially."
    IO.println ""
    IO.println "Low-level mechanics report:"
    let mut anyMechanics := false
    for spec in specs do
      let mechanics := collectLowLevelMechanics spec
      if !mechanics.isEmpty then
        anyMechanics := true
        IO.println s!"  {spec.name}: {String.intercalate ", " mechanics}"
    if !anyMechanics then
      IO.println "  (no first-class low-level call or returndata primitives used)"
    IO.println "  Proof boundary: mechanics are lowered natively by the compiler; current proof interpreters do not model these primitives, and callee behavior remains assumption-backed unless discharged separately."
    IO.println ""
    IO.println "Axiomatized primitive report:"
    let mut anyAxiomatized := false
    for spec in specs do
      let primitives := collectAxiomatizedPrimitives spec
      if !primitives.isEmpty then
        anyAxiomatized := true
        IO.println s!"  {spec.name}: {String.intercalate ", " primitives}"
    if !anyAxiomatized then
      IO.println "  (no axiomatized primitives used)"
    IO.println "  Proof boundary: these primitives compile through explicit trusted boundaries (for example, keccak-backed hashing) and should be audited alongside AXIOMS.md/TRUST_ASSUMPTIONS.md."
    IO.println ""
    IO.println "Local obligation report:"
    let mut anyLocalObligations := false
    for spec in specs do
      let obligations := collectLocalObligations spec
      if !obligations.isEmpty then
        anyLocalObligations := true
        IO.println s!"  {spec.name}:"
        for obligation in obligations do
          IO.println s!"    [{obligation.proofStatus.toJsonString}] {obligation.name}: {obligation.obligation}"
    if !anyLocalObligations then
      IO.println "  (no local unsafe/refinement obligations declared)"
    IO.println "  Proof boundary: local obligations isolate unsafe/assembly-shaped trust boundaries to one usage site and can later be discharged from `assumed`/`unchecked` to `proved`."
    IO.println ""
    IO.println "Proof-status summary:"
    let mut anyForeignStatus := false
    let mut anyUncheckedStatus := false
    for spec in specs do
      let primitives := collectAxiomatizedPrimitives spec
      let provedLocalObligations :=
        (collectLocalObligations spec).foldl
          (fun acc obligation => if obligation.proofStatus == .proved then acc ++ [obligation.name] else acc) []
      let assumedLocalObligations :=
        (collectLocalObligations spec).foldl
          (fun acc obligation => if obligation.proofStatus == .assumed then acc ++ [obligation.name] else acc) []
      let uncheckedLocalObligations :=
        (collectLocalObligations spec).foldl
          (fun acc obligation => if obligation.proofStatus == .unchecked then acc ++ [obligation.name] else acc) []
      let provedExternals :=
        (collectUsedExternalAssumptions spec).foldl
          (fun acc ext => if ext.proofStatus == .proved then acc ++ [ext.name] else acc) []
      let assumedExternals :=
        (collectUsedExternalAssumptions spec).foldl
          (fun acc ext => if ext.proofStatus == .assumed then acc ++ [ext.name] else acc) []
      let uncheckedExternals :=
        (collectUsedExternalAssumptions spec).foldl
          (fun acc ext => if ext.proofStatus == .unchecked then acc ++ [ext.name] else acc) []
      let usedModules := collectUsedEcmModules spec
      let provedModules := usedModules.foldl
        (fun acc mod => if mod.proofStatus == .proved then acc ++ [mod.name] else acc) []
      let assumedModules := usedModules.foldl
        (fun acc mod => if mod.proofStatus == .assumed then acc ++ [mod.name] else acc) []
      let uncheckedModules := usedModules.foldl
        (fun acc mod => if mod.proofStatus == .unchecked then acc ++ [mod.name] else acc) []
      if !primitives.isEmpty || !provedLocalObligations.isEmpty || !assumedLocalObligations.isEmpty ||
          !uncheckedLocalObligations.isEmpty || !provedExternals.isEmpty || !assumedExternals.isEmpty ||
          !uncheckedExternals.isEmpty || !provedModules.isEmpty || !assumedModules.isEmpty ||
          !uncheckedModules.isEmpty then
        anyForeignStatus := true
        IO.println s!"  {spec.name}:"
        if !primitives.isEmpty then
          IO.println s!"    assumed primitives: {String.intercalate ", " primitives}"
        if !provedLocalObligations.isEmpty then
          IO.println s!"    proved local obligations: {String.intercalate ", " provedLocalObligations}"
        if !assumedLocalObligations.isEmpty then
          IO.println s!"    assumed local obligations: {String.intercalate ", " assumedLocalObligations}"
        if !uncheckedLocalObligations.isEmpty then
          anyUncheckedStatus := true
          IO.println s!"    unchecked local obligations: {String.intercalate ", " uncheckedLocalObligations}"
        if !provedExternals.isEmpty then
          IO.println s!"    proved linked externals: {String.intercalate ", " provedExternals}"
        if !assumedExternals.isEmpty then
          IO.println s!"    assumed linked externals: {String.intercalate ", " assumedExternals}"
        if !uncheckedExternals.isEmpty then
          anyUncheckedStatus := true
          IO.println s!"    unchecked linked externals: {String.intercalate ", " uncheckedExternals}"
        if !provedModules.isEmpty then
          IO.println s!"    proved ECM modules: {String.intercalate ", " provedModules}"
        if !assumedModules.isEmpty then
          IO.println s!"    assumed ECM modules: {String.intercalate ", " assumedModules}"
        if !uncheckedModules.isEmpty then
          anyUncheckedStatus := true
          IO.println s!"    unchecked ECM modules: {String.intercalate ", " uncheckedModules}"
    if !anyForeignStatus then
      IO.println "  proved: none"
      IO.println "  assumed: none"
      IO.println "  unchecked: none"
    else if !anyUncheckedStatus then
      IO.println "  unchecked: none reported"
    else
      IO.println "  warning: unchecked foreign dependencies are present; exclude these contracts from full-verification claims"
    IO.println ""
    IO.println "Usage-site trust report:"
    let usageSiteLines := emitVerboseUsageSiteLines specs
    if usageSiteLines.isEmpty then
      IO.println "  (no localized trust surfaces)"
    else
      for line in usageSiteLines do
        IO.println line
    IO.println ""
    IO.println "External assumption report:"
    let mut anyExternalAssumptions := false
    for spec in specs do
      let primitiveAssumptions := collectAxiomatizedPrimitives spec
      let externals := collectUsedExternalAssumptions spec
      let ecmAxioms := collectEcmAxioms spec
      if !primitiveAssumptions.isEmpty || !externals.isEmpty || !ecmAxioms.isEmpty then
        anyExternalAssumptions := true
        IO.println s!"  {spec.name}:"
        if !primitiveAssumptions.isEmpty then
          for primitive in primitiveAssumptions do
            IO.println
              s!"    [primitive:{primitive}][assumed] {primitiveAssumptionName primitive}"
        if !externals.isEmpty then
          for ext in externals do
            let renderedAxioms :=
              if ext.axiomNames.isEmpty then "(no declared axioms)"
              else String.intercalate ", " ext.axiomNames
            IO.println s!"    [linked:{ext.name}][{ext.proofStatus.toJsonString}] {renderedAxioms}"
        if !ecmAxioms.isEmpty then
          for (modName, assumption) in ecmAxioms do
            IO.println s!"    [ecm:{modName}] {assumption}"
    if !anyExternalAssumptions then
      IO.println "  (no primitive assumptions, linked external assumptions, or ECM axioms)"
    IO.println ""
    IO.println "ECM axiom report:"
    let mut anyAxioms := false
    for spec in specs do
      let axioms := collectEcmAxioms spec
      if !axioms.isEmpty then
        anyAxioms := true
        IO.println s!"  {spec.name}:"
        for (modName, assumption) in axioms do
          IO.println s!"    [{modName}] {assumption}"
    if !anyAxioms then
      IO.println "  (no ECM axioms — no external call modules used)"
    IO.println ""
    IO.println "Compilation complete!"
    IO.println s!"Generated {specs.length} contracts in {outDir}"

unsafe def compileModulesWithOptions
    (backend : CodegenBackend)
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
  let specs ←
    match ← Compiler.ModuleInput.loadSpecsFromRawModules modules with
    | .ok specs => pure specs
    | .error err => throw (IO.userError err)
  compileSpecsWithOptions
    backend specs outDir verbose libraryPaths options patchReportPath trustReportPath assumptionReportPath abiOutDir
    denyUncheckedDependencies denyAssumedDependencies denyAxiomatizedPrimitives denyLocalObligations denyLinearMemoryMechanics
    denyEventEmission denyLowLevelMechanics denyRuntimeIntrospection denyProxyUpgradeability layoutReportPath
    layoutCompatibilityReportPath denyLayoutIncompatibility

end Compiler.CompileDriverCommon
