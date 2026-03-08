import Std
import Compiler.Selector
import Compiler.Codegen
import Compiler.Yul.PrettyPrint
import Compiler.Linker
import Compiler.ABI
import Compiler.ModuleInput
import Compiler.CompilationModel.TrustSurface

open Compiler
open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Selector
open Compiler.Linker

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

private def writeContract
    (outDir : String)
    (contract : IRContract)
    (libraryPaths : List String)
    (verbose : Bool)
    (options : YulEmitOptions) : IO Yul.PatchPassReport := do
  let (yulObj, patchReport) := emitYulWithOptionsReport contract options

  -- Load and link external libraries if provided
  let libraries ← libraryPaths.mapM fun path => do
    if verbose then
      IO.println s!"  Loading library: {path}"
    loadLibrary path

  let allLibFunctions := libraries.flatten

  -- Validate libraries
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
    (specs : List CompilationModel)
    (outDir : String)
    (verbose : Bool)
    (libraryPaths : List String)
    (options : YulEmitOptions)
    (patchReportPath : Option String)
    (trustReportPath : Option String)
    (abiOutDir : Option String) : IO Unit := do
  IO.FS.createDirAll outDir
  match abiOutDir with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()

  -- Load libraries once for validation messages
  if !libraryPaths.isEmpty then
    if verbose then
      IO.println s!"Loading {libraryPaths.length} external libraries..."

  let mut patchRows : List (String × Yul.PatchPassReport) := []
  for spec in specs do
    let selectors ← computeSelectors spec
    match compile spec selectors with
    | .ok contract =>
      -- Only pass libraries to contracts that declare external functions.
      let contractLibs := if spec.externals.isEmpty then [] else libraryPaths
      let patchReport ← writeContract outDir contract contractLibs verbose options
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
  -- Axiom aggregation report (verbose mode)
  if verbose then
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
    IO.println "Proof-status summary:"
    let mut anyForeignStatus := false
    let mut anyUncheckedStatus := false
    for spec in specs do
      let primitives := collectAxiomatizedPrimitives spec
      let provedExternals :=
        (collectUsedExternalAssumptions spec).foldl
          (fun acc ext => if ext.proofStatus == .proved then acc ++ [ext.name] else acc) []
      let assumedExternals :=
        (collectUsedExternalAssumptions spec).foldl
          (fun acc ext => if ext.proofStatus == .assumed then acc ++ [ext.name] else acc) []
      let uncheckedExternals :=
        (collectUsedExternalAssumptions spec).foldl
          (fun acc ext => if ext.proofStatus == .unchecked then acc ++ [ext.name] else acc) []
      let usedModules :=
        spec.functions.flatMap (·.body)
          |>.foldl
            (fun acc stmt =>
              let mods :=
                let rec collectFromStmt : Stmt → List ECM.ExternalCallModule
                  | .ecm mod _ => [mod]
                  | .ite _ thenBr elseBr =>
                      thenBr.flatMap collectFromStmt ++ elseBr.flatMap collectFromStmt
                  | .forEach _ _ body =>
                      body.flatMap collectFromStmt
                  | _ => []
                collectFromStmt stmt
              mods.foldl (fun inner mod => if inner.contains mod then inner else inner ++ [mod]) acc)
            []
      let provedModules := usedModules.foldl
        (fun acc mod => if mod.proofStatus == .proved then acc ++ [mod.name] else acc) []
      let assumedModules := usedModules.foldl
        (fun acc mod => if mod.proofStatus == .assumed then acc ++ [mod.name] else acc) []
      let uncheckedModules := usedModules.foldl
        (fun acc mod => if mod.proofStatus == .unchecked then acc ++ [mod.name] else acc) []
      if !primitives.isEmpty || !provedExternals.isEmpty || !assumedExternals.isEmpty ||
          !uncheckedExternals.isEmpty || !provedModules.isEmpty || !assumedModules.isEmpty ||
          !uncheckedModules.isEmpty then
        anyForeignStatus := true
        IO.println s!"  {spec.name}:"
        if !primitives.isEmpty then
          IO.println s!"    assumed primitives: {String.intercalate ", " primitives}"
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
    IO.println "External assumption report:"
    let mut anyExternalAssumptions := false
    for spec in specs do
      let externals := collectUsedExternalAssumptions spec
      let ecmAxioms := collectEcmAxioms spec
      if !externals.isEmpty || !ecmAxioms.isEmpty then
        anyExternalAssumptions := true
        IO.println s!"  {spec.name}:"
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
      IO.println "  (no linked external assumptions or ECM axioms)"
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
  if verbose then
    IO.println ""
    IO.println "Compilation complete!"
    IO.println s!"Generated {specs.length} contracts in {outDir}"

unsafe def compileModulesWithOptions
    (outDir : String)
    (modules : List String)
    (verbose : Bool := false)
    (libraryPaths : List String := [])
    (options : YulEmitOptions := {})
    (patchReportPath : Option String := none)
    (trustReportPath : Option String := none)
    (abiOutDir : Option String := none) : IO Unit := do
  let specs ←
    match ← Compiler.ModuleInput.loadSpecsFromRawModules modules with
    | .ok specs => pure specs
    | .error err => throw (IO.userError err)
  compileSpecsWithOptions specs outDir verbose libraryPaths options patchReportPath trustReportPath abiOutDir
