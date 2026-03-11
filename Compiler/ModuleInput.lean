import Lean
import Compiler.CompilationModel

namespace Compiler.ModuleInput

open Lean
open Compiler.CompilationModel

/-- Deterministic duplicate detection after canonical module-name parsing. -/
private def findDuplicateModule? (seen : List Name) : List (String × Name) → Option String
  | [] => none
  | (raw, moduleName) :: rest =>
      if moduleName ∈ seen then
        some raw.trim
      else
        findDuplicateModule? (moduleName :: seen) rest

/-- Parse a dotted Lean module name from CLI/manifest input. -/
def parseModuleName (raw : String) : Except String Name := do
  let trimmed := raw.trim
  if trimmed.isEmpty then
    throw "Module name cannot be empty"
  let parts := trimmed.splitOn "."
  if parts.any (·.isEmpty) then
    throw s!"Invalid module name: {raw}"
  pure <| parts.foldl Name.str Name.anonymous

/-- Resolve the default spec constant for a module.

For flattened contract modules like `Contracts.Counter.Counter`, the generated
`verity_contract` declarations still live under `Contracts.Counter`, so the
canonical spec constant is `Contracts.Counter.spec` rather than
`Contracts.Counter.Counter.spec`.
-/
def specNameOfModule (moduleName : Name) : Name :=
  let parts := moduleName.toString.splitOn "."
  let ownerParts :=
    match parts.reverse with
    | leaf :: parent :: rest =>
        if leaf == parent then
          (parent :: rest).reverse
        else
          parts
    | _ => parts
  let owner := ownerParts.foldl Name.str Name.anonymous
  owner ++ `spec

private def manifestLine? (line : String) : Option String :=
  let trimmed := line.trim
  if trimmed.isEmpty || trimmed.startsWith "#" then
    none
  else
    some trimmed

/-- Read module names from a manifest file, preserving manifest order. -/
def readManifestModules (path : System.FilePath) : IO (Except String (List String)) := do
  try
    let text ← IO.FS.readFile path
    pure <| .ok (text.splitOn "\n" |>.filterMap manifestLine?)
  catch e =>
    pure <| .error s!"Failed to read manifest '{path}': {e}"

private unsafe def evalSpecConst
    (env : Environment)
    (opts : Options)
    (specName : Name) : Except String CompilationModel := do
  if !env.contains specName then
    throw s!"Imported modules did not define '{specName}'"
  match unsafe env.evalConstCheck CompilationModel opts
      ``Compiler.CompilationModel.CompilationModel specName with
  | .ok spec => pure spec
  | .error _ =>
      throw s!"Unable to evaluate '{specName}' as Compiler.CompilationModel.CompilationModel"

private def splitPackageSearchRoots : List System.FilePath :=
  [ ".lake/build/lib/lean"
  , "packages/verity-edsl/.lake/build/lib/lean"
  , "packages/verity-compiler/.lake/build/lib/lean"
  , "packages/verity-examples/.lake/build/lib/lean"
  ]

private def existingSplitPackageSearchRoots : IO SearchPath := do
  let mut roots : SearchPath := []
  for path in splitPackageSearchRoots do
    if ← path.isDir then
      roots := roots.concat path
  pure roots

/-- Import modules and evaluate their canonical `<Module>.spec` constants. -/
unsafe def loadSpecsFromModules (moduleNames : List Name) : IO (Except String (List CompilationModel)) := do
  Lean.initSearchPath (← Lean.findSysroot)
  let originalSearchPath ← searchPathRef.get
  let extraSearchRoots ← existingSplitPackageSearchRoots
  searchPathRef.set (originalSearchPath ++ extraSearchRoots)
  try
    let env ← Lean.importModules (moduleNames.toArray.map fun moduleName => { module := moduleName }) {}
    let opts : Options := {}
    pure <| moduleNames.mapM (fun moduleName => evalSpecConst env opts (specNameOfModule moduleName))
  catch e =>
    pure <| .error e.toString
  finally
    searchPathRef.set originalSearchPath

/-- Parse raw module names, reject duplicates, then load their canonical specs. -/
unsafe def loadSpecsFromRawModules (rawModules : List String) : IO (Except String (List CompilationModel)) := do
  match rawModules.mapM (fun raw => do pure (raw, ← parseModuleName raw)) with
  | .error err => pure <| .error err
  | .ok parsedModules =>
      match findDuplicateModule? [] parsedModules with
      | some dup => pure <| .error s!"Duplicate module input: {dup}"
      | none => loadSpecsFromModules (parsedModules.map Prod.snd)

/-- Merge manifest modules and explicit `--module` values, preserving input order. -/
def resolveRawModules
    (manifestPath : Option String)
    (explicitModules : List String) : IO (Except String (List String)) := do
  match manifestPath with
  | none => pure <| .ok explicitModules
  | some path =>
      match ← readManifestModules path with
      | .error err => pure <| .error err
      | .ok manifestModules => pure <| .ok (manifestModules ++ explicitModules)

end Compiler.ModuleInput
