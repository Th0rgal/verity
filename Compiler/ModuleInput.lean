import Lean
import Compiler.CompilationModel

namespace Compiler.ModuleInput

open Lean
open Compiler.CompilationModel

/-- Deterministic duplicate detection that preserves the first repeated raw token. -/
private def findDuplicateRaw? (seen : List String) : List String → Option String
  | [] => none
  | raw :: rest =>
      if raw ∈ seen then
        some raw
      else
        findDuplicateRaw? (raw :: seen) rest

/-- Parse a dotted Lean module name from CLI/manifest input. -/
def parseModuleName (raw : String) : Except String Name := do
  let trimmed := raw.trim
  if trimmed.isEmpty then
    throw "Module name cannot be empty"
  let parts := trimmed.splitOn "."
  if parts.any (·.isEmpty) then
    throw s!"Invalid module name: {raw}"
  pure <| parts.foldl Name.str Name.anonymous

/-- Resolve the default `<Module>.spec` constant name. -/
def specNameOfModule (moduleName : Name) : Name :=
  moduleName ++ `spec

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

/-- Import modules and evaluate their canonical `<Module>.spec` constants. -/
unsafe def loadSpecsFromModules (moduleNames : List Name) : IO (Except String (List CompilationModel)) := do
  try
    let env ← Lean.importModules (moduleNames.toArray.map fun moduleName => { module := moduleName }) {}
    let opts : Options := {}
    pure <| moduleNames.mapM (fun moduleName => evalSpecConst env opts (specNameOfModule moduleName))
  catch e =>
    pure <| .error e.toString

/-- Parse raw module names, reject duplicates, then load their canonical specs. -/
unsafe def loadSpecsFromRawModules (rawModules : List String) : IO (Except String (List CompilationModel)) := do
  match findDuplicateRaw? [] rawModules with
  | some dup => pure <| .error s!"Duplicate --module value: {dup}"
  | none =>
      match rawModules.mapM parseModuleName with
      | .error err => pure <| .error err
      | .ok moduleNames => loadSpecsFromModules moduleNames

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
