import Contracts
import Compiler.ModuleInput

namespace Compiler.ModuleInputTest

open Lean
open Compiler.ModuleInput

private def expectErrorEq (label : String) (actual : Except String α) (expected : String) : IO Unit := do
  match actual with
  | .ok _ => throw <| IO.userError s!"✗ {label}: expected error '{expected}', got success"
  | .error err =>
      if err != expected then
        throw <| IO.userError s!"✗ {label}: expected '{expected}', got '{err}'"
      IO.println s!"✓ {label}"

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw <| IO.userError s!"✗ {label}"
  IO.println s!"✓ {label}"

unsafe def runTests : IO Unit := do
  let dupWhitespace ← loadSpecsFromRawModules
    ["Contracts.Counter.Counter", "  Contracts.Counter.Counter  "]
  expectErrorEq
    "whitespace-normalized duplicate module inputs are rejected"
    dupWhitespace
    "Duplicate module input: Contracts.Counter.Counter"

  let nonce ← IO.monoMsNow
  let manifestPath := s!"/tmp/verity-module-input-test-{nonce}.manifest"
  IO.FS.writeFile manifestPath "# comment\n  Contracts.Counter.Counter  \n"
  let resolved ← resolveRawModules (some manifestPath) ["Contracts.Counter.Counter"]
  match resolved with
  | .ok rawModules =>
      if rawModules != ["Contracts.Counter.Counter", "Contracts.Counter.Counter"] then
        throw <| IO.userError
          s!"✗ manifest modules preserve trimmed entries before duplicate detection: got {rawModules}"
      IO.println "✓ manifest modules preserve trimmed entries before duplicate detection"
  | .error err =>
      throw <| IO.userError
        s!"✗ manifest modules preserve trimmed entries before duplicate detection: got error '{err}'"
  let dupManifest ←
    match resolved with
    | .ok rawModules => loadSpecsFromRawModules rawModules
    | .error err => pure <| .error err
  expectErrorEq
    "manifest and explicit module duplicates are rejected after canonical parsing"
    dupManifest
    "Duplicate module input: Contracts.Counter.Counter"

  let originalSearchPath ← searchPathRef.get
  let loadedSpecs ← loadSpecsFromRawModules ["Contracts.Counter.Counter"]
  match loadedSpecs with
  | .ok specs =>
      expectTrue
        "module loader imports contracts from split package build outputs"
        (specs.length == 1)
  | .error err =>
      throw <| IO.userError
        s!"✗ module loader imports contracts from split package build outputs: got error '{err}'"
  let restoredSearchPath ← searchPathRef.get
  expectTrue
    "module loader restores Lean search path after dynamic imports"
    (restoredSearchPath == originalSearchPath)

#eval! runTests

end Compiler.ModuleInputTest
