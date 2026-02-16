import Std
import Compiler.Specs
import Compiler.ContractSpec
import Compiler.Selector
import Compiler.Codegen
import Compiler.Yul.PrettyPrint
import Compiler.Linker

open Compiler
open Compiler.Yul
open Compiler.ContractSpec
open Compiler.Selector
open Compiler.Linker

private def writeContract (outDir : String) (contract : IRContract) (libraryPaths : List String) : IO Unit := do
  let yulObj := emitYul contract

  -- Load and link external libraries if provided
  let libraries ← libraryPaths.mapM fun path => do
    if verbose then
      IO.println s!"  Loading library: {path}"
    loadLibrary path

  let allLibFunctions := libraries.flatten

  -- Validate: no duplicate function names across libraries
  if !allLibFunctions.isEmpty then
    match validateNoDuplicateNames allLibFunctions with
    | .error err => throw (IO.userError err)
    | .ok () => pure ()

  -- Validate: all external calls in the contract are provided by libraries
  match validateExternalReferences yulObj allLibFunctions with
  | .error err => throw (IO.userError err)
  | .ok () => pure ()

  let text :=
    if allLibFunctions.isEmpty then
      Yul.render yulObj
    else
      renderWithLibraries yulObj allLibFunctions

  let path := s!"{outDir}/{contract.name}.yul"
  IO.FS.writeFile path text
where
  verbose := false  -- Can be parameterized later

def compileAll (outDir : String) (verbose : Bool := false) (libraryPaths : List String := []) : IO Unit := do
  IO.FS.createDirAll outDir

  -- Load libraries once for validation messages
  if !libraryPaths.isEmpty then
    if verbose then
      IO.println s!"Loading {libraryPaths.length} external libraries..."

  for spec in Specs.allSpecs do
    let selectors ← computeSelectors spec
    match compile spec selectors with
    | .ok contract =>
      writeContract outDir contract libraryPaths
      if verbose then
        IO.println s!"✓ Compiled {contract.name}"
    | .error err =>
      throw (IO.userError err)
  if verbose then
    IO.println ""
    IO.println "Compilation complete!"
    IO.println s!"Generated {Specs.allSpecs.length} contracts in {outDir}"
