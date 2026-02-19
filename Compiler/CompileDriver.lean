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

private def orThrow (r : Except String Unit) : IO Unit :=
  match r with
  | .error err => throw (IO.userError err)
  | .ok () => pure ()

private def writeContract (outDir : String) (contract : IRContract) (libraryPaths : List String) (verbose : Bool) : IO Unit := do
  let yulObj := emitYul contract

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

def compileAll (outDir : String) (verbose : Bool := false) (libraryPaths : List String := []) : IO Unit := do
  IO.FS.createDirAll outDir

  -- Load libraries once for validation messages
  if !libraryPaths.isEmpty then
    if verbose then
      IO.println s!"Loading {libraryPaths.length} external libraries..."

  -- When external libraries are provided, also compile CryptoHash (which
  -- requires linked Poseidon functions).  Without --link the external call
  -- validation would correctly reject it.
  let specs :=
    if libraryPaths.isEmpty then Specs.allSpecs
    else Specs.allSpecs ++ [Specs.cryptoHashSpec]

  for spec in specs do
    let selectors ← computeSelectors spec
    match compile spec selectors with
    | .ok contract =>
      -- Only pass libraries to contracts that declare external functions
      let contractLibs := if spec.externals.isEmpty then [] else libraryPaths
      writeContract outDir contract contractLibs verbose
      if verbose then
        IO.println s!"✓ Compiled {contract.name}"
    | .error err =>
      throw (IO.userError err)
  if verbose then
    IO.println ""
    IO.println "Compilation complete!"
    IO.println s!"Generated {specs.length} contracts in {outDir}"
