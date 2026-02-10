/-
  Compiler.MainNew: New automatic compilation system

  This demonstrates the new declarative contract specification system.
  Contracts are specified once and compiled automatically.
-/

import Std
import Compiler.Specs      -- New system
import Compiler.ContractSpec
import Compiler.Selector
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

open Compiler
open Compiler.Yul
open Compiler.ContractSpec
open Compiler.Selector

private def writeContract (outDir : String) (contract : IRContract) : IO Unit := do
  let yulObj := emitYul contract
  let text := Yul.render yulObj
  let path := s!"{outDir}/{contract.name}.yul"
  IO.FS.writeFile path text

def main : IO Unit := do
  let outDir := "compiler/yul-new"
  IO.FS.createDirAll outDir

  -- Compile contracts from new spec system
  for spec in Specs.allSpecs do
    let selectors ← computeSelectors spec
    let contract := compile spec selectors
    writeContract outDir contract
    IO.println s!"✓ Compiled {contract.name} (new system)"

  IO.println ""
  IO.println "New compilation complete!"
  IO.println s!"Generated {Specs.allSpecs.length} contracts in {outDir}"
