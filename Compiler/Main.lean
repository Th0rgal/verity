import Std
import Compiler.Specs
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
  let outDir := "compiler/yul"
  IO.FS.createDirAll outDir
  for spec in Specs.allSpecs do
    let selectors ← computeSelectors spec
    let contract := compile spec selectors
    writeContract outDir contract
