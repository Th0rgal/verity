import Std
import Compiler.Translate
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

open Compiler
open Compiler.Yul

private def writeContract (outDir : String) (contract : IRContract) : IO Unit := do
  let yulObj := emitYul contract
  let text := Yul.render yulObj
  let path := s!"{outDir}/{contract.name}.yul"
  IO.FS.writeFile path text

def main : IO Unit := do
  let outDir := "compiler/yul"
  IO.FS.createDirAll outDir
  for contract in Translate.allContracts do
    writeContract outDir contract
