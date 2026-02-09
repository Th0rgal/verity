import DumbContracts.Compiler
import DumbContracts.Yul

open DumbContracts
open DumbContracts.Compiler
open DumbContracts.Yul

-- Emit a minimal Yul program for testing strict-assembly.
def main : IO Unit := do
  let prog := compileProgram [exampleEntry, exampleEntry2]
  let yul := Yul.Pretty.program prog
  IO.FS.writeFile "out/example.yul" yul
  IO.println yul
