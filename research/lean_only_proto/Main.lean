import DumbContracts.Compiler
import DumbContracts.EvmAsm
import DumbContracts.Yul

open DumbContracts
open DumbContracts.Compiler
open DumbContracts.Yul

-- Emit Yul/EVM artifacts.
def main : IO Unit := do
  let exampleProg := compileProgram [exampleEntry, exampleEntry2, exampleEntry3, exampleEntry4, exampleEntry5]
  let exampleYul := Yul.Pretty.program exampleProg
  IO.FS.writeFile "out/example.yul" exampleYul
  let healthProg := compileProgram [healthEntrySet, healthEntryCheck]
  let healthYul := Yul.Pretty.program healthProg
  IO.FS.writeFile "out/health.yul" healthYul
  let evmAsm := DumbContracts.EvmAsm.pretty DumbContracts.EvmAsm.directProgramAsm
  IO.FS.writeFile "out/example.evm" evmAsm
  IO.println exampleYul
