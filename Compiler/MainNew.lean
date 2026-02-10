/-
  Compiler.MainNew: New automatic compilation system

  This demonstrates the new declarative contract specification system.
  Contracts are specified once and compiled automatically.
-/

import Compiler.CompileDriver

def main : IO Unit := do
  compileAll "compiler/yul-new" true
