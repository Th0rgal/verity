import Compiler.Main

/-- Thin entry-point wrapper so verity-compiler resolves this module's main. -/
unsafe def main (args : List String) : IO Unit :=
  Compiler.Main.main args
