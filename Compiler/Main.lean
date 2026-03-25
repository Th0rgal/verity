import Compiler.MainDriver

unsafe def main (args : List String) : IO Unit :=
  Compiler.Main.run args
