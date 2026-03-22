import Compiler.MainTest

unsafe def _root_.main (_args : List String) : IO UInt32 := do
  Compiler.MainTest.runTests
  pure 0
