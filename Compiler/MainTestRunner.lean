import Compiler.MainTest

namespace Compiler.MainTestRunner

unsafe def main (_args : List String) : IO UInt32 := do
  Compiler.MainTest.runTests
  pure 0

end Compiler.MainTestRunner

unsafe def main (args : List String) : IO UInt32 :=
  Compiler.MainTestRunner.main args
