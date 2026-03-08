import Compiler.CompilationModel

namespace Contracts.RawLogTrustSurface

open Compiler.CompilationModel

def spec : CompilationModel := {
  name := "RawLogTrustSurface"
  fields := []
  constructor := none
  functions := [
    { name := "emitTrace"
      params := []
      returnType := none
      body := [
        Stmt.rawLog [Expr.literal 1, Expr.literal 2] (Expr.literal 0) (Expr.literal 64),
        Stmt.stop
      ]
    }
  ]
}

end Contracts.RawLogTrustSurface
