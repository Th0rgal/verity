import Compiler.CompilationModel

namespace Contracts.LocalObligationTrustSurface

open Compiler.CompilationModel

def spec : CompilationModel := {
  name := "LocalObligationTrustSurface"
  fields := []
  «constructor» := none
  functions := [
    { name := "unsafeEdge"
      params := []
      returnType := none
      localObligations := [
        { name := "manual_delegatecall_refinement"
          obligation := "Caller must separately prove the handwritten assembly path refines the intended state transition."
          proofStatus := .assumed }
      ]
      body := [Stmt.stop]
    }
  ]
}

end Contracts.LocalObligationTrustSurface
