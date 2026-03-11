import Compiler.CompilationModel

namespace Contracts.StringArrayEventSmoke

open Compiler.CompilationModel

def spec : CompilationModel := {
  name := "StringArrayEventSmoke"
  fields := []
  constructor := none
  functions := [
    { name := "logBatch"
      params := [{ name := "messages", ty := ParamType.array ParamType.string }]
      returnType := none
      body := [
        Stmt.emit "MessageBatch" [Expr.param "messages", Expr.param "messages"],
        Stmt.stop
      ]
    }
  ]
  events := [
    { name := "MessageBatch"
      params := [
        { name := "body", ty := ParamType.array ParamType.string, kind := EventParamKind.unindexed }
      , { name := "topicBody", ty := ParamType.array ParamType.string, kind := EventParamKind.indexed }
      ]
    }
  ]
}

end Contracts.StringArrayEventSmoke
