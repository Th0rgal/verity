import Compiler.CompilationModel

namespace Contracts.StringArrayErrorSmoke

open Compiler.CompilationModel

def spec : CompilationModel := {
  name := "StringArrayErrorSmoke"
  fields := []
  constructor := none
  functions := [
    { name := "checkBatch"
      params := [
        { name := "ok", ty := ParamType.bool }
      , { name := "messages", ty := ParamType.array ParamType.string }
      ]
      returnType := none
      body := [
        Stmt.requireError (Expr.param "ok") "BadMessages" [Expr.param "messages"],
        Stmt.stop
      ]
    }
    , { name := "checkTaggedBatch"
        params := [
          { name := "tag", ty := ParamType.uint256 }
        , { name := "messages", ty := ParamType.array ParamType.string }
        ]
        returnType := none
        body := [
          Stmt.requireError (Expr.eq (Expr.param "tag") (Expr.literal 1))
            "TaggedMessages" [Expr.param "tag", Expr.param "messages"],
          Stmt.stop
        ]
      }
    , { name := "checkSecondBatch"
        params := [
          { name := "ok", ty := ParamType.bool }
        , { name := "prefix", ty := ParamType.array ParamType.string }
        , { name := "messages", ty := ParamType.array ParamType.string }
        ]
        returnType := none
        body := [
          Stmt.requireError (Expr.param "ok") "SecondMessages"
            [Expr.param "prefix", Expr.param "messages"],
          Stmt.stop
        ]
      }
  ]
  errors := [
    { name := "BadMessages"
      params := [ParamType.array ParamType.string]
    }
    , { name := "TaggedMessages"
        params := [ParamType.uint256, ParamType.array ParamType.string]
      }
    , { name := "SecondMessages"
        params := [ParamType.array ParamType.string, ParamType.array ParamType.string]
      }
  ]
}

end Contracts.StringArrayErrorSmoke
