import Compiler.CompilationModel

namespace Contracts.StringEventSmoke

open Compiler.CompilationModel

def spec : CompilationModel := {
  name := "StringEventSmoke"
  fields := []
  constructor := none
  functions := [
    { name := "logMessage"
      params := [{ name := "message", ty := ParamType.string }]
      returnType := none
      body := [Stmt.emit "MessageLogged" [Expr.param "message"], Stmt.stop]
    }
    , { name := "logTaggedMessage"
        params := [{ name := "tag", ty := ParamType.uint256 }, { name := "message", ty := ParamType.string }]
        returnType := none
        body := [Stmt.emit "TaggedMessageLogged" [Expr.param "tag", Expr.param "message"], Stmt.stop]
      }
    , { name := "logIndexedMessage"
        params := [{ name := "message", ty := ParamType.string }]
        returnType := none
        body := [Stmt.emit "IndexedMessageLogged" [Expr.param "message"], Stmt.stop]
      }
    , { name := "logSecondMessage"
        params := [{ name := "prefix", ty := ParamType.string }, { name := "message", ty := ParamType.string }]
        returnType := none
        body := [Stmt.emit "SecondMessageLogged" [Expr.param "prefix", Expr.param "message"], Stmt.stop]
      }
  ]
  events := [
    { name := "MessageLogged"
      params := [{ name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }]
    }
    , { name := "TaggedMessageLogged"
        params := [
          { name := "tag", ty := ParamType.uint256, kind := EventParamKind.indexed }
        , { name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }
        ]
      }
    , { name := "IndexedMessageLogged"
        params := [{ name := "message", ty := ParamType.string, kind := EventParamKind.indexed }]
      }
    , { name := "SecondMessageLogged"
        params := [
          { name := "prefix", ty := ParamType.string, kind := EventParamKind.unindexed }
        , { name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }
        ]
      }
  ]
}

end Contracts.StringEventSmoke
