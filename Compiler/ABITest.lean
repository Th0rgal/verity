import Compiler.ABI

namespace Compiler.ABITest

open Compiler.CompilationModel

private def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
        if (c :: cs).take n.length == n then true
        else go cs
    go h

private def assertContains (label rendered : String) (needles : List String) : IO Unit := do
  for needle in needles do
    if !contains rendered needle then
      throw (IO.userError s!"✗ {label}: missing '{needle}' in:\n{rendered}")
  IO.println s!"✓ {label}"

private def abiSpec : CompilationModel := {
  name := "ABIEmitterFixture"
  fields := []
  constructor := some {
    params := [{ name := "owner", ty := ParamType.address }]
    isPayable := true
    body := [Stmt.stop]
  }
  functions := [
    { name := "setTuple"
      params := [{ name := "cfg", ty := ParamType.tuple [ParamType.address, ParamType.uint256] }]
      returnType := none
      body := [Stmt.stop]
    },
    { name := "echoTupleArray"
      params := [{ name := "items", ty := ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.bool]) }]
      returnType := none
      returns := [ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.bool])]
      body := [Stmt.stop]
    },
    { name := "totalSupply"
      params := []
      returnType := some FieldType.uint256
      isView := true
      body := [Stmt.return (Expr.literal 1)]
    },
    { name := "version"
      params := []
      returnType := some FieldType.uint256
      isPure := true
      body := [Stmt.return (Expr.literal 1)]
    },
    { name := "fallback"
      params := []
      returnType := none
      isPayable := false
      body := [Stmt.stop]
    },
    { name := "receive"
      params := []
      returnType := none
      isPayable := true
      body := [Stmt.stop]
    },
    { name := "internalHelper"
      params := [{ name := "x", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.param "x")]
      isInternal := true
    }
  ]
  events := [
    { name := "Data"
      params := [
        { name := "id", ty := ParamType.uint256, kind := EventParamKind.indexed },
        { name := "payload", ty := ParamType.bytes, kind := EventParamKind.unindexed }
      ]
    }
  ]
  «errors» := [
    { name := "BadThing"
      params := [ParamType.address, ParamType.bytes]
    }
  ]
}

private def stringAbiSpec : CompilationModel := {
  name := "StringABIEmitterFixture"
  fields := []
  constructor := none
  functions := [
    { name := "echoString"
      params := [{ name := "message", ty := ParamType.string }]
      returnType := none
      returns := [ParamType.string]
      body := [Stmt.returnBytes "message"]
    }
    , { name := "echoStringAfterUint"
        params := [{ name := "tag", ty := ParamType.uint256 }, { name := "message", ty := ParamType.string }]
        returnType := none
        returns := [ParamType.string]
        body := [Stmt.returnBytes "message"]
      }
    , { name := "echoStringBeforeUint"
        params := [{ name := "message", ty := ParamType.string }, { name := "tag", ty := ParamType.uint256 }]
        returnType := none
        returns := [ParamType.string]
        body := [Stmt.returnBytes "message"]
      }
    , { name := "echoSecondString"
        params := [{ name := "prefix", ty := ParamType.string }, { name := "message", ty := ParamType.string }]
        returnType := none
        returns := [ParamType.string]
        body := [Stmt.returnBytes "message"]
      }
  ]
  events := [
    { name := "MessageLogged"
      params := [
        { name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }
      ]
    }
  ]
  «errors» := [
    { name := "BadMessage"
      params := [ParamType.string]
    }
    , { name := "TaggedMessage"
        params := [ParamType.uint256, ParamType.string]
      }
    , { name := "SecondMessage"
        params := [ParamType.string, ParamType.string]
      }
  ]
}

#eval! do
  let rendered := Compiler.ABI.emitContractABIJson abiSpec
  assertContains "constructor entry" rendered ["\"type\": \"constructor\"", "\"stateMutability\": \"payable\""]
  assertContains "function entry" rendered ["\"type\": \"function\"", "\"name\": \"setTuple\""]
  assertContains "tuple components" rendered ["\"type\": \"tuple\"", "\"components\": [{\"name\": \"\", \"type\": \"address\"}, {\"name\": \"\", \"type\": \"uint256\"}]"]
  assertContains "tuple array components" rendered ["\"type\": \"tuple[]\"", "\"outputs\": [{\"name\": \"\", \"type\": \"tuple[]\", \"components\": [{\"name\": \"\", \"type\": \"uint256\"}, {\"name\": \"\", \"type\": \"bool\"}]}]"]
  assertContains "state mutability view/pure" rendered ["\"name\": \"totalSupply\"", "\"stateMutability\": \"view\"", "\"name\": \"version\"", "\"stateMutability\": \"pure\""]
  assertContains "event indexed metadata" rendered ["\"type\": \"event\"", "\"indexed\": true", "\"indexed\": false"]
  assertContains "error entry" rendered ["\"type\": \"error\"", "\"name\": \"BadThing\""]
  assertContains "special entrypoints" rendered ["\"type\": \"fallback\"", "\"type\": \"receive\""]
  if contains rendered "internalHelper" then
    throw (IO.userError s!"✗ internal functions must not appear in ABI: {rendered}")
  IO.println "✓ internal function filtering"

  let stringRendered := Compiler.ABI.emitContractABIJson stringAbiSpec
  assertContains
    "string function input/output ABI"
    stringRendered
    [ "\"name\": \"echoString\""
    , "\"inputs\": [{\"name\": \"message\", \"type\": \"string\"}]"
    , "\"name\": \"echoStringAfterUint\""
    , "\"inputs\": [{\"name\": \"tag\", \"type\": \"uint256\"}, {\"name\": \"message\", \"type\": \"string\"}]"
    , "\"name\": \"echoStringBeforeUint\""
    , "\"inputs\": [{\"name\": \"message\", \"type\": \"string\"}, {\"name\": \"tag\", \"type\": \"uint256\"}]"
    , "\"name\": \"echoSecondString\""
    , "\"inputs\": [{\"name\": \"prefix\", \"type\": \"string\"}, {\"name\": \"message\", \"type\": \"string\"}]"
    , "\"outputs\": [{\"name\": \"\", \"type\": \"string\"}]"
    ]
  assertContains
    "string event ABI"
    stringRendered
    ["\"type\": \"event\"", "\"name\": \"MessageLogged\"", "\"type\": \"string\"", "\"indexed\": false"]
  assertContains
    "string error ABI"
    stringRendered
    [ "\"type\": \"error\""
    , "\"name\": \"BadMessage\""
    , "\"inputs\": [{\"name\": \"\", \"type\": \"string\"}]"
    , "\"name\": \"TaggedMessage\""
    , "\"inputs\": [{\"name\": \"\", \"type\": \"uint256\"}, {\"name\": \"\", \"type\": \"string\"}]"
    , "\"name\": \"SecondMessage\""
    , "\"inputs\": [{\"name\": \"\", \"type\": \"string\"}, {\"name\": \"\", \"type\": \"string\"}]"
    ]

end Compiler.ABITest
