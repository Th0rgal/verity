/-
  Exports IntentSpec definitions to JSON for the explain.md frontend.

  Produces the full DSL structure (conditionals, all templates, formats)
  so the frontend can evaluate intents without duplicating specs in TypeScript.

  Usage:
    lake env lean Compiler/ExportIntentJson.lean
-/
import Verity.Intent.Types
import Verity.Intent.DSL
import Contracts.ERC20.Display
import Contracts.UniswapV2.Display

open Verity.Intent

-- ─── JSON helpers ────────────────────────────────────────────────────────────

private def esc (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"

private def jstr (s : String) : String := s!"\"{esc s}\""
private def jarr (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"
private def jobj (fs : List (String × String)) : String :=
  "{" ++ ",".intercalate (fs.map fun (k, v) => s!"{jstr k}:{v}") ++ "}"

-- ─── Serializers ─────────────────────────────────────────────────────────────

private def fmtJ : Format → String
  | .raw => jobj [("kind", jstr "raw")]
  | .tokenAmount d none => jobj [("kind", jstr "tokenAmount"), ("decimals", toString d)]
  | .tokenAmount d (some s) => jobj [("kind", jstr "tokenAmount"), ("decimals", toString d), ("symbol", jstr s)]
  | .address => jobj [("kind", jstr "address")]
  | .enum n => jobj [("kind", jstr "enum"), ("enumName", jstr n)]

private def holeJ (h : Hole) : String :=
  jobj [("name", jstr h.param), ("format", fmtJ h.format)]

private def tmplJ (t : Template) : String :=
  jobj [("text", jstr t.text), ("holes", jarr (t.holes.map holeJ))]

private partial def exprJ : Expr → String
  | .param name => jobj [("kind", jstr "param"), ("name", jstr name)]
  | .intLit n => jobj [("kind", jstr "const"), ("value", jstr (toString n))]
  | .strLit s => jobj [("kind", jstr "strLit"), ("value", jstr s)]
  | .eq a b => jobj [("kind", jstr "eq"), ("left", exprJ a), ("right", exprJ b)]
  | .ne a b => jobj [("kind", jstr "ne"), ("left", exprJ a), ("right", exprJ b)]
  | .lt a b => jobj [("kind", jstr "lt"), ("left", exprJ a), ("right", exprJ b)]
  | .gt a b => jobj [("kind", jstr "gt"), ("left", exprJ a), ("right", exprJ b)]
  | .le a b => jobj [("kind", jstr "le"), ("left", exprJ a), ("right", exprJ b)]
  | .ge a b => jobj [("kind", jstr "ge"), ("left", exprJ a), ("right", exprJ b)]
  | .and a b => jobj [("kind", jstr "and"), ("left", exprJ a), ("right", exprJ b)]
  | .or a b => jobj [("kind", jstr "or"), ("left", exprJ a), ("right", exprJ b)]
  | .not a => jobj [("kind", jstr "not"), ("expr", exprJ a)]
  | .call fn args => jobj [("kind", jstr "call"), ("name", jstr fn), ("args", jarr (args.map exprJ))]
  | .index arr idx => jobj [("kind", jstr "index"), ("array", exprJ arr), ("index", exprJ idx)]
  | Expr.length arr => jobj [("kind", jstr "length"), ("array", exprJ arr)]

private partial def stmtJ : Stmt → String
  | .emit t => jobj [("kind", jstr "emit"), ("template", tmplJ t)]
  | .ite c th el => jobj [
      ("kind", jstr "when"), ("condition", exprJ c),
      ("then", jarr (th.map stmtJ)), ("otherwise", jarr (el.map stmtJ))]
  | .forEach v arr body => jobj [
      ("kind", jstr "forEach"), ("name", jstr v),
      ("array", exprJ arr), ("body", jarr (body.map stmtJ))]
  | .call fn args => jobj [("kind", jstr "callStmt"), ("name", jstr fn), ("args", jarr (args.map exprJ))]

open Compiler.CompilationModel in
private def paramTypeJ : ParamType → String
  | ParamType.uint256 => jstr "uint256"
  | ParamType.int256 => jstr "int256"
  | ParamType.uint8 => jstr "uint8"
  | ParamType.address => jstr "address"
  | ParamType.bool => jstr "bool"
  | ParamType.bytes32 => jstr "bytes32"
  | ParamType.string => jstr "string"
  | ParamType.tuple _ => jstr "tuple"
  | ParamType.array t => jstr s!"array({(paramTypeJ t).drop 1 |>.dropRight 1})"
  | ParamType.fixedArray t n => jstr s!"fixedArray({(paramTypeJ t).drop 1 |>.dropRight 1},{n})"
  | ParamType.bytes => jstr "bytes"

private def returnKindJ : ReturnKind → String
  | .void   => jstr "void"
  | .bool   => jstr "bool"
  | .string => jstr "string"

private def fnDeclJ (f : FnDecl) : String :=
  let params := jarr (f.params.map fun (n, t) => jobj [("name", jstr n), ("type", paramTypeJ t)])
  let body := jarr (f.body.map stmtJ)
  let expr := match f.expr with
    | none => "null"
    | some e => exprJ e
  jobj [("name", jstr f.name), ("params", params), ("returnKind", returnKindJ f.returnKind),
        ("body", body), ("expr", expr)]

private def constJ (c : ConstDef) : String :=
  jobj [("name", jstr c.name), ("value", exprJ c.value)]

private def bindingJ (b : IntentBinding) : String :=
  jobj [("functionName", jstr b.functionName), ("intentFnName", jstr b.intentFn)]

private def specJ (s : IntentSpec) : String :=
  jobj [
    ("contractName", jstr s.contractName),
    ("fns", jarr (s.fns.map fnDeclJ)),
    ("constants", jarr (s.constants.map constJ)),
    ("bindings", jarr (s.bindings.map bindingJ))
  ]

-- ─── Main ────────────────────────────────────────────────────────────────────

def main : IO Unit := do
  IO.println "=== ERC20 ==="
  IO.println (specJ Contracts.ERC20.intentSpec)
  IO.println "=== UniswapV2 ==="
  IO.println (specJ Contracts.UniswapV2.intentSpec)
