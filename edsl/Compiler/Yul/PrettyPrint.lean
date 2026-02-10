import Compiler.Yul.Ast

namespace Compiler.Yul

open YulExpr

private def hexDigit (n : Nat) : Char :=
  if n < 10 then
    Char.ofNat (n + 48)
  else
    Char.ofNat (n - 10 + 97)

partial def toHex (n : Nat) : String :=
  if n == 0 then
    "0"
  else
    let rec loop (x : Nat) (acc : List Char) : List Char :=
      if x == 0 then acc
      else
        let d := x % 16
        let acc' := hexDigit d :: acc
        loop (x / 16) acc'
    String.mk (loop n [])

private def indentStr (n : Nat) : String :=
  String.mk (List.replicate (n * 4) ' ')

partial def ppExpr : YulExpr → String
  | lit n => toString n
  | hex n => "0x" ++ toHex n
  | str s => "\"" ++ s ++ "\""
  | ident name => name
  | call func args =>
      let rendered := args.map ppExpr |>.intersperse ", " |>.foldl (· ++ ·) ""
      s!"{func}({rendered})"

partial def ppStmt (indent : Nat) : YulStmt → List String
  | YulStmt.comment text =>
      [s!"{indentStr indent}/* {text} */"]
  | YulStmt.let_ name value =>
      [s!"{indentStr indent}let {name} := {ppExpr value}"]
  | YulStmt.assign name value =>
      [s!"{indentStr indent}{name} := {ppExpr value}"]
  | YulStmt.expr e =>
      [s!"{indentStr indent}{ppExpr e}"]
  | YulStmt.if_ cond body =>
      let header := indentStr indent ++ "if " ++ ppExpr cond ++ " {"
      let bodyLines := body.flatMap (ppStmt (indent + 1))
      let footer := s!"{indentStr indent}}"
      header :: bodyLines ++ [footer]
  | YulStmt.switch expr cases defaultCase =>
      let header := indentStr indent ++ "switch " ++ ppExpr expr
      let caseLines := cases.flatMap (fun (c, body) =>
        let caseHeader := indentStr indent ++ "case 0x" ++ toHex c ++ " {"
        let bodyLines := body.flatMap (ppStmt (indent + 1))
        let footer := s!"{indentStr indent}}"
        caseHeader :: bodyLines ++ [footer]
      )
      let defaultLines :=
        match defaultCase with
        | none => []
        | some body =>
            let defaultHeader := indentStr indent ++ "default {"
            let bodyLines := body.flatMap (ppStmt (indent + 1))
            let footer := s!"{indentStr indent}}"
            defaultHeader :: bodyLines ++ [footer]
      header :: caseLines ++ defaultLines
  | YulStmt.block stmts =>
      let header := indentStr indent ++ "{"
      let bodyLines := stmts.flatMap (ppStmt (indent + 1))
      let footer := s!"{indentStr indent}}"
      header :: bodyLines ++ [footer]
  | YulStmt.funcDef name params rets body =>
      let paramsStr := params.intersperse ", " |>.foldl (· ++ ·) ""
      let retsStr :=
        match rets with
        | [] => ""
        | _ => " -> " ++ (rets.intersperse ", " |>.foldl (· ++ ·) "")
      let header := indentStr indent ++ "function " ++ name ++ "(" ++ paramsStr ++ ")" ++ retsStr ++ " {"
      let bodyLines := body.flatMap (ppStmt (indent + 1))
      let footer := s!"{indentStr indent}}"
      header :: bodyLines ++ [footer]

private def ppObject (obj : YulObject) : List String :=
  let header := "object \"" ++ obj.name ++ "\" {"
  let deployHeader := "    code {"
  let deployBody := obj.deployCode.flatMap (ppStmt 2)
  let deployFooter := "    }"
  let runtimeHeader := "    object \"runtime\" {"
  let runtimeCodeHeader := "        code {"
  let runtimeBody := obj.runtimeCode.flatMap (ppStmt 3)
  let runtimeFooter := "        }"
  let runtimeClose := "    }"
  let footer := "}"
  [header]
    ++ [deployHeader] ++ deployBody ++ [deployFooter]
    ++ [runtimeHeader] ++ [runtimeCodeHeader] ++ runtimeBody ++ [runtimeFooter] ++ [runtimeClose]
    ++ [footer]

partial def render (obj : YulObject) : String :=
  (ppObject obj).intersperse "\n" |>.foldl (· ++ ·) ""

end Compiler.Yul
