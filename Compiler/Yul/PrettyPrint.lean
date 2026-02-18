import Compiler.Yul.Ast
import Compiler.Hex

namespace Compiler.Yul

open YulExpr
open Compiler.Hex (hexDigit)

def toHex (n : Nat) : String :=
  if n == 0 then
    "0"
  else
    let rec loop (x : Nat) (acc : List Char) : List Char :=
      if x == 0 then acc
      else
        let d := x % 16
        let acc' := hexDigit d :: acc
        loop (x / 16) acc'
    termination_by x
    decreasing_by
      simp_wf
      simp [Nat.beq_eq] at *
      exact Nat.div_lt_self (by omega) (by omega)
    String.mk (loop n [])

private def indentStr (n : Nat) : String :=
  String.mk (List.replicate (n * 4) ' ')

mutual
def ppExpr : YulExpr → String
  | lit n => toString n
  | hex n => "0x" ++ toHex n
  | str s => "\"" ++ s ++ "\""
  | ident name => name
  | call func args =>
      let rendered := ppExprs args |>.intersperse ", " |>.foldl (· ++ ·) ""
      s!"{func}({rendered})"

def ppExprs : List YulExpr → List String
  | [] => []
  | e :: es => ppExpr e :: ppExprs es

def ppStmt (indent : Nat) : YulStmt → List String
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
      let bodyLines := ppStmts (indent + 1) body
      let footer := s!"{indentStr indent}}"
      header :: bodyLines ++ [footer]
  | YulStmt.for_ init cond post body =>
      let initBlock := ppStmts (indent + 1) init
      let postBlock := ppStmts (indent + 1) post
      let bodyLines := ppStmts (indent + 1) body
      let header := indentStr indent ++ "for {"
      let initFooter := indentStr indent ++ "} " ++ ppExpr cond ++ " {"
      let postFooter := indentStr indent ++ "} {"
      let footer := indentStr indent ++ "}"
      header :: initBlock ++ [initFooter] ++ postBlock ++ [postFooter] ++ bodyLines ++ [footer]
  | YulStmt.switch expr cases defaultCase =>
      let header := indentStr indent ++ "switch " ++ ppExpr expr
      let caseLines := ppCases indent cases
      let defaultLines :=
        match defaultCase with
        | none => []
        | some body =>
            let defaultHeader := indentStr indent ++ "default {"
            let bodyLines := ppStmts (indent + 1) body
            let footer := s!"{indentStr indent}}"
            defaultHeader :: bodyLines ++ [footer]
      header :: caseLines ++ defaultLines
  | YulStmt.block stmts =>
      let header := indentStr indent ++ "{"
      let bodyLines := ppStmts (indent + 1) stmts
      let footer := s!"{indentStr indent}}"
      header :: bodyLines ++ [footer]
  | YulStmt.funcDef name params rets body =>
      let paramsStr := params.intersperse ", " |>.foldl (· ++ ·) ""
      let retsStr :=
        match rets with
        | [] => ""
        | _ => " -> " ++ (rets.intersperse ", " |>.foldl (· ++ ·) "")
      let header := indentStr indent ++ "function " ++ name ++ "(" ++ paramsStr ++ ")" ++ retsStr ++ " {"
      let bodyLines := ppStmts (indent + 1) body
      let footer := s!"{indentStr indent}}"
      header :: bodyLines ++ [footer]

def ppStmts (indent : Nat) : List YulStmt → List String
  | [] => []
  | s :: ss => ppStmt indent s ++ ppStmts indent ss

def ppCases (indent : Nat) : List (Nat × List YulStmt) → List String
  | [] => []
  | (c, body) :: rest =>
      let caseHeader := indentStr indent ++ "case 0x" ++ toHex c ++ " {"
      let bodyLines := ppStmts (indent + 1) body
      let footer := s!"{indentStr indent}}"
      (caseHeader :: bodyLines ++ [footer]) ++ ppCases indent rest
end

private def ppObject (obj : YulObject) : List String :=
  let header := "object \"" ++ obj.name ++ "\" {"
  let deployHeader := "    code {"
  let deployBody := ppStmts 2 obj.deployCode
  let deployFooter := "    }"
  let runtimeHeader := "    object \"runtime\" {"
  let runtimeCodeHeader := "        code {"
  let runtimeBody := ppStmts 3 obj.runtimeCode
  let runtimeFooter := "        }"
  let runtimeClose := "    }"
  let footer := "}"
  [header]
    ++ [deployHeader] ++ deployBody ++ [deployFooter]
    ++ [runtimeHeader] ++ [runtimeCodeHeader] ++ runtimeBody ++ [runtimeFooter] ++ [runtimeClose]
    ++ [footer]

def render (obj : YulObject) : String :=
  (ppObject obj).intersperse "\n" |>.foldl (· ++ ·) ""

end Compiler.Yul
