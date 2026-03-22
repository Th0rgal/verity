import Compiler.Yul.Ast
import Compiler.Hex

namespace Compiler.Yul

open YulExpr
open Compiler.Hex (natToHexUnpadded natToHex)

private def indentStr (n : Nat) : String :=
  String.mk (List.replicate (n * 4) ' ')

mutual
def ppExpr : YulExpr → String
  | lit n => toString n
  | hex n =>
      let raw := natToHexUnpadded n
      if raw.length % 2 = 0 then
        "0x" ++ raw
      else
        "0x0" ++ raw
  | str s => "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""
  | ident name => name
  | call func args =>
      s!"{func}({", ".intercalate (ppExprs args)})"

def ppExprs : List YulExpr → List String
  | [] => []
  | e :: es => ppExpr e :: ppExprs es

def ppStmt (indent : Nat) : YulStmt → List String
  | YulStmt.comment text =>
      [s!"{indentStr indent}/* {text.replace "*/" "* /"} */"]
  | YulStmt.let_ name value =>
      [s!"{indentStr indent}let {name} := {ppExpr value}"]
  | YulStmt.letMany names value =>
      [s!"{indentStr indent}let {", ".intercalate names} := {ppExpr value}"]
  | YulStmt.assign name value =>
      [s!"{indentStr indent}{name} := {ppExpr value}"]
  | YulStmt.expr e =>
      [s!"{indentStr indent}{ppExpr e}"]
  | YulStmt.leave =>
      [s!"{indentStr indent}leave"]
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
      let paramsStr := ", ".intercalate params
      let retsStr :=
        match rets with
        | [] => ""
        | _ => " -> " ++ ", ".intercalate rets
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
      let caseValue :=
        if c = 0 then
          "0"
        else
          natToHex c
      let caseHeader := indentStr indent ++ "case " ++ caseValue ++ " {"
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
  "\n".intercalate (ppObject obj)

example : ppCases 0 [(0, [])] = ["case 0 {", "}"] := by
  native_decide

example : ppCases 0 [(1, [])] = ["case 0x00000001 {", "}"] := by
  native_decide

end Compiler.Yul
