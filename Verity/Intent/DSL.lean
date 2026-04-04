/-
  Verity.Intent.DSL: Macros for writing IntentSpec declarations concisely.

  Instead of:
    def intentSpec : IntentSpec := {
      contractName := "ERC20"
      fns := [
        { name := "transfer"
          params := [("to", .address), ("amount", .uint256)]
          returnKind := .void
          body := [
            .ite (.call "isMaxUint" [.param "amount"])
              [.emit { text := "Send all tokens to {to}",
                       holes := [{ param := "to", format := .address }] }]
              [.emit { text := "Send {amount} tokens to {to}",
                       holes := [{ param := "amount", format := .tokenAmount 18 },
                                 { param := "to", format := .address }] }]
          ] }
      ]
      bindings := [{ functionName := "transfer", intentFn := "transfer" }]
    }

  Write:
    intent_spec "ERC20" where
      const MAX_UINT256 := (2 ^ 256 : Nat) - 1

      predicate isMaxUint(v : uint256) :=
        v == MAX_UINT256

      intent transfer(to : address, amount : uint256) where
        when isMaxUint(amount) =>
          emit "Send all tokens to {to:address}"
        otherwise =>
          emit "Send {amount:tokenAmount 18} tokens to {to:address}"

  Rule: `intent transfer(...)` implicitly binds to ABI function "transfer".
  For renamed/multi-bound intents: `intent myFn(...) binds ["transfer"] where ...`
-/
import Verity.Intent.Types

namespace Verity.Intent.DSL

open Verity.Intent
open Compiler.CompilationModel (ParamType)

/-! ## Syntax categories -/

declare_syntax_cat intentParamType
declare_syntax_cat intentParam
declare_syntax_cat intentExpr
declare_syntax_cat intentStmt
declare_syntax_cat intentDecl

/-! ## Parameter types (ABI types) -/

syntax "uint256" : intentParamType
syntax "int256" : intentParamType
syntax "uint8" : intentParamType
syntax "address" : intentParamType
syntax "bool" : intentParamType
syntax "bytes32" : intentParamType

/-! ## Parameters: name : type -/

syntax ident " : " intentParamType : intentParam

/-! ## Expressions -/

-- Atoms
syntax ident : intentExpr
syntax num : intentExpr
syntax "-" num : intentExpr
syntax str : intentExpr
syntax "(" intentExpr ")" : intentExpr

-- Function call: fnName(args...)
syntax ident "(" intentExpr,* ")" : intentExpr

-- Comparison / logical operators (left-associative, flat)
syntax:50 intentExpr " == " intentExpr : intentExpr
syntax:50 intentExpr " != " intentExpr : intentExpr
syntax:50 intentExpr " < "  intentExpr : intentExpr
syntax:50 intentExpr " > "  intentExpr : intentExpr
syntax:50 intentExpr " <= " intentExpr : intentExpr
syntax:50 intentExpr " >= " intentExpr : intentExpr
syntax:40 intentExpr " && " intentExpr : intentExpr
syntax:40 intentExpr " || " intentExpr : intentExpr
syntax:60 "!" intentExpr : intentExpr

-- Array access
syntax:70 intentExpr "[" intentExpr "]" : intentExpr
syntax:70 intentExpr ".length" : intentExpr

/-! ## Statements

Emit strings use inline typed placeholders: `{name:format}`.
  Formats: `address`, `raw`, `tokenAmount N`, `tokenAmount N "SYM"`, `enum "Name"`.
  Plain `{name}` defaults to `raw`.

`when/otherwise` is sugar for conditional branching.
-/

syntax "emit " str : intentStmt
syntax "when " intentExpr " => " intentStmt+ " otherwise " "=> " intentStmt+ : intentStmt
syntax "for " ident " in " intentExpr " {" intentStmt,* "}" : intentStmt
syntax ident "(" intentExpr,* ")" : intentStmt

/-! ## Top-level declarations -/

syntax "const " ident " := " term : intentDecl
syntax "enum " ident " {" (num " => " str),* "}" : intentDecl
syntax "predicate " ident "(" intentParam,* ")" " := " intentExpr : intentDecl
-- intent with implicit same-name binding
syntax "intent " ident "(" intentParam,* ")" " where" intentStmt+ : intentDecl
-- intent with explicit binds clause
syntax "intent " ident "(" intentParam,* ")" " binds " "[" str,* "]" " where" intentStmt+ : intentDecl

/-! ## Top-level command -/

syntax (name := intentSpecCmd)
  (docComment)?
  "intent_spec " str " where"
  intentDecl* : command

/-! ## Macro expansion helpers -/

/-- Expand an intentParamType to a ParamType term. -/
scoped syntax "ipt!" intentParamType : term
macro_rules
  | `(ipt! uint256)  => `(ParamType.uint256)
  | `(ipt! int256)   => `(ParamType.int256)
  | `(ipt! uint8)    => `(ParamType.uint8)
  | `(ipt! address)  => `(ParamType.address)
  | `(ipt! bool)     => `(ParamType.bool)
  | `(ipt! bytes32)  => `(ParamType.bytes32)

/-- Expand an intentExpr to an Expr term. -/
scoped syntax "iexpr!" intentExpr : term
macro_rules
  -- atoms
  | `(iexpr! $x:ident) => `(Expr.param $(Lean.quote (toString x.getId)))
  | `(iexpr! $n:num) => `(Expr.intLit $n)
  | `(iexpr! - $n:num) => `(Expr.intLit (-$n))
  | `(iexpr! $s:str) => `(Expr.strLit $s)
  | `(iexpr! ( $e:intentExpr )) => `(iexpr! $e)
  -- function call
  | `(iexpr! $fn:ident ( $args:intentExpr,* )) =>
    let fnName := Lean.quote (toString fn.getId)
    let argExprs := args.getElems.map fun a => (⟨a.raw⟩ : Lean.TSyntax `intentExpr)
    `(Expr.call $fnName [ $[ iexpr! $argExprs ],* ])
  -- comparisons
  | `(iexpr! $a:intentExpr == $b:intentExpr) => `(Expr.eq  (iexpr! $a) (iexpr! $b))
  | `(iexpr! $a:intentExpr != $b:intentExpr) => `(Expr.ne  (iexpr! $a) (iexpr! $b))
  | `(iexpr! $a:intentExpr <  $b:intentExpr) => `(Expr.lt  (iexpr! $a) (iexpr! $b))
  | `(iexpr! $a:intentExpr >  $b:intentExpr) => `(Expr.gt  (iexpr! $a) (iexpr! $b))
  | `(iexpr! $a:intentExpr <= $b:intentExpr) => `(Expr.le  (iexpr! $a) (iexpr! $b))
  | `(iexpr! $a:intentExpr >= $b:intentExpr) => `(Expr.ge  (iexpr! $a) (iexpr! $b))
  | `(iexpr! $a:intentExpr && $b:intentExpr) => `(Expr.and (iexpr! $a) (iexpr! $b))
  | `(iexpr! $a:intentExpr || $b:intentExpr) => `(Expr.or  (iexpr! $a) (iexpr! $b))
  | `(iexpr! ! $a:intentExpr) => `(Expr.not (iexpr! $a))
  -- array ops
  | `(iexpr! $a:intentExpr [ $i:intentExpr ]) => `(Expr.index  (iexpr! $a) (iexpr! $i))
  | `(iexpr! $a:intentExpr .length)            => `(Expr.length (iexpr! $a))

/-! ## Inline placeholder parsing

Parse `{name:format}` from emit strings at macro-expansion time.
`{name}` without a format defaults to `raw`.
-/

/-- Parse a format specifier string into a Format syntax term. -/
private def parseFormatSpec (spec : String) : Lean.MacroM (Lean.TSyntax `term) := do
  let spec := spec.trim
  if spec == "raw" || spec == "" then
    `(Format.raw)
  else if spec == "address" then
    `(Format.address)
  else if spec.startsWith "tokenAmount " then
    let rest := (spec.drop 12).trim  -- "tokenAmount " is 12 chars
    -- Check for optional symbol: `tokenAmount 18 "SYM"`
    if let some qIdx := rest.toList.findIdx? (· == '"') then
      let numStr := (rest.take qIdx).trim
      let sym := ((rest.drop (qIdx + 1)).dropRight 1)
      let nLit := Lean.Syntax.mkNumLit numStr
      let sLit := Lean.Syntax.mkStrLit sym
      `(Format.tokenAmount $nLit (some $sLit))
    else
      let nLit := Lean.Syntax.mkNumLit rest
      `(Format.tokenAmount $nLit)
  else if spec.startsWith "enum " then
    let rest := (spec.drop 5).trim  -- "enum " is 5 chars
    let name := if rest.startsWith "\"" then (rest.drop 1).dropRight 1 else rest
    let sLit := Lean.Syntax.mkStrLit name
    `(Format.enum $sLit)
  else
    Lean.Macro.throwError s!"unknown format specifier: {spec}"

/-- Parse all `{name:format}` placeholders from a template string.
    Returns the list of (param, formatSpec) pairs. -/
private def parseInlinePlaceholders (s : String) : List (String × String) := Id.run do
  let mut holes : List (String × String) := []
  let mut i := 0
  let chars := s.toList
  while h : i < chars.length do
    if chars[i] == '{' then
      let mut j := i + 1
      while j < chars.length && chars[j]! != '}' do
        j := j + 1
      if j < chars.length then
        let content := (chars.drop (i + 1)).take (j - i - 1)
        let contentStr := String.mk content
        let (paramName, fmtSpec) :=
          if let some colonIdx := contentStr.toList.findIdx? (· == ':') then
            (contentStr.take colonIdx, (contentStr.drop (colonIdx + 1)).trim)
          else
            (contentStr, "")
        holes := holes ++ [(paramName.trim, fmtSpec)]
      i := j + 1
    else
      i := i + 1
  return holes

/-- Strip format specifiers from placeholders: `{name:format}` → `{name}`. -/
private def stripFormats (s : String) : String := Id.run do
  let mut result := ""
  let mut i := 0
  let chars := s.toList
  while h : i < chars.length do
    if chars[i] == '{' then
      let mut j := i + 1
      while j < chars.length && chars[j]! != '}' do
        j := j + 1
      if j < chars.length then
        let content := (chars.drop (i + 1)).take (j - i - 1)
        let contentStr := String.mk content
        let paramName :=
          if let some colonIdx := contentStr.toList.findIdx? (· == ':') then
            contentStr.take colonIdx
          else
            contentStr
        result := result ++ "{" ++ paramName.trim ++ "}"
      i := j + 1
    else
      result := result.push chars[i]
      i := i + 1
  return result

/-- Expand an emit statement with inline placeholders to a Stmt.emit term. -/
private def expandEmit (txt : Lean.TSyntax `str) : Lean.MacroM (Lean.TSyntax `term) := do
  let rawStr := txt.getString
  let holes := parseInlinePlaceholders rawStr
  let displayText := stripFormats rawStr
  let displayLit := Lean.Syntax.mkStrLit displayText
  let mut holeTerms : Array (Lean.TSyntax `term) := #[]
  for (param, fmtSpec) in holes do
    let paramLit := Lean.Syntax.mkStrLit param
    let fmtTerm ← parseFormatSpec fmtSpec
    holeTerms := holeTerms.push (← `(Hole.mk $paramLit $fmtTerm))
  `(Stmt.emit (Template.mk $displayLit [ $[$holeTerms],* ]))

/-- Expand a statement to a Stmt term. -/
scoped syntax "istmt!" intentStmt : term
macro_rules
  -- emit with inline placeholders
  | `(istmt! emit $txt:str) =>
    expandEmit txt
  -- when/otherwise
  | `(istmt! when $cond:intentExpr => $thenSs:intentStmt* otherwise => $elseSs:intentStmt*) => do
    let thenExprs := thenSs.map fun s => (⟨s.raw⟩ : Lean.TSyntax `intentStmt)
    let elseExprs := elseSs.map fun s => (⟨s.raw⟩ : Lean.TSyntax `intentStmt)
    `(Stmt.ite (iexpr! $cond) [ $[ istmt! $thenExprs ],* ] [ $[ istmt! $elseExprs ],* ])
  -- forEach
  | `(istmt! for $var:ident in $arr:intentExpr { $bodySs:intentStmt,* }) =>
    let bodyExprs := bodySs.getElems.map fun s => (⟨s.raw⟩ : Lean.TSyntax `intentStmt)
    `(Stmt.forEach $(Lean.quote (toString var.getId)) (iexpr! $arr) [ $[ istmt! $bodyExprs ],* ])
  -- void function call
  | `(istmt! $fn:ident ( $args:intentExpr,* )) =>
    let fnName := Lean.quote (toString fn.getId)
    let argExprs := args.getElems.map fun a => (⟨a.raw⟩ : Lean.TSyntax `intentExpr)
    `(Stmt.call $fnName [ $[ iexpr! $argExprs ],* ])

/-! ## Declaration expansion -/

/-- Expand a single param to (name, type) pair. -/
scoped syntax "iparam!" intentParam : term
macro_rules
  | `(iparam! $name:ident : $ty:intentParamType) =>
    `(($(Lean.quote (toString name.getId)), ipt! $ty))

/-! ## Main command macro -/

private def mkConstList (decls : Array (Lean.TSyntax `intentDecl)) : Lean.MacroM (Array (Lean.TSyntax `term)) := do
  let mut result := #[]
  for d in decls do
    match d with
    | `(intentDecl| const $name:ident := $val:term) =>
      let nameStr := Lean.quote (toString name.getId)
      result := result.push (← `(ConstDef.mk $nameStr (Expr.intLit ($val : Int))))
    | _ => pure ()
  return result

private def mkEnumList (decls : Array (Lean.TSyntax `intentDecl)) : Lean.MacroM (Array (Lean.TSyntax `term)) := do
  let mut result := #[]
  for d in decls do
    match d with
    | `(intentDecl| enum $name:ident { $[$ns:num => $ss:str],* }) =>
      let nameStr := Lean.quote (toString name.getId)
      result := result.push (← `(EnumDef.mk $nameStr [ $[($ns, $ss)],* ]))
    | _ => pure ()
  return result

private def mkFnList (decls : Array (Lean.TSyntax `intentDecl)) : Lean.MacroM (Array (Lean.TSyntax `term)) := do
  let mut result := #[]
  for d in decls do
    match d with
    | `(intentDecl| predicate $name:ident ( $params:intentParam,* ) := $body:intentExpr) =>
      let nameStr := Lean.quote (toString name.getId)
      let paramExprs := params.getElems.map fun p => (⟨p.raw⟩ : Lean.TSyntax `intentParam)
      result := result.push (← `(FnDecl.mk $nameStr [ $[ iparam! $paramExprs ],* ] ReturnKind.bool [] (some (iexpr! $body))))
    | `(intentDecl| intent $name:ident ( $params:intentParam,* ) where $stmts:intentStmt*) =>
      let nameStr := Lean.quote (toString name.getId)
      let paramExprs := params.getElems.map fun p => (⟨p.raw⟩ : Lean.TSyntax `intentParam)
      let stmtExprs := stmts.map fun s => (⟨s.raw⟩ : Lean.TSyntax `intentStmt)
      result := result.push (← `(FnDecl.mk $nameStr [ $[ iparam! $paramExprs ],* ] ReturnKind.void [ $[ istmt! $stmtExprs ],* ] none))
    | `(intentDecl| intent $name:ident ( $params:intentParam,* ) binds [ $_:str ,* ] where $stmts:intentStmt*) =>
      let nameStr := Lean.quote (toString name.getId)
      let paramExprs := params.getElems.map fun p => (⟨p.raw⟩ : Lean.TSyntax `intentParam)
      let stmtExprs := stmts.map fun s => (⟨s.raw⟩ : Lean.TSyntax `intentStmt)
      result := result.push (← `(FnDecl.mk $nameStr [ $[ iparam! $paramExprs ],* ] ReturnKind.void [ $[ istmt! $stmtExprs ],* ] none))
    | _ => pure ()
  return result

/-- Collect bindings from intent declarations.
    - `intent foo(...)` → implicit binding: `"foo" → "foo"`
    - `intent foo(...) binds ["bar", "baz"]` → explicit: `"bar" → "foo"`, `"baz" → "foo"` -/
private def mkBindingList (decls : Array (Lean.TSyntax `intentDecl)) : Lean.MacroM (Array (Lean.TSyntax `term)) := do
  let mut result := #[]
  for d in decls do
    match d with
    | `(intentDecl| intent $name:ident ( $_ ,* ) where $_ *) =>
      let nameStr := Lean.quote (toString name.getId)
      result := result.push (← `(IntentBinding.mk $nameStr $nameStr))
    | `(intentDecl| intent $name:ident ( $_ ,* ) binds [ $fns:str ,* ] where $_ *) =>
      let nameStr := Lean.quote (toString name.getId)
      for fn in fns.getElems do
        result := result.push (← `(IntentBinding.mk $fn $nameStr))
    | _ => pure ()
  return result

macro_rules
  | `(command| $[$doc?:docComment]? intent_spec $contractName:str where $decls:intentDecl*) => do
    let declArr : Array (Lean.TSyntax `intentDecl) := decls
    let constTerms ← mkConstList declArr
    let enumTerms ← mkEnumList declArr
    let fnTerms ← mkFnList declArr
    let bindingTerms ← mkBindingList declArr
    let specName := Lean.mkIdent `intentSpec
    let specType := Lean.mkIdent `IntentSpec
    `(command|
      $[$doc?:docComment]? def $specName : $specType := {
        contractName := $contractName
        constants := [ $[$constTerms],* ]
        enums := [ $[$enumTerms],* ]
        fns := [ $[$fnTerms],* ]
        bindings := [ $[$bindingTerms],* ]
      })

end Verity.Intent.DSL
