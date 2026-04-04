/-
  Verity.Intent.DSL: Macros for writing IntentSpec declarations concisely.

  Instead of:
    def intentSpec : IntentSpec := {
      contractName := "ERC20"
      fns := [
        { name := "transferIntent"
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
      bindings := [{ functionName := "transfer", intentFn := "transferIntent" }]
    }

  Write:
    intent_spec "ERC20" where
      const MAX_UINT256 := (2 ^ 256 : Nat) - 1

      predicate isMaxUint(v : uint256) :=
        v == MAX_UINT256

      intent transferIntent(to : address, amount : uint256) where
        if isMaxUint(amount)
        then emit "Send all tokens to {to}" [to : address]
        else emit "Send {amount} tokens to {to}" [amount : tokenAmount 18, to : address]

      bind "transfer" => transferIntent
-/
import Verity.Intent.Types

namespace Verity.Intent.DSL

open Verity.Intent
open Compiler.CompilationModel (ParamType)

/-! ## Syntax categories -/

declare_syntax_cat intentParamType
declare_syntax_cat intentFormat
declare_syntax_cat intentParam
declare_syntax_cat intentHole
declare_syntax_cat intentExpr
declare_syntax_cat intentStmt
declare_syntax_cat intentDecl
declare_syntax_cat intentBinding

/-! ## Parameter types (ABI types) -/

syntax "uint256" : intentParamType
syntax "int256" : intentParamType
syntax "uint8" : intentParamType
syntax "address" : intentParamType
syntax "bool" : intentParamType
syntax "bytes32" : intentParamType

/-! ## Format directives -/

syntax "raw" : intentFormat
syntax "address" : intentFormat
syntax "tokenAmount" num : intentFormat
syntax "tokenAmount" num str : intentFormat
syntax "enum" str : intentFormat

/-! ## Parameters: name : type -/

syntax ident " : " intentParamType : intentParam

/-! ## Holes in emit: param : format -/

syntax ident " : " intentFormat : intentHole

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

/-! ## Statements -/

syntax "emit " str " [" intentHole,* "]" : intentStmt
syntax "emit " str : intentStmt
syntax "if " intentExpr " then " intentStmt " else " intentStmt : intentStmt
syntax "if " intentExpr
       " then" " {" intentStmt,* "}"
       " else" " {" intentStmt,* "}" : intentStmt
syntax "for " ident " in " intentExpr " {" intentStmt,* "}" : intentStmt
syntax ident "(" intentExpr,* ")" : intentStmt

/-! ## Top-level declarations -/

syntax "const " ident " := " term : intentDecl
syntax "enum " ident " {" (num " => " str),* "}" : intentDecl
syntax "predicate " ident "(" intentParam,* ")" " := " intentExpr : intentDecl
syntax "intent " ident "(" intentParam,* ")" " where " intentStmt,* : intentDecl
syntax "bind " str " => " ident : intentBinding

/-! ## Top-level command -/

syntax (name := intentSpecCmd)
  (docComment)?
  "intent_spec " str " where"
  intentDecl*
  intentBinding* : command

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

/-- Expand an intentFormat to a Format term. -/
scoped syntax "ifmt!" intentFormat : term
macro_rules
  | `(ifmt! raw)                  => `(Format.raw)
  | `(ifmt! address)              => `(Format.address)
  | `(ifmt! tokenAmount $n:num)   => `(Format.tokenAmount $n)
  | `(ifmt! tokenAmount $n:num $s:str) => `(Format.tokenAmount $n (some $s))
  | `(ifmt! enum $s:str)          => `(Format.enum $s)

/-- Expand a hole to a Hole term. -/
scoped syntax "ihole!" intentHole : term
macro_rules
  | `(ihole! $name:ident : $fmt:intentFormat) =>
    `({ param := $(Lean.quote (toString name.getId)), format := ifmt! $fmt : Hole })

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

/-- Expand a statement to a Stmt term. -/
scoped syntax "istmt!" intentStmt : term
macro_rules
  -- emit with holes
  | `(istmt! emit $txt:str [ $holes:intentHole,* ]) =>
    let holeExprs := holes.getElems.map fun h => (⟨h.raw⟩ : Lean.TSyntax `intentHole)
    `(Stmt.emit { text := $txt, holes := [ $[ ihole! $holeExprs ],* ] })
  -- emit without holes
  | `(istmt! emit $txt:str) =>
    `(Stmt.emit { text := $txt, holes := [] })
  -- if/then/else single statements
  | `(istmt! if $cond:intentExpr then $thenS:intentStmt else $elseS:intentStmt) =>
    `(Stmt.ite (iexpr! $cond) [istmt! $thenS] [istmt! $elseS])
  -- if/then/else blocks
  | `(istmt! if $cond:intentExpr then { $thenSs:intentStmt,* } else { $elseSs:intentStmt,* }) =>
    let thenExprs := thenSs.getElems.map fun s => (⟨s.raw⟩ : Lean.TSyntax `intentStmt)
    let elseExprs := elseSs.getElems.map fun s => (⟨s.raw⟩ : Lean.TSyntax `intentStmt)
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

/-- Helper: expand a const declaration to a ConstDef term. -/
scoped syntax "iconst!" "const " ident " := " term : term
macro_rules
  | `(iconst! const $name:ident := $val:term) =>
    `({ name := $(Lean.quote (toString name.getId)), value := .intLit ($val : Int) : ConstDef })

/-- Helper: expand an enum declaration. -/
scoped syntax "ienum!" "enum " ident " {" (num " => " str),* "}" : term
macro_rules
  | `(ienum! enum $name:ident { $[$ns:num => $ss:str],* }) =>
    `({ name := $(Lean.quote (toString name.getId)),
        values := [ $[($ns, $ss)],* ] : EnumDef })

/-- Helper: expand a predicate declaration to an FnDecl term. -/
scoped syntax "ipred!" "predicate " ident "(" intentParam,* ")" " := " intentExpr : term
macro_rules
  | `(ipred! predicate $name:ident ( $params:intentParam,* ) := $body:intentExpr) =>
    let paramExprs := params.getElems.map fun p => (⟨p.raw⟩ : Lean.TSyntax `intentParam)
    `({ name := $(Lean.quote (toString name.getId)),
        params := [ $[ iparam! $paramExprs ],* ],
        returnKind := ReturnKind.bool,
        expr := some (iexpr! $body) : FnDecl })

/-- Helper: expand an intent declaration to an FnDecl term. -/
scoped syntax "iintent!" "intent " ident "(" intentParam,* ")" " where " intentStmt,* : term
macro_rules
  | `(iintent! intent $name:ident ( $params:intentParam,* ) where $stmts:intentStmt,*) =>
    let paramExprs := params.getElems.map fun p => (⟨p.raw⟩ : Lean.TSyntax `intentParam)
    let stmtExprs := stmts.getElems.map fun s => (⟨s.raw⟩ : Lean.TSyntax `intentStmt)
    `({ name := $(Lean.quote (toString name.getId)),
        params := [ $[ iparam! $paramExprs ],* ],
        returnKind := ReturnKind.void,
        body := [ $[ istmt! $stmtExprs ],* ] : FnDecl })

/-- Helper: expand a binding to an IntentBinding term. -/
scoped syntax "ibind!" "bind " str " => " ident : term
macro_rules
  | `(ibind! bind $fnName:str => $intentFn:ident) =>
    `({ functionName := $fnName,
        intentFn := $(Lean.quote (toString intentFn.getId)) : IntentBinding })

/-! ## Main command macro -/

-- We use `macro_rules` to match the `intent_spec` command and expand it.
-- The tricky part is separating decls into constants, enums, fns, and collecting bindings.
-- We do this by generating individual terms and relying on List.filterMap-style separation.

private def mkConstList (decls : Array (Lean.TSyntax `intentDecl)) : Lean.MacroM (Array (Lean.TSyntax `term)) := do
  let mut result := #[]
  for d in decls do
    match d with
    | `(intentDecl| const $name:ident := $val:term) =>
      result := result.push (← `(iconst! const $name := $val))
    | _ => pure ()
  return result

private def mkEnumList (decls : Array (Lean.TSyntax `intentDecl)) : Lean.MacroM (Array (Lean.TSyntax `term)) := do
  let mut result := #[]
  for d in decls do
    match d with
    | `(intentDecl| enum $name:ident { $[$ns:num => $ss:str],* }) =>
      result := result.push (← `(ienum! enum $name { $[$ns => $ss],* }))
    | _ => pure ()
  return result

private def mkFnList (decls : Array (Lean.TSyntax `intentDecl)) : Lean.MacroM (Array (Lean.TSyntax `term)) := do
  let mut result := #[]
  for d in decls do
    match d with
    | `(intentDecl| predicate $name:ident ( $params:intentParam,* ) := $body:intentExpr) =>
      result := result.push (← `(ipred! predicate $name ( $params,* ) := $body))
    | `(intentDecl| intent $name:ident ( $params:intentParam,* ) where $stmts:intentStmt,*) =>
      result := result.push (← `(iintent! intent $name ( $params,* ) where $stmts,*))
    | _ => pure ()
  return result

private def mkBindingList (bindings : Array (Lean.TSyntax `intentBinding)) : Lean.MacroM (Array (Lean.TSyntax `term)) := do
  let mut result := #[]
  for b in bindings do
    match b with
    | `(intentBinding| bind $fnName:str => $intentFn:ident) =>
      result := result.push (← `(ibind! bind $fnName => $intentFn))
    | _ => pure ()
  return result

macro_rules
  | `(command| $[$doc?:docComment]? intent_spec $contractName:str where $decls:intentDecl* $bindings:intentBinding*) => do
    let declArr : Array (Lean.TSyntax `intentDecl) := decls
    let bindArr : Array (Lean.TSyntax `intentBinding) := bindings
    let constTerms ← mkConstList declArr
    let enumTerms ← mkEnumList declArr
    let fnTerms ← mkFnList declArr
    let bindingTerms ← mkBindingList bindArr
    -- Use mkIdent to avoid macro hygiene mangling the definition name and type
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
