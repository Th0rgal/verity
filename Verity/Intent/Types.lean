/-
  Verity.Intent.Types: AST for the provable intent DSL.

  A minimal, terminating, pure language that maps
  (selector, calldata) → (templateId, hole values).

  See PR #1676 for the full design document.

  Phase 2: adds forEach loops (unrolled at compile time), index/length
  expressions, and enum format support.
-/
import Compiler.CompilationModel.Types

namespace Verity.Intent

open Compiler.CompilationModel (ParamType)

/-! ## Format Directives

Describe how to render a parameter value in a template hole.
-/

inductive Format where
  /-- Display the value as-is (decimal for ints, hex for addresses/bytes). -/
  | raw
  /-- Display as a token amount: divide by 10^decimals, append symbol if given. -/
  | tokenAmount (decimals : Nat) (symbol : Option String := none)
  /-- Display as a checksummed or named address. -/
  | address
  /-- Display using an enum mapping: look up the integer value in the named EnumDef. -/
  | enum (enumName : String)
  deriving Repr, BEq

/-! ## Templates

A template is a display string with typed holes.
Example: "Transfer {amount} to {to}" with holes for amount and to.
-/

/-- A hole in a template: which parameter to display and how. -/
structure Hole where
  /-- Parameter name (must match a function parameter). -/
  param : String
  /-- How to format this parameter for display. -/
  format : Format
  deriving Repr, BEq

/-- A template: a display string with typed holes.
    Holes are referenced by `{name}` in the text. -/
structure Template where
  /-- The display string with `{name}` placeholders. -/
  text : String
  /-- One entry per placeholder, specifying which param and how to format it. -/
  holes : List Hole := []
  deriving Repr, BEq

/-! ## Expressions

Pure expressions that evaluate to a value.
Used in conditions, function arguments, and hole values.
-/

inductive Expr where
  /-- Reference to a function parameter by name. -/
  | param (name : String)
  /-- Integer literal (covers uint256, int256, uint8, bool). -/
  | intLit (n : Int)
  /-- String literal. -/
  | strLit (s : String)
  /-- Equality comparison. -/
  | eq (a b : Expr)
  /-- Inequality comparison. -/
  | ne (a b : Expr)
  /-- Less-than (unsigned for uint). -/
  | lt (a b : Expr)
  /-- Greater-than (unsigned for uint). -/
  | gt (a b : Expr)
  /-- Less-or-equal. -/
  | le (a b : Expr)
  /-- Greater-or-equal. -/
  | ge (a b : Expr)
  /-- Logical AND (both operands evaluated). -/
  | and (a b : Expr)
  /-- Logical OR (both operands evaluated). -/
  | or (a b : Expr)
  /-- Logical NOT. -/
  | not (a : Expr)
  /-- Call a named helper function. -/
  | call (fnName : String) (args : List Expr)
  /-- Array indexing: `array[idx]`. -/
  | index (array : Expr) (idx : Expr)
  /-- Array length: `array.length`. -/
  | length (array : Expr)
  deriving Repr

/-! ## Statements

Statements that execute sequentially and may emit template records.
-/

inductive Stmt where
  /-- Emit a template record (the core output operation). -/
  | emit (tmpl : Template)
  /-- Conditional: if cond then thenBranch else elseBranch. -/
  | ite (cond : Expr) (thenBranch : List Stmt) (elseBranch : List Stmt)
  /-- Iterate over an array parameter: `for x in arr { body }`.
      The array length must be statically known (from ABI fixed-size arrays)
      so the loop can be unrolled at circuit compile time. -/
  | forEach (var : String) (array : Expr) (body : List Stmt)
  /-- Call a void helper function. -/
  | call (fnName : String) (args : List Expr)
  deriving Repr

/-! ## Function Declarations

Three kinds: intent (void/emits), predicate (Bool), formatter (String).
-/

/-- Return type of a helper function. -/
inductive ReturnKind where
  | void    -- intent functions: emit templates
  | bool    -- predicate helpers: return a boolean
  | string  -- formatter helpers: return a formatted string
  deriving Repr, BEq

/-- A function declaration in the intent DSL. -/
structure FnDecl where
  /-- Function name (unique within an IntentSpec). -/
  name : String
  /-- Parameters with their ABI types. -/
  params : List (String × ParamType)
  /-- What kind of value this function returns. -/
  returnKind : ReturnKind
  /-- Statement body (for void functions). -/
  body : List Stmt := []
  /-- Expression body (for bool/string functions). -/
  expr : Option Expr := none
  deriving Repr

/-! ## Top-Level Declarations -/

/-- An enum mapping: integer values → display strings.
    Example: { 1 → "Stable", 2 → "Variable" } -/
structure EnumDef where
  name : String
  values : List (Int × String)
  deriving Repr

/-- A named constant. -/
structure ConstDef where
  name : String
  value : Expr
  deriving Repr

/-- Binds a contract function (by name) to an intent function. -/
structure IntentBinding where
  /-- The contract function name (must match CompilationModel.FunctionSpec.name). -/
  functionName : String
  /-- The intent function to invoke for this selector. -/
  intentFn : String
  deriving Repr

/-- Top-level intent specification for a contract. -/
structure IntentSpec where
  /-- Contract name (must match CompilationModel.name). -/
  contractName : String
  /-- All function declarations (intents, predicates, formatters). -/
  fns : List FnDecl := []
  /-- Enum definitions for display. -/
  enums : List EnumDef := []
  /-- Named constants. -/
  constants : List ConstDef := []
  /-- Bindings from contract functions to intent functions. -/
  bindings : List IntentBinding := []
  deriving Repr

end Verity.Intent
