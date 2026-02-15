/-
  Compiler.Linker: External Yul Library Linking

  This module provides functionality to link external Yul library files
  with generated contract code, enabling production cryptographic libraries
  to be used with formally verified contract logic.

  Usage:
    lake exe verity-compiler \
        --link examples/external-libs/PoseidonT3.yul \
        --link examples/external-libs/PoseidonT4.yul \
        -o compiler/yul
-/

import Compiler.Yul.Ast
import Compiler.Yul.PrettyPrint

namespace Compiler.Linker

open Compiler.Yul

/-!
## Yul Library Parsing

External libraries are expected to contain pure Yul function definitions.
We use a simple line-based parser to extract function definitions from library files.
-/

-- Extract function name from a Yul function definition line
private def extractFunctionName (line : String) : Option String :=
  let trimmed := line.trim
  if trimmed.startsWith "function " then
    let afterFunction := trimmed.drop "function ".length
    let beforeParen := afterFunction.takeWhile (· != '(')
    some beforeParen.trim
  else
    none

-- Check if a line starts a function definition
private def isFunctionStart (line : String) : Bool :=
  extractFunctionName line |>.isSome

-- Count braces in a line to track nesting depth
private def countBraces (line : String) : Int :=
  let opens := line.toList.filter (· == '{') |>.length
  let closes := line.toList.filter (· == '}') |>.length
  opens - closes

-- Extract a complete function definition from lines
private partial def extractFunction (lines : List String) : Option (String × List String × List String) :=
  match lines with
  | [] => none
  | firstLine :: rest =>
      match extractFunctionName firstLine with
      | none => none
      | some name =>
          let rec collectBody (remaining : List String) (acc : List String) (depth : Int) : List String × List String :=
            match remaining with
            | [] => (acc.reverse, [])
            | line :: rest' =>
                let newDepth := depth + countBraces line
                let acc' := line :: acc
                if newDepth <= 0 then
                  (acc'.reverse, rest')
                else
                  collectBody rest' acc' newDepth
          let initialDepth := countBraces firstLine
          let (bodyLines, remaining) := collectBody rest [firstLine] initialDepth
          some (name, bodyLines, remaining)

-- Extract all function definitions from library lines
private partial def extractAllFunctions (lines : List String) : List (String × List String) :=
  let rec go (remaining : List String) (acc : List (String × List String)) : List (String × List String) :=
    match remaining with
    | [] => acc.reverse
    | line :: rest =>
        if isFunctionStart line then
          match extractFunction (line :: rest) with
          | none => go rest acc
          | some (name, body, remaining') =>
              go remaining' ((name, body) :: acc)
        else
          go rest acc
  go lines []

/-!
## Library Loading
-/

structure LibraryFunction where
  name : String
  body : List String  -- Raw Yul text lines
  deriving Repr

-- Parse a Yul library file and extract function definitions
def parseLibrary (content : String) : List LibraryFunction :=
  let lines := content.splitOn "\n"
  let functions := extractAllFunctions lines
  functions.map fun (name, body) =>
    { name := name, body := body }

-- Load library from file path
def loadLibrary (path : String) : IO (List LibraryFunction) := do
  let content ← IO.FS.readFile path
  return parseLibrary content

/-!
## Linking
-/

-- Inject library function text directly into rendered Yul output
-- This preserves the exact library code without parsing/re-emitting
def renderWithLibraries (obj : YulObject) (libraries : List LibraryFunction) : String :=
  -- Render the main object
  let mainYul := Yul.render obj

  -- If no libraries, return as-is
  if libraries.isEmpty then
    mainYul
  else
    -- Extract the runtime code section and inject libraries
    -- Find the runtime "code {" line and inject library functions after it
    let lines := mainYul.splitOn "\n"
    let rec insertLibraries (remaining : List String) (acc : List String) (inserted : Bool) (depth : Nat) : List String :=
      match remaining with
      | [] => acc
      | line :: rest =>
          -- Track depth: we want the second "code {" (inside object "runtime")
          let isCodeLine := line.trim.startsWith "code {"
          let newDepth := if isCodeLine then depth + 1 else depth
          if !inserted && newDepth == 2 && isCodeLine then
            -- Found the runtime code section, insert libraries after this line
            let libraryLines := libraries.flatMap fun fn =>
              -- Add proper indentation (3 levels = 12 spaces for runtime code functions)
              fn.body.map fun bodyLine =>
                if bodyLine.trim.isEmpty then bodyLine
                else "            " ++ bodyLine
            insertLibraries rest (acc ++ [line] ++ libraryLines) true newDepth
          else
            insertLibraries rest (acc ++ [line]) inserted newDepth
    let resultLines := insertLibraries lines [] false 0
    String.intercalate "\n" resultLines

/-!
## Validation
-/

-- Collect all external function calls from Yul statements
private partial def collectExternalCalls (stmts : List YulStmt) : List String :=
  let rec fromExpr : YulExpr → List String
    | YulExpr.call name args =>
        -- Consider it external if it's not a builtin Yul opcode
        let builtins := ["add", "sub", "mul", "div", "mod", "sload", "sstore",
                        "caller", "callvalue", "timestamp", "mstore", "mload",
                        "keccak256", "return", "revert", "stop", "eq", "lt",
                        "gt", "iszero", "and", "or", "xor", "not", "shl", "shr",
                        "calldataload", "datacopy", "dataoffset", "datasize",
                        "codecopy", "codesize"]
        let childCalls := args.flatMap fromExpr
        if builtins.contains name then childCalls else name :: childCalls
    | YulExpr.lit _ => []
    | YulExpr.hex _ => []
    | YulExpr.str _ => []
    | YulExpr.ident _ => []

  let rec fromStmt : YulStmt → List String
    | YulStmt.comment _ => []
    | YulStmt.let_ _ value => fromExpr value
    | YulStmt.assign _ value => fromExpr value
    | YulStmt.expr e => fromExpr e
    | YulStmt.if_ cond body => fromExpr cond ++ body.flatMap fromStmt
    | YulStmt.switch expr cases default =>
        fromExpr expr ++
        cases.flatMap (fun (_, body) => body.flatMap fromStmt) ++
        (default.map (·.flatMap fromStmt)).getD []
    | YulStmt.block stmts => stmts.flatMap fromStmt
    | YulStmt.funcDef _ _ _ body => body.flatMap fromStmt

  stmts.flatMap fromStmt

-- Collect all function names defined in library
private def collectLibraryFunctions (libs : List LibraryFunction) : List String :=
  libs.map (·.name)

-- Validate that all external calls are provided by libraries
def validateExternalReferences (obj : YulObject) (libraries : List LibraryFunction) : Except String Unit := do
  let externalCalls := (collectExternalCalls obj.runtimeCode).eraseDups
  let providedFunctions := collectLibraryFunctions libraries
  let missingFunctions := externalCalls.filter fun call =>
    !providedFunctions.contains call
  if missingFunctions.isEmpty then
    pure ()
  else
    throw s!"Unresolved external references: {String.intercalate ", " missingFunctions}"

end Compiler.Linker
