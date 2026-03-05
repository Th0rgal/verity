namespace Compiler.CompilationModel

/-- Prefix prepended to internal function names in generated Yul to avoid
    collision with external function names and EVM/Yul builtins.
    Used by compileExpr, compileStmt, and compileInternalFunction. -/
def internalFunctionPrefix : String := "internal_"

/-- Build the Yul-level name for an internal function. -/
def internalFunctionYulName (name : String) : String :=
  s!"{internalFunctionPrefix}{name}"

def pickFreshName (base : String) (usedNames : List String) : String :=
  if !usedNames.contains base then
    base
  else
    let rec go (suffix : Nat) (remaining : Nat) : String :=
      let candidate := s!"{base}_{suffix}"
      if !usedNames.contains candidate then
        candidate
      else
        match remaining with
        | 0 => s!"{base}_fresh"
        | n + 1 => go (suffix + 1) n
    go 1 usedNames.length

end Compiler.CompilationModel
