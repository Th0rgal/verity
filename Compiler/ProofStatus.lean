namespace Compiler

inductive ProofStatus
  | proved
  | assumed
  | unchecked
  deriving Repr, BEq, DecidableEq, Inhabited

def ProofStatus.toJsonString : ProofStatus → String
  | .proved => "proved"
  | .assumed => "assumed"
  | .unchecked => "unchecked"

end Compiler
