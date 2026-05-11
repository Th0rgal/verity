namespace Compiler.Proofs.YulGeneration

/-- Yul log builtin names accepted by the proof-side runtime models. -/
def isYulLogName (func : String) : Bool :=
  func == "log0" || func == "log1" || func == "log2" ||
    func == "log3" || func == "log4"

end Compiler.Proofs.YulGeneration
