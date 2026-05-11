import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Yul

/-! ## Fuel-Parametric IR Aliases

These names are shared by the source-to-IR proof stack and the legacy IR/Yul
equivalence stack. They are intentionally kept free of the reference-oracle Yul
interpreter so IR-generation compiler-correctness modules do not need to import
`Compiler.Proofs.YulGeneration.Equivalence` just to talk about fuel-indexed IR
execution.
-/

abbrev execIRStmtFuel := @execIRStmt
abbrev execIRStmtsFuel := @execIRStmts

theorem execIRStmtsFuel_nil (fuel : Nat) (state : IRState) :
    execIRStmtsFuel fuel state [] = .continue state := by
  simp [execIRStmtsFuel, execIRStmts]

theorem execIRStmtsFuel_cons
    (fuel : Nat) (state : IRState) (stmt : YulStmt) (rest : List YulStmt) :
    execIRStmtsFuel (Nat.succ fuel) state (stmt :: rest) =
      match execIRStmtFuel fuel state stmt with
      | .continue s' => execIRStmtsFuel fuel s' rest
      | .return v s => .return v s
      | .stop s => .stop s
      | .revert s => .revert s := by
  rfl

def execIRFunctionFuel
    (fuel : Nat) (fn : IRFunction) (args : List Nat)
    (initialState : IRState) :
    IRResult :=
  let stateWithParams := fn.params.zip args |>.foldl
    (fun s (p, v) => s.setVar p.name v)
    initialState
  match execIRStmtsFuel fuel stateWithParams fn.body with
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events }

def execIRFunctionFuel_adequate_goal
    (fn : IRFunction) (args : List Nat) (initialState : IRState) : Prop :=
  execIRFunctionFuel (sizeOf fn.body + 1) fn args initialState =
    execIRFunction fn args initialState

/-- Fuel adequacy holds by `rfl` because the fuel aliases resolve to the total
IR executors. -/
theorem execIRFunctionFuel_adequate
    (fn : IRFunction) (args : List Nat) (initialState : IRState) :
    execIRFunctionFuel_adequate_goal fn args initialState := by
  unfold execIRFunctionFuel_adequate_goal execIRFunctionFuel execIRFunction
    execIRStmtsFuel
  rfl

end Compiler.Proofs.YulGeneration
