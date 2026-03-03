import Compiler.Yul.Ast
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.MappingSlot
import Compiler.Proofs.YulGeneration.Builtins

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration
open Compiler.Proofs

/-! ## Yul Runtime Semantics (Layer 3 Foundation)

This module defines execution semantics for a Yul runtime program. It mirrors
IRInterpreter but models selector-aware calldata so `emitYul`'s runtime switch
behaves correctly.
-/

/-- Selector expression used by the runtime switch. -/
def selectorExpr : YulExpr :=
  YulExpr.call "shr" [
    YulExpr.lit selectorShift,
    YulExpr.call "calldataload" [YulExpr.lit 0]
  ]

/-!
Runtime Yul mapping slots are derived via `keccak(baseSlot, key)`. Proof
semantics call through `MappingSlot`; the active backend is `keccak` (see
`activeMappingSlotBackend`), so `mappingSlot`/`sload`/`sstore` semantics are
aligned with Solidity's keccak-derived flat storage slot layout.
-/

/-! ## Execution State -/

structure YulState where
  vars : List (String × Nat)
  storage : Nat → Nat
  memory : Nat → Nat
  calldata : List Nat
  selector : Nat
  returnValue : Option Nat
  sender : Nat
  deriving Nonempty

structure YulTransaction where
  sender : Nat
  functionSelector : Nat
  args : List Nat
  deriving Repr

/-- Initial state for Yul execution -/
def YulState.initial (tx : YulTransaction) (storage : Nat → Nat) : YulState :=
  { vars := []
    storage := storage
    memory := fun _ => 0
    calldata := tx.args
    selector := tx.functionSelector
    returnValue := none
    sender := tx.sender }

/-- Lookup variable in state -/
def YulState.getVar (s : YulState) (name : String) : Option Nat :=
  s.vars.find? (·.1 == name) |>.map (·.2)

/-- Set variable in state -/
def YulState.setVar (s : YulState) (name : String) (value : Nat) : YulState :=
  { s with vars := (name, value) :: s.vars.filter (·.1 != name) }

/-! ## Yul Expression Evaluation -/

/-! Size measures for termination proofs. -/
mutual
def exprSize : YulExpr → Nat
  | .call _ args => exprsSize args + 2
  | _ => 1

def exprsSize : List YulExpr → Nat
  | [] => 0
  | e :: es => exprSize e + exprsSize es + 1
end

mutual

/-- Evaluate a list of Yul expressions -/
def evalYulExprs (state : YulState) : List YulExpr → Option (List Nat)
  | [] => some []
  | e :: es => do
    let v ← evalYulExpr state e
    let vs ← evalYulExprs state es
    pure (v :: vs)
termination_by es => exprsSize es
decreasing_by
  all_goals
    simp [exprsSize]
    omega

def evalYulCall (state : YulState) (func : String) : List YulExpr → Option Nat
  | args => do
    let argVals ← evalYulExprs state args
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackend
      Compiler.Proofs.YulGeneration.defaultBuiltinBackend
      state.storage state.sender state.selector state.calldata func argVals
termination_by args => exprsSize args + 1
decreasing_by
  omega

/-- Evaluate a Yul expression -/
def evalYulExpr (state : YulState) : YulExpr → Option Nat
  | .lit n => some n
  | .hex n => some n
  | .str _ => none
  | .ident name => state.getVar name
  | .call func args => evalYulCall state func args
termination_by e => exprSize e
decreasing_by
  simp [exprSize]

end

/-! ## Yul Statement Execution -/

inductive YulExecResult
  | continue (state : YulState)
  | return (value : Nat) (state : YulState)
  | stop (state : YulState)
  | revert (state : YulState)
  deriving Nonempty

inductive YulExecTarget
  | stmt (s : YulStmt)
  | stmts (ss : List YulStmt)

def execYulFuel : Nat → YulState → YulExecTarget → YulExecResult
  | _, state, .stmts [] => .continue state
  | _, state, .stmt (YulStmt.funcDef _ _ _ _) => .continue state
  | 0, state, _ => .revert state
  | Nat.succ fuel, state, target =>
      match target with
      | .stmt stmt =>
          match stmt with
          | .comment _ => .continue state
          | .let_ name value =>
              match evalYulExpr state value with
              | some v => .continue (state.setVar name v)
              | none => .revert state
          | .letMany _ _ => .revert state
          | .assign name value =>
              match evalYulExpr state value with
              | some v => .continue (state.setVar name v)
              | none => .revert state
          | .leave => .continue state
          | .expr e =>
              match e with
              | .call "sstore" [slotExpr, valExpr] =>
                  match slotExpr with
                  | .call "mappingSlot" [baseExpr, keyExpr] =>
                      match evalYulExpr state baseExpr, evalYulExpr state keyExpr, evalYulExpr state valExpr with
                      | some baseSlot, some key, some val =>
                          let updated := Compiler.Proofs.abstractStoreMappingEntry
                            state.storage baseSlot key val
                          .continue {
                            state with
                            storage := updated
                          }
                      | _, _, _ => .revert state
                  | _ =>
                      match evalYulExpr state slotExpr, evalYulExpr state valExpr with
                      | some slot, some val =>
                          let updated := Compiler.Proofs.abstractStoreStorageOrMapping
                            state.storage slot val
                          .continue {
                            state with
                            storage := updated
                          }
                      | _, _ => .revert state
              | .call "mstore" [offsetExpr, valExpr] =>
                  match evalYulExpr state offsetExpr, evalYulExpr state valExpr with
                  | some offset, some val =>
                      .continue { state with memory := fun o => if o = offset then val else state.memory o }
                  | _, _ => .revert state
              | .call "stop" [] => .stop state
              | .call "return" [offsetExpr, sizeExpr] =>
                  match evalYulExpr state offsetExpr, evalYulExpr state sizeExpr with
                  | some offset, some size =>
                      if size = 32 then
                        .return (state.memory offset) state
                      else
                        .return 0 state
                  | _, _ => .revert state
              | .call "revert" [_, _] => .revert state
              | _ =>
                  match evalYulExpr state e with
                  | some _ => .continue state
                  | none => .revert state
          | .if_ cond body =>
              match evalYulExpr state cond with
              | some v =>
                  if v = 0 then
                    .continue state
                  else
                    execYulFuel fuel state (.stmts body)
              | none => .revert state
          | .switch expr cases defaultCase =>
              match evalYulExpr state expr with
              | some v =>
                  match cases.find? (fun x => decide (x.fst = v)) with
                  | some (_, body) => execYulFuel fuel state (.stmts body)
                  | none =>
                      match defaultCase with
                      | some body => execYulFuel fuel state (.stmts body)
                      | none => .continue state
              | none => .revert state
          | .for_ init cond post body =>
              -- Execute init, then loop: check cond, run body, run post, repeat
              match execYulFuel fuel state (.stmts init) with
              | .continue s' =>
                  match evalYulExpr s' cond with
                  | some v =>
                      if v = 0 then .continue s'
                      else
                        match execYulFuel fuel s' (.stmts body) with
                        | .continue s'' =>
                            match execYulFuel fuel s'' (.stmts post) with
                            | .continue s''' =>
                                execYulFuel fuel s''' (.stmt (.for_ [] cond post body))
                            | other => other
                        | other => other
                  | none => .revert s'
              | other => other
          | .block stmts => execYulFuel fuel state (.stmts stmts)
          | .funcDef _ _ _ _ => .continue state
      | .stmts [] => .continue state
      | .stmts (stmt :: rest) =>
          match execYulFuel fuel state (.stmt stmt) with
          | .continue s' => execYulFuel fuel s' (.stmts rest)
          | .return v s => .return v s
          | .stop s => .stop s
          | .revert s => .revert s
def execYulStmtFuel (fuel : Nat) (state : YulState) (stmt : YulStmt) : YulExecResult :=
  execYulFuel fuel state (.stmt stmt)

def execYulStmtsFuel (fuel : Nat) (state : YulState) (stmts : List YulStmt) : YulExecResult :=
  execYulFuel fuel state (.stmts stmts)

set_option allowUnsafeReducibility true in
attribute [reducible] execYulFuel


noncomputable def execYulStmt (state : YulState) (stmt : YulStmt) : YulExecResult :=
  execYulStmtFuel (sizeOf stmt + 1) state stmt

noncomputable def execYulStmts (state : YulState) (stmts : List YulStmt) : YulExecResult :=
  execYulStmtsFuel (sizeOf stmts + 1) state stmts

structure YulResult where
  success : Bool
  returnValue : Option Nat
  finalStorage : Nat → Nat
  finalMappings : Nat → Nat → Nat

/-- Execute a Yul runtime program with selector-aware calldata -/
noncomputable def interpretYulRuntime (runtimeCode : List YulStmt) (tx : YulTransaction)
    (storage : Nat → Nat) : YulResult :=
  let initialState := YulState.initial tx storage
  match execYulStmts initialState runtimeCode with
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage }
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := storage
        finalMappings := Compiler.Proofs.storageAsMappings storage }

/-- Interpret a Yul object by executing its runtime code. -/
noncomputable def interpretYulObject (obj : YulObject) (tx : YulTransaction)
    (storage : Nat → Nat) : YulResult :=
  interpretYulRuntime obj.runtimeCode tx storage

end Compiler.Proofs.YulGeneration
