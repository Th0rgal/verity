import Compiler.Yul.Ast
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.MappingSlot
import Compiler.Proofs.YulGeneration.RuntimeTypes
import Compiler.Proofs.YulGeneration.ReferenceOracle.Builtins

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration
open Compiler.Proofs

/-!
Reference oracle only.

This module preserves Verity's historical `legacyExecYulFuel` runtime semantics for
regression tests and bridge comparisons. EVMYulLean is the trusted semantic
target for the current retargeting path; this file is not part of that trust
boundary.
-/

/-! ## Yul Runtime Semantics (Layer 3 Foundation)

This module defines the historical fuel-based execution semantics for a Yul
runtime program. Shared transaction/result/state plumbing lives in
`RuntimeTypes.lean` so native EVMYulLean proofs can use those data structures
without importing this legacy interpreter.
-/

/-!
Runtime Yul mapping slots are derived via `keccak(baseSlot, key)`. Proof
semantics call through `MappingSlot`; the active backend is `keccak` (see
`activeMappingSlotBackend`), so `mappingSlot`/`sload`/`sstore` semantics are
aligned with Solidity's keccak-derived flat storage slot layout.
-/

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
    if func = "tload" then
      match argVals with
      | [slot] => some (state.transientStorage (slot % Compiler.Constants.evmModulus))
      | _ => none
    else if func = "mload" then
      match argVals with
      | [offset] => some (state.memory offset)
      | _ => none
    else if func = "keccak256" then
      match argVals with
      | [offset, size] => some (abstractKeccakMemorySlice state.memory offset size)
      | _ => none
    else
      Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext
        Compiler.Proofs.YulGeneration.defaultBuiltinBackend
        state.storage state.sender state.msgValue state.thisAddress state.blockTimestamp
        state.blockNumber state.chainId state.blobBaseFee state.selector state.calldata func argVals
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

def YulState.appendYulLog (s : YulState) (offset size : Nat)
    (topics : List Nat) : YulState :=
  { s with events := s.events ++ [encodeYulLogEvent s.memory offset size topics] }

def applyYulLogCall? (state : YulState) (func : String)
    (argVals : List Nat) : Option YulState :=
  match func, argVals with
  | "log0", [offset, size] =>
      some (state.appendYulLog offset size [])
  | "log1", [offset, size, topic0] =>
      some (state.appendYulLog offset size [topic0])
  | "log2", [offset, size, topic0, topic1] =>
      some (state.appendYulLog offset size [topic0, topic1])
  | "log3", [offset, size, topic0, topic1, topic2] =>
      some (state.appendYulLog offset size [topic0, topic1, topic2])
  | "log4", [offset, size, topic0, topic1, topic2, topic3] =>
      some (state.appendYulLog offset size [topic0, topic1, topic2, topic3])
  | _, _ => none

inductive YulExecTarget
  | stmt (s : YulStmt)
  | stmts (ss : List YulStmt)

def legacyExecYulFuel : Nat → YulState → YulExecTarget → YulExecResult
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
              | .call "tstore" [offsetExpr, valExpr] =>
                  match evalYulExpr state offsetExpr, evalYulExpr state valExpr with
                  | some offset, some val =>
                      .continue {
                        state with
                        transientStorage := fun o =>
                          if o = offset then val else state.transientStorage o
                      }
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
              | .call func args =>
                  if isYulLogName func then
                    match evalYulExprs state args with
                    | some argVals =>
                        match applyYulLogCall? state func argVals with
                        | some next => .continue next
                        | none => .revert state
                    | none => .revert state
                  else
                    match evalYulExpr state e with
                    | some _ => .continue state
                    | none => .revert state
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
                    legacyExecYulFuel fuel state (.stmts body)
              | none => .revert state
          | .switch expr cases defaultCase =>
              match evalYulExpr state expr with
              | some v =>
                  match cases.find? (fun x => decide (x.fst = v)) with
                  | some (_, body) => legacyExecYulFuel fuel state (.stmts body)
                  | none =>
                      match defaultCase with
                      | some body => legacyExecYulFuel fuel state (.stmts body)
                      | none => .continue state
              | none => .revert state
          | .for_ init cond post body =>
              -- Execute init, then loop: check cond, run body, run post, repeat
              match legacyExecYulFuel fuel state (.stmts init) with
              | .continue s' =>
                  match evalYulExpr s' cond with
                  | some v =>
                      if v = 0 then .continue s'
                      else
                        match legacyExecYulFuel fuel s' (.stmts body) with
                        | .continue s'' =>
                            match legacyExecYulFuel fuel s'' (.stmts post) with
                            | .continue s''' =>
                                legacyExecYulFuel fuel s''' (.stmt (.for_ [] cond post body))
                            | other => other
                        | other => other
                  | none => .revert s'
              | other => other
          | .block stmts => legacyExecYulFuel fuel state (.stmts stmts)
          | .funcDef _ _ _ _ => .continue state
      | .stmts [] => .continue state
      | .stmts (stmt :: rest) =>
          match legacyExecYulFuel fuel state (.stmt stmt) with
          | .continue s' => legacyExecYulFuel fuel s' (.stmts rest)
          | .return v s => .return v s
          | .stop s => .stop s
          | .revert s => .revert s
def execYulStmtFuel (fuel : Nat) (state : YulState) (stmt : YulStmt) : YulExecResult :=
  legacyExecYulFuel fuel state (.stmt stmt)

def execYulStmtsFuel (fuel : Nat) (state : YulState) (stmts : List YulStmt) : YulExecResult :=
  legacyExecYulFuel fuel state (.stmts stmts)

set_option allowUnsafeReducibility true in
attribute [reducible] legacyExecYulFuel


noncomputable def execYulStmt (state : YulState) (stmt : YulStmt) : YulExecResult :=
  execYulStmtFuel (sizeOf stmt + 1) state stmt

noncomputable def execYulStmts (state : YulState) (stmts : List YulStmt) : YulExecResult :=
  execYulStmtsFuel (sizeOf stmts + 1) state stmts

/-- Execute a Yul runtime program with selector-aware calldata -/
noncomputable def interpretYulRuntime (runtimeCode : List YulStmt) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (events : List (List Nat) := []) : YulResult :=
  let initialState := YulState.initial tx storage events
  match execYulStmts initialState runtimeCode with
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
        finalStorage := storage
        finalMappings := Compiler.Proofs.storageAsMappings storage
        events := initialState.events }

/-- Interpret a Yul object by executing its runtime code. -/
noncomputable def interpretYulObject (obj : YulObject) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (events : List (List Nat) := []) : YulResult :=
  interpretYulRuntime obj.runtimeCode tx storage events

end Compiler.Proofs.YulGeneration
