/-
  Neutral EVMYulLean bridge-fragment predicates.

  This module contains only the syntactic builtin set and `Bridged*` Yul
  fragment predicates used by native closure proofs. It deliberately avoids the
  legacy Yul reference oracle and the retarget executor equivalence stack.
-/

import Compiler.Yul.Ast
import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Proofs.IRGeneration

/-- The set of builtins for which the native and transition backends produce
    identical results in the transition bridge. Kept here so native
    closure proofs can name the supported fragment without importing the legacy
    retarget executor theorem stack. -/
def bridgedBuiltins : List String :=
  ["add", "sub", "mul", "div", "mod",
   "lt", "gt", "eq", "iszero",
   "and", "or", "xor", "not", "shl", "shr",
   "addmod", "mulmod", "byte",
   "slt", "sgt",
   "exp", "sdiv", "smod", "sar", "signextend",
   "caller", "address", "callvalue", "timestamp",
   "number", "chainid", "blobbasefee",
   "calldataload", "calldatasize",
   "sload", "mappingSlot"]

/-- Every builtin handled by the legacy context evaluator currently has an
    EVMYulLean bridge lemma. -/
def unbridgedBuiltins : List String := []

def allowedExprCallName (func : String) : Prop :=
  func ∈ bridgedBuiltins ∨ func = "tload" ∨ func = "mload" ∨ func = "keccak256"

inductive BridgedExpr : Compiler.Yul.YulExpr → Prop
  | lit (n : Nat) : BridgedExpr (.lit n)
  | hex (n : Nat) : BridgedExpr (.hex n)
  | str (s : String) : BridgedExpr (.str s)
  | ident (name : String) : BridgedExpr (.ident name)
  | call (func : String) (args : List Compiler.Yul.YulExpr)
      (hName : allowedExprCallName func)
      (hArgs : ∀ arg ∈ args, BridgedExpr arg) :
      BridgedExpr (.call func args)

inductive BridgedStraightStmt : Compiler.Yul.YulStmt → Prop
  | comment (text : String) : BridgedStraightStmt (.comment text)
  | let_ (name : String) (value : Compiler.Yul.YulExpr)
      (hValue : BridgedExpr value) :
      BridgedStraightStmt (.let_ name value)
  | letMany (names : List String) (value : Compiler.Yul.YulExpr) :
      BridgedStraightStmt (.letMany names value)
  | assign (name : String) (value : Compiler.Yul.YulExpr)
      (hValue : BridgedExpr value) :
      BridgedStraightStmt (.assign name value)
  | leave : BridgedStraightStmt .leave
  | expr_sstore_mapping (baseExpr keyExpr valExpr : Compiler.Yul.YulExpr)
      (hBase : BridgedExpr baseExpr) (hKey : BridgedExpr keyExpr)
      (hVal : BridgedExpr valExpr) :
      BridgedStraightStmt
        (.expr (.call "sstore" [.call "mappingSlot" [baseExpr, keyExpr], valExpr]))
  | expr_sstore_lit (slot : Nat) (valExpr : Compiler.Yul.YulExpr)
      (hVal : BridgedExpr valExpr) :
      BridgedStraightStmt (.expr (.call "sstore" [.lit slot, valExpr]))
  | expr_sstore_ident (slotName : String) (valExpr : Compiler.Yul.YulExpr)
      (hVal : BridgedExpr valExpr) :
      BridgedStraightStmt (.expr (.call "sstore" [.ident slotName, valExpr]))
  | expr_sstore_add (leftExpr rightExpr valExpr : Compiler.Yul.YulExpr)
      (hLeft : BridgedExpr leftExpr) (hRight : BridgedExpr rightExpr)
      (hVal : BridgedExpr valExpr) :
      BridgedStraightStmt
        (.expr (.call "sstore" [.call "add" [leftExpr, rightExpr], valExpr]))
  | expr_mstore (offsetExpr valExpr : Compiler.Yul.YulExpr)
      (hOffset : BridgedExpr offsetExpr) (hVal : BridgedExpr valExpr) :
      BridgedStraightStmt (.expr (.call "mstore" [offsetExpr, valExpr]))
  | expr_tstore (offsetExpr valExpr : Compiler.Yul.YulExpr)
      (hOffset : BridgedExpr offsetExpr) (hVal : BridgedExpr valExpr) :
      BridgedStraightStmt (.expr (.call "tstore" [offsetExpr, valExpr]))
  | expr_stop : BridgedStraightStmt (.expr (.call "stop" []))
  | expr_return (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
      (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
      BridgedStraightStmt (.expr (.call "return" [offsetExpr, sizeExpr]))
  | expr_revert (offsetExpr sizeExpr : Compiler.Yul.YulExpr) :
      BridgedStraightStmt (.expr (.call "revert" [offsetExpr, sizeExpr]))
  | expr_log (func : String) (args : List Compiler.Yul.YulExpr)
      (hLog : isYulLogName func = true)
      (hArgs : ∀ arg ∈ args, BridgedExpr arg) :
      BridgedStraightStmt (.expr (.call func args))
  | funcDef (name : String) (params rets : List String)
      (body : List Compiler.Yul.YulStmt) :
      BridgedStraightStmt (.funcDef name params rets body)

def BridgedStraightStmts (stmts : List Compiler.Yul.YulStmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedStraightStmt stmt

theorem BridgedStraightStmts_nil : BridgedStraightStmts [] := by
  intro stmt hMem
  cases hMem

theorem BridgedStraightStmts_cons {stmt : Compiler.Yul.YulStmt}
    {stmts : List Compiler.Yul.YulStmt}
    (hStmt : BridgedStraightStmt stmt) (hStmts : BridgedStraightStmts stmts) :
    BridgedStraightStmts (stmt :: stmts) := by
  intro s hMem
  cases hMem with
  | head => exact hStmt
  | tail _ hTail => exact hStmts s hTail

theorem BridgedStraightStmts_append {xs ys : List Compiler.Yul.YulStmt}
    (hXs : BridgedStraightStmts xs) (hYs : BridgedStraightStmts ys) :
    BridgedStraightStmts (xs ++ ys) := by
  intro stmt hMem
  simp only [List.mem_append] at hMem
  cases hMem with
  | inl h => exact hXs stmt h
  | inr h => exact hYs stmt h

theorem BridgedStraightStmts_singleton {stmt : Compiler.Yul.YulStmt}
    (hStmt : BridgedStraightStmt stmt) : BridgedStraightStmts [stmt] :=
  BridgedStraightStmts_cons hStmt BridgedStraightStmts_nil

theorem BridgedStraightStmts_snoc {xs : List Compiler.Yul.YulStmt}
    {y : Compiler.Yul.YulStmt}
    (hXs : BridgedStraightStmts xs) (hY : BridgedStraightStmt y) :
    BridgedStraightStmts (xs ++ [y]) :=
  BridgedStraightStmts_append hXs (BridgedStraightStmts_singleton hY)

theorem BridgedStraightStmts_map_mstore
    (pairs : List (Compiler.Yul.YulExpr × Compiler.Yul.YulExpr))
    (hPairs : ∀ p ∈ pairs, BridgedExpr p.1 ∧ BridgedExpr p.2) :
    BridgedStraightStmts
      (pairs.map fun p =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "mstore" [p.1, p.2])) := by
  induction pairs with
  | nil => exact BridgedStraightStmts_nil
  | cons p rest ih =>
      have hHead : BridgedExpr p.1 ∧ BridgedExpr p.2 := hPairs p (by simp)
      have hRest : ∀ q ∈ rest, BridgedExpr q.1 ∧ BridgedExpr q.2 := by
        intro q hq
        exact hPairs q (by simp [hq])
      exact BridgedStraightStmts_cons
        (BridgedStraightStmt.expr_mstore p.1 p.2 hHead.1 hHead.2)
        (ih hRest)

theorem BridgedStraightStmts_map_tstore
    (pairs : List (Compiler.Yul.YulExpr × Compiler.Yul.YulExpr))
    (hPairs : ∀ p ∈ pairs, BridgedExpr p.1 ∧ BridgedExpr p.2) :
    BridgedStraightStmts
      (pairs.map fun p =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "tstore" [p.1, p.2])) := by
  induction pairs with
  | nil => exact BridgedStraightStmts_nil
  | cons p rest ih =>
      have hHead : BridgedExpr p.1 ∧ BridgedExpr p.2 := hPairs p (by simp)
      have hRest : ∀ q ∈ rest, BridgedExpr q.1 ∧ BridgedExpr q.2 := by
        intro q hq
        exact hPairs q (by simp [hq])
      exact BridgedStraightStmts_cons
        (BridgedStraightStmt.expr_tstore p.1 p.2 hHead.1 hHead.2)
        (ih hRest)

def BridgedSwitchCases (cases : List (Nat × List Compiler.Yul.YulStmt)) : Prop :=
  ∀ scrutinee value body,
    cases.find? (fun x => decide (x.fst = scrutinee)) = some (value, body) →
      BridgedStraightStmts body

inductive BridgedStmt : Compiler.Yul.YulStmt → Prop
  | straight (stmt : Compiler.Yul.YulStmt)
      (hStmt : BridgedStraightStmt stmt) :
      BridgedStmt stmt
  | block (stmts : List Compiler.Yul.YulStmt)
      (hStmts : ∀ stmt ∈ stmts, BridgedStmt stmt) :
      BridgedStmt (.block stmts)
  | if_ (cond : Compiler.Yul.YulExpr) (body : List Compiler.Yul.YulStmt)
      (hCond : BridgedExpr cond)
      (hBody : ∀ stmt ∈ body, BridgedStmt stmt) :
      BridgedStmt (.if_ cond body)
  | «switch» (expr : Compiler.Yul.YulExpr)
      (cases : List (Nat × List Compiler.Yul.YulStmt))
      (defaultCase : Option (List Compiler.Yul.YulStmt))
      (hExpr : BridgedExpr expr)
      (hCases : ∀ scrutinee value body,
        cases.find? (fun x => decide (x.fst = scrutinee)) = some (value, body) →
        ∀ stmt ∈ body, BridgedStmt stmt)
      (hDefault : ∀ body, defaultCase = some body →
        ∀ stmt ∈ body, BridgedStmt stmt) :
      BridgedStmt (.switch expr cases defaultCase)
  | for_ (init : List Compiler.Yul.YulStmt) (cond : Compiler.Yul.YulExpr)
      (post body : List Compiler.Yul.YulStmt)
      (hInit : ∀ stmt ∈ init, BridgedStmt stmt)
      (hCond : BridgedExpr cond)
      (hPost : ∀ stmt ∈ post, BridgedStmt stmt)
      (hBody : ∀ stmt ∈ body, BridgedStmt stmt) :
      BridgedStmt (.for_ init cond post body)

def BridgedStmts (stmts : List Compiler.Yul.YulStmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedStmt stmt

theorem BridgedStmts_nil : BridgedStmts [] := by
  intro stmt hMem
  cases hMem

theorem BridgedStmts_cons {stmt : Compiler.Yul.YulStmt}
    {stmts : List Compiler.Yul.YulStmt}
    (hStmt : BridgedStmt stmt) (hStmts : BridgedStmts stmts) :
    BridgedStmts (stmt :: stmts) := by
  intro s hMem
  cases hMem with
  | head => exact hStmt
  | tail _ hTail => exact hStmts s hTail

theorem BridgedStmts_append {xs ys : List Compiler.Yul.YulStmt}
    (hXs : BridgedStmts xs) (hYs : BridgedStmts ys) :
    BridgedStmts (xs ++ ys) := by
  intro stmt hMem
  simp only [List.mem_append] at hMem
  cases hMem with
  | inl h => exact hXs stmt h
  | inr h => exact hYs stmt h

theorem BridgedStmts_singleton {stmt : Compiler.Yul.YulStmt}
    (hStmt : BridgedStmt stmt) : BridgedStmts [stmt] :=
  BridgedStmts_cons hStmt BridgedStmts_nil

theorem BridgedStmts_snoc {xs : List Compiler.Yul.YulStmt}
    {y : Compiler.Yul.YulStmt}
    (hXs : BridgedStmts xs) (hY : BridgedStmt y) :
    BridgedStmts (xs ++ [y]) :=
  BridgedStmts_append hXs (BridgedStmts_singleton hY)

theorem bridgedExpr_keccak256 (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "keccak256" [offsetExpr, sizeExpr]) := by
  refine BridgedExpr.call "keccak256" _ (Or.inr (Or.inr (Or.inr rfl))) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact hOffset
  · exact hSize

theorem bridgedExpr_mload (offsetExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "mload" [offsetExpr]) := by
  refine BridgedExpr.call "mload" _ (Or.inr (Or.inr (Or.inl rfl))) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  exact hOffset

theorem bridgedExpr_tload (slotExpr : Compiler.Yul.YulExpr)
    (hSlot : BridgedExpr slotExpr) :
    BridgedExpr
      (Compiler.Yul.YulExpr.call "tload" [slotExpr]) := by
  refine BridgedExpr.call "tload" _ (Or.inr (Or.inl rfl)) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  exact hSlot

theorem bridgedStraightStmt_let_mload (name : String)
    (offsetExpr : Compiler.Yul.YulExpr) (hOffset : BridgedExpr offsetExpr) :
    BridgedStraightStmt
      (.let_ name (Compiler.Yul.YulExpr.call "mload" [offsetExpr])) :=
  BridgedStraightStmt.let_ name _ (bridgedExpr_mload offsetExpr hOffset)

theorem bridgedStraightStmt_let_tload (name : String)
    (slotExpr : Compiler.Yul.YulExpr) (hSlot : BridgedExpr slotExpr) :
    BridgedStraightStmt
      (.let_ name (Compiler.Yul.YulExpr.call "tload" [slotExpr])) :=
  BridgedStraightStmt.let_ name _ (bridgedExpr_tload slotExpr hSlot)

theorem bridgedStraightStmt_let_keccak256 (name : String)
    (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
    BridgedStraightStmt
      (.let_ name
        (Compiler.Yul.YulExpr.call "keccak256" [offsetExpr, sizeExpr])) :=
  BridgedStraightStmt.let_ name _
    (bridgedExpr_keccak256 offsetExpr sizeExpr hOffset hSize)

theorem bridgedStraightStmt_assign_mload (name : String)
    (offsetExpr : Compiler.Yul.YulExpr) (hOffset : BridgedExpr offsetExpr) :
    BridgedStraightStmt
      (.assign name (Compiler.Yul.YulExpr.call "mload" [offsetExpr])) :=
  BridgedStraightStmt.assign name _ (bridgedExpr_mload offsetExpr hOffset)

theorem bridgedStraightStmt_assign_tload (name : String)
    (slotExpr : Compiler.Yul.YulExpr) (hSlot : BridgedExpr slotExpr) :
    BridgedStraightStmt
      (.assign name (Compiler.Yul.YulExpr.call "tload" [slotExpr])) :=
  BridgedStraightStmt.assign name _ (bridgedExpr_tload slotExpr hSlot)

theorem bridgedStraightStmt_assign_keccak256 (name : String)
    (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
    BridgedStraightStmt
      (.assign name
        (Compiler.Yul.YulExpr.call "keccak256" [offsetExpr, sizeExpr])) :=
  BridgedStraightStmt.assign name _
    (bridgedExpr_keccak256 offsetExpr sizeExpr hOffset hSize)

theorem bridgedStraightStmt_log_of_bridged_args
    (func : String) (args : List Compiler.Yul.YulExpr)
    (hLog : isYulLogName func = true)
    (hArgs : ∀ arg ∈ args, BridgedExpr arg) :
    BridgedStraightStmt (.expr (.call func args)) :=
  BridgedStraightStmt.expr_log func args hLog hArgs

theorem bridgedStmt_of_bridgedStraightStmt {stmt : Compiler.Yul.YulStmt}
    (hStmt : BridgedStraightStmt stmt) : BridgedStmt stmt :=
  BridgedStmt.straight stmt hStmt

theorem bridgedStmt_log_of_bridged_args
    (func : String) (args : List Compiler.Yul.YulExpr)
    (hLog : isYulLogName func = true)
    (hArgs : ∀ arg ∈ args, BridgedExpr arg) :
    BridgedStmt (.expr (.call func args)) :=
  bridgedStmt_of_bridgedStraightStmt
    (bridgedStraightStmt_log_of_bridged_args func args hLog hArgs)

theorem bridgedStmt_let_mload (name : String)
    (offsetExpr : Compiler.Yul.YulExpr) (hOffset : BridgedExpr offsetExpr) :
    BridgedStmt (.let_ name (Compiler.Yul.YulExpr.call "mload" [offsetExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (bridgedStraightStmt_let_mload name offsetExpr hOffset)

theorem bridgedStmt_let_tload (name : String)
    (slotExpr : Compiler.Yul.YulExpr) (hSlot : BridgedExpr slotExpr) :
    BridgedStmt (.let_ name (Compiler.Yul.YulExpr.call "tload" [slotExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (bridgedStraightStmt_let_tload name slotExpr hSlot)

theorem bridgedStmt_let_keccak256 (name : String)
    (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
    BridgedStmt
      (.let_ name
        (Compiler.Yul.YulExpr.call "keccak256" [offsetExpr, sizeExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (bridgedStraightStmt_let_keccak256 name offsetExpr sizeExpr hOffset hSize)

theorem bridgedStmt_assign_mload (name : String)
    (offsetExpr : Compiler.Yul.YulExpr) (hOffset : BridgedExpr offsetExpr) :
    BridgedStmt
      (.assign name (Compiler.Yul.YulExpr.call "mload" [offsetExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (bridgedStraightStmt_assign_mload name offsetExpr hOffset)

theorem bridgedStmt_assign_tload (name : String)
    (slotExpr : Compiler.Yul.YulExpr) (hSlot : BridgedExpr slotExpr) :
    BridgedStmt
      (.assign name (Compiler.Yul.YulExpr.call "tload" [slotExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (bridgedStraightStmt_assign_tload name slotExpr hSlot)

theorem bridgedStmt_assign_keccak256 (name : String)
    (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
    BridgedStmt
      (.assign name
        (Compiler.Yul.YulExpr.call "keccak256" [offsetExpr, sizeExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (bridgedStraightStmt_assign_keccak256 name offsetExpr sizeExpr hOffset hSize)

theorem bridgedStmt_mstore_of_bridged_args
    (offsetExpr valExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hVal : BridgedExpr valExpr) :
    BridgedStmt
      (.expr (Compiler.Yul.YulExpr.call "mstore" [offsetExpr, valExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.expr_mstore offsetExpr valExpr hOffset hVal)

theorem bridgedStmt_tstore_of_bridged_args
    (offsetExpr valExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hVal : BridgedExpr valExpr) :
    BridgedStmt
      (.expr (Compiler.Yul.YulExpr.call "tstore" [offsetExpr, valExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.expr_tstore offsetExpr valExpr hOffset hVal)

theorem bridgedStmt_sstore_mapping_of_bridged_args
    (baseExpr keyExpr valExpr : Compiler.Yul.YulExpr)
    (hBase : BridgedExpr baseExpr) (hKey : BridgedExpr keyExpr)
    (hVal : BridgedExpr valExpr) :
    BridgedStmt
      (.expr (Compiler.Yul.YulExpr.call "sstore"
        [Compiler.Yul.YulExpr.call "mappingSlot" [baseExpr, keyExpr], valExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.expr_sstore_mapping baseExpr keyExpr valExpr hBase hKey hVal)

theorem bridgedStmt_sstore_lit_of_bridged_val
    (slot : Nat) (valExpr : Compiler.Yul.YulExpr) (hVal : BridgedExpr valExpr) :
    BridgedStmt
      (.expr (Compiler.Yul.YulExpr.call "sstore" [.lit slot, valExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.expr_sstore_lit slot valExpr hVal)

theorem bridgedStmt_sstore_ident_of_bridged_val
    (slotName : String) (valExpr : Compiler.Yul.YulExpr) (hVal : BridgedExpr valExpr) :
    BridgedStmt
      (.expr (Compiler.Yul.YulExpr.call "sstore" [.ident slotName, valExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.expr_sstore_ident slotName valExpr hVal)

theorem bridgedStmt_sstore_add_of_bridged_args
    (leftExpr rightExpr valExpr : Compiler.Yul.YulExpr)
    (hLeft : BridgedExpr leftExpr) (hRight : BridgedExpr rightExpr)
    (hVal : BridgedExpr valExpr) :
    BridgedStmt
      (.expr (Compiler.Yul.YulExpr.call "sstore"
        [Compiler.Yul.YulExpr.call "add" [leftExpr, rightExpr], valExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.expr_sstore_add leftExpr rightExpr valExpr hLeft hRight hVal)

theorem bridgedStmt_stop :
    BridgedStmt (Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "stop" [])) :=
  bridgedStmt_of_bridgedStraightStmt BridgedStraightStmt.expr_stop

theorem bridgedStmt_return_of_bridged_args
    (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
    BridgedStmt
      (.expr (Compiler.Yul.YulExpr.call "return" [offsetExpr, sizeExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.expr_return offsetExpr sizeExpr hOffset hSize)

theorem bridgedStmt_revert (offsetExpr sizeExpr : Compiler.Yul.YulExpr) :
    BridgedStmt
      (.expr (Compiler.Yul.YulExpr.call "revert" [offsetExpr, sizeExpr])) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.expr_revert offsetExpr sizeExpr)

theorem bridgedStmt_leave : BridgedStmt .leave :=
  bridgedStmt_of_bridgedStraightStmt BridgedStraightStmt.leave

theorem bridgedStmt_let_of_bridged_val
    (name : String) (value : Compiler.Yul.YulExpr) (hValue : BridgedExpr value) :
    BridgedStmt (.let_ name value) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.let_ name value hValue)

theorem bridgedStmt_letMany (names : List String) (value : Compiler.Yul.YulExpr) :
    BridgedStmt (.letMany names value) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.letMany names value)

theorem bridgedStmt_assign_of_bridged_val
    (name : String) (value : Compiler.Yul.YulExpr) (hValue : BridgedExpr value) :
    BridgedStmt (.assign name value) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.assign name value hValue)

theorem bridgedStmt_comment (text : String) :
    BridgedStmt (.comment text) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.comment text)

theorem bridgedStmt_funcDef
    (name : String) (params rets : List String)
    (body : List Compiler.Yul.YulStmt) :
    BridgedStmt (.funcDef name params rets body) :=
  bridgedStmt_of_bridgedStraightStmt
    (BridgedStraightStmt.funcDef name params rets body)

theorem BridgedStmts_of_BridgedStraightStmts
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStraightStmts stmts) :
    BridgedStmts stmts := by
  intro stmt hMem
  exact bridgedStmt_of_bridgedStraightStmt (hStmts stmt hMem)

theorem BridgedStmts_cons_straight {stmt : Compiler.Yul.YulStmt}
    {stmts : List Compiler.Yul.YulStmt}
    (hStmt : BridgedStraightStmt stmt) (hStmts : BridgedStmts stmts) :
    BridgedStmts (stmt :: stmts) :=
  BridgedStmts_cons (bridgedStmt_of_bridgedStraightStmt hStmt) hStmts

theorem BridgedStmts_singleton_straight {stmt : Compiler.Yul.YulStmt}
    (hStmt : BridgedStraightStmt stmt) :
    BridgedStmts [stmt] :=
  BridgedStmts_singleton (bridgedStmt_of_bridgedStraightStmt hStmt)

theorem BridgedStmts_append_straight {xs ys : List Compiler.Yul.YulStmt}
    (hXs : BridgedStraightStmts xs) (hYs : BridgedStmts ys) :
    BridgedStmts (xs ++ ys) :=
  BridgedStmts_append (BridgedStmts_of_BridgedStraightStmts hXs) hYs

theorem BridgedStmts_map_mstore
    (pairs : List (Compiler.Yul.YulExpr × Compiler.Yul.YulExpr))
    (hPairs : ∀ p ∈ pairs, BridgedExpr p.1 ∧ BridgedExpr p.2) :
    BridgedStmts
      (pairs.map fun p =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "mstore" [p.1, p.2])) :=
  BridgedStmts_of_BridgedStraightStmts
    (BridgedStraightStmts_map_mstore pairs hPairs)

theorem bridgedStmt_block_of_bridgedStmts
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmt (.block stmts) :=
  BridgedStmt.block stmts hStmts

theorem BridgedStmts_singleton_block
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts [.block stmts] :=
  BridgedStmts_singleton (bridgedStmt_block_of_bridgedStmts hStmts)

theorem BridgedStmts_cons_block
    {blockStmts stmts : List Compiler.Yul.YulStmt}
    (hBlock : BridgedStmts blockStmts) (hStmts : BridgedStmts stmts) :
    BridgedStmts (.block blockStmts :: stmts) :=
  BridgedStmts_cons (bridgedStmt_block_of_bridgedStmts hBlock) hStmts

theorem bridgedStmt_if_of_bridgedStmts
    {cond : Compiler.Yul.YulExpr} {body : List Compiler.Yul.YulStmt}
    (hCond : BridgedExpr cond) (hBody : BridgedStmts body) :
    BridgedStmt (.if_ cond body) :=
  BridgedStmt.if_ cond body hCond hBody

theorem BridgedStmts_singleton_if
    {cond : Compiler.Yul.YulExpr} {body : List Compiler.Yul.YulStmt}
    (hCond : BridgedExpr cond) (hBody : BridgedStmts body) :
    BridgedStmts [.if_ cond body] :=
  BridgedStmts_singleton (bridgedStmt_if_of_bridgedStmts hCond hBody)

theorem BridgedStmts_cons_if
    {cond : Compiler.Yul.YulExpr} {body stmts : List Compiler.Yul.YulStmt}
    (hCond : BridgedExpr cond) (hBody : BridgedStmts body)
    (hStmts : BridgedStmts stmts) :
    BridgedStmts (.if_ cond body :: stmts) :=
  BridgedStmts_cons (bridgedStmt_if_of_bridgedStmts hCond hBody) hStmts

theorem bridgedStmt_for_of_bridgedStmts
    {init : List Compiler.Yul.YulStmt} {cond : Compiler.Yul.YulExpr}
    {post body : List Compiler.Yul.YulStmt}
    (hInit : BridgedStmts init) (hCond : BridgedExpr cond)
    (hPost : BridgedStmts post) (hBody : BridgedStmts body) :
    BridgedStmt (.for_ init cond post body) :=
  BridgedStmt.for_ init cond post body hInit hCond hPost hBody

theorem BridgedStmts_singleton_for
    {init : List Compiler.Yul.YulStmt} {cond : Compiler.Yul.YulExpr}
    {post body : List Compiler.Yul.YulStmt}
    (hInit : BridgedStmts init) (hCond : BridgedExpr cond)
    (hPost : BridgedStmts post) (hBody : BridgedStmts body) :
    BridgedStmts [.for_ init cond post body] :=
  BridgedStmts_singleton
    (bridgedStmt_for_of_bridgedStmts hInit hCond hPost hBody)

theorem BridgedStmts_cons_for
    {init : List Compiler.Yul.YulStmt} {cond : Compiler.Yul.YulExpr}
    {post body stmts : List Compiler.Yul.YulStmt}
    (hInit : BridgedStmts init) (hCond : BridgedExpr cond)
    (hPost : BridgedStmts post) (hBody : BridgedStmts body)
    (hStmts : BridgedStmts stmts) :
    BridgedStmts (.for_ init cond post body :: stmts) :=
  BridgedStmts_cons
    (bridgedStmt_for_of_bridgedStmts hInit hCond hPost hBody) hStmts

theorem bridgedStmt_switch_of_bridgedStmts
    {expr : Compiler.Yul.YulExpr}
    {cases : List (Nat × List Compiler.Yul.YulStmt)}
    {defaultCase : Option (List Compiler.Yul.YulStmt)}
    (hExpr : BridgedExpr expr)
    (hCases : ∀ scrutinee value body,
      cases.find? (fun x => decide (x.fst = scrutinee)) = some (value, body) →
      BridgedStmts body)
    (hDefault : ∀ body, defaultCase = some body → BridgedStmts body) :
    BridgedStmt (.switch expr cases defaultCase) :=
  BridgedStmt.switch expr cases defaultCase hExpr hCases hDefault

theorem BridgedStmts_singleton_switch
    {expr : Compiler.Yul.YulExpr}
    {cases : List (Nat × List Compiler.Yul.YulStmt)}
    {defaultCase : Option (List Compiler.Yul.YulStmt)}
    (hExpr : BridgedExpr expr)
    (hCases : ∀ scrutinee value body,
      cases.find? (fun x => decide (x.fst = scrutinee)) = some (value, body) →
      BridgedStmts body)
    (hDefault : ∀ body, defaultCase = some body → BridgedStmts body) :
    BridgedStmts [.switch expr cases defaultCase] :=
  BridgedStmts_singleton
    (bridgedStmt_switch_of_bridgedStmts hExpr hCases hDefault)

theorem BridgedStmts_cons_switch
    {expr : Compiler.Yul.YulExpr}
    {cases : List (Nat × List Compiler.Yul.YulStmt)}
    {defaultCase : Option (List Compiler.Yul.YulStmt)}
    {stmts : List Compiler.Yul.YulStmt}
    (hExpr : BridgedExpr expr)
    (hCases : ∀ scrutinee value body,
      cases.find? (fun x => decide (x.fst = scrutinee)) = some (value, body) →
      BridgedStmts body)
    (hDefault : ∀ body, defaultCase = some body → BridgedStmts body)
    (hStmts : BridgedStmts stmts) :
    BridgedStmts (.switch expr cases defaultCase :: stmts) :=
  BridgedStmts_cons
    (bridgedStmt_switch_of_bridgedStmts hExpr hCases hDefault) hStmts

theorem bridgedStmt_block_of_bridgedStraightStmts
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStraightStmts stmts) :
    BridgedStmt (.block stmts) :=
  bridgedStmt_block_of_bridgedStmts
    (BridgedStmts_of_BridgedStraightStmts hStmts)

theorem bridgedStmt_if_of_bridgedStraightStmts
    {cond : Compiler.Yul.YulExpr} {body : List Compiler.Yul.YulStmt}
    (hCond : BridgedExpr cond) (hBody : BridgedStraightStmts body) :
    BridgedStmt (.if_ cond body) :=
  bridgedStmt_if_of_bridgedStmts hCond
    (BridgedStmts_of_BridgedStraightStmts hBody)

theorem bridgedStmt_for_of_bridgedStraightStmts
    {init : List Compiler.Yul.YulStmt} {cond : Compiler.Yul.YulExpr}
    {post body : List Compiler.Yul.YulStmt}
    (hInit : BridgedStraightStmts init) (hCond : BridgedExpr cond)
    (hPost : BridgedStraightStmts post) (hBody : BridgedStraightStmts body) :
    BridgedStmt (.for_ init cond post body) :=
  bridgedStmt_for_of_bridgedStmts
    (BridgedStmts_of_BridgedStraightStmts hInit) hCond
    (BridgedStmts_of_BridgedStraightStmts hPost)
    (BridgedStmts_of_BridgedStraightStmts hBody)

theorem BridgedStmts_map_tstore
    (pairs : List (Compiler.Yul.YulExpr × Compiler.Yul.YulExpr))
    (hPairs : ∀ p ∈ pairs, BridgedExpr p.1 ∧ BridgedExpr p.2) :
    BridgedStmts
      (pairs.map fun p =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "tstore" [p.1, p.2])) :=
  BridgedStmts_of_BridgedStraightStmts
    (BridgedStraightStmts_map_tstore pairs hPairs)

theorem bridgedStmt_revert_zero :
    BridgedStmt
      (Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "revert"
          [Compiler.Yul.YulExpr.lit 0, Compiler.Yul.YulExpr.lit 0])) :=
  bridgedStmt_revert (Compiler.Yul.YulExpr.lit 0) (Compiler.Yul.YulExpr.lit 0)

theorem BridgedStmts_singleton_revert_zero :
    BridgedStmts
      [Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "revert"
          [Compiler.Yul.YulExpr.lit 0, Compiler.Yul.YulExpr.lit 0])] :=
  BridgedStmts_singleton bridgedStmt_revert_zero

theorem BridgedStmts_singleton_comment (text : String) :
    BridgedStmts [.comment text] :=
  BridgedStmts_singleton (bridgedStmt_comment text)

theorem BridgedStmts_cons_comment
    (text : String) {stmts : List Compiler.Yul.YulStmt}
    (hStmts : BridgedStmts stmts) :
    BridgedStmts (.comment text :: stmts) :=
  BridgedStmts_cons (bridgedStmt_comment text) hStmts

theorem BridgedStmts_singleton_let
    (name : String) (value : Compiler.Yul.YulExpr) (hValue : BridgedExpr value) :
    BridgedStmts [.let_ name value] :=
  BridgedStmts_singleton (bridgedStmt_let_of_bridged_val name value hValue)

theorem BridgedStmts_cons_let
    (name : String) (value : Compiler.Yul.YulExpr) (hValue : BridgedExpr value)
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts (.let_ name value :: stmts) :=
  BridgedStmts_cons (bridgedStmt_let_of_bridged_val name value hValue) hStmts

theorem BridgedStmts_singleton_assign
    (name : String) (value : Compiler.Yul.YulExpr) (hValue : BridgedExpr value) :
    BridgedStmts [.assign name value] :=
  BridgedStmts_singleton (bridgedStmt_assign_of_bridged_val name value hValue)

theorem BridgedStmts_cons_assign
    (name : String) (value : Compiler.Yul.YulExpr) (hValue : BridgedExpr value)
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts (.assign name value :: stmts) :=
  BridgedStmts_cons (bridgedStmt_assign_of_bridged_val name value hValue) hStmts

theorem BridgedStmts_singleton_letMany
    (names : List String) (value : Compiler.Yul.YulExpr) :
    BridgedStmts [.letMany names value] :=
  BridgedStmts_singleton (bridgedStmt_letMany names value)

theorem BridgedStmts_cons_letMany
    (names : List String) (value : Compiler.Yul.YulExpr)
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts (.letMany names value :: stmts) :=
  BridgedStmts_cons (bridgedStmt_letMany names value) hStmts

theorem BridgedStmts_singleton_stop :
    BridgedStmts
      [Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "stop" [])] :=
  BridgedStmts_singleton bridgedStmt_stop

theorem BridgedStmts_cons_stop {stmts : List Compiler.Yul.YulStmt}
    (hStmts : BridgedStmts stmts) :
    BridgedStmts
      (Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "stop" []) :: stmts) :=
  BridgedStmts_cons bridgedStmt_stop hStmts

theorem BridgedStmts_singleton_leave :
    BridgedStmts [Compiler.Yul.YulStmt.leave] :=
  BridgedStmts_singleton bridgedStmt_leave

theorem BridgedStmts_cons_leave {stmts : List Compiler.Yul.YulStmt}
    (hStmts : BridgedStmts stmts) :
    BridgedStmts (Compiler.Yul.YulStmt.leave :: stmts) :=
  BridgedStmts_cons bridgedStmt_leave hStmts

theorem BridgedStmts_singleton_return
    (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr) :
    BridgedStmts [.expr (.call "return" [offsetExpr, sizeExpr])] :=
  BridgedStmts_singleton
    (bridgedStmt_return_of_bridged_args offsetExpr sizeExpr hOffset hSize)

theorem BridgedStmts_cons_return
    (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hSize : BridgedExpr sizeExpr)
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts (.expr (.call "return" [offsetExpr, sizeExpr]) :: stmts) :=
  BridgedStmts_cons
    (bridgedStmt_return_of_bridged_args offsetExpr sizeExpr hOffset hSize) hStmts

theorem BridgedStmts_singleton_revert
    (offsetExpr sizeExpr : Compiler.Yul.YulExpr) :
    BridgedStmts [.expr (.call "revert" [offsetExpr, sizeExpr])] :=
  BridgedStmts_singleton (bridgedStmt_revert offsetExpr sizeExpr)

theorem BridgedStmts_cons_revert
    (offsetExpr sizeExpr : Compiler.Yul.YulExpr)
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts (.expr (.call "revert" [offsetExpr, sizeExpr]) :: stmts) :=
  BridgedStmts_cons (bridgedStmt_revert offsetExpr sizeExpr) hStmts

theorem BridgedStmts_singleton_mstore
    (offsetExpr valExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hVal : BridgedExpr valExpr) :
    BridgedStmts [.expr (.call "mstore" [offsetExpr, valExpr])] :=
  BridgedStmts_singleton
    (bridgedStmt_mstore_of_bridged_args offsetExpr valExpr hOffset hVal)

theorem BridgedStmts_cons_mstore
    (offsetExpr valExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hVal : BridgedExpr valExpr)
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts (.expr (.call "mstore" [offsetExpr, valExpr]) :: stmts) :=
  BridgedStmts_cons
    (bridgedStmt_mstore_of_bridged_args offsetExpr valExpr hOffset hVal) hStmts

theorem BridgedStmts_singleton_tstore
    (offsetExpr valExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hVal : BridgedExpr valExpr) :
    BridgedStmts [.expr (.call "tstore" [offsetExpr, valExpr])] :=
  BridgedStmts_singleton
    (bridgedStmt_tstore_of_bridged_args offsetExpr valExpr hOffset hVal)

theorem BridgedStmts_cons_tstore
    (offsetExpr valExpr : Compiler.Yul.YulExpr)
    (hOffset : BridgedExpr offsetExpr) (hVal : BridgedExpr valExpr)
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts (.expr (.call "tstore" [offsetExpr, valExpr]) :: stmts) :=
  BridgedStmts_cons
    (bridgedStmt_tstore_of_bridged_args offsetExpr valExpr hOffset hVal) hStmts

theorem BridgedStmts_singleton_sstore_lit
    (slot : Nat) (valExpr : Compiler.Yul.YulExpr) (hVal : BridgedExpr valExpr) :
    BridgedStmts [.expr (.call "sstore" [.lit slot, valExpr])] :=
  BridgedStmts_singleton
    (bridgedStmt_sstore_lit_of_bridged_val slot valExpr hVal)

theorem BridgedStmts_cons_sstore_lit
    (slot : Nat) (valExpr : Compiler.Yul.YulExpr) (hVal : BridgedExpr valExpr)
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts (.expr (.call "sstore" [.lit slot, valExpr]) :: stmts) :=
  BridgedStmts_cons
    (bridgedStmt_sstore_lit_of_bridged_val slot valExpr hVal) hStmts

theorem BridgedStmts_singleton_sstore_ident
    (slotName : String) (valExpr : Compiler.Yul.YulExpr) (hVal : BridgedExpr valExpr) :
    BridgedStmts [.expr (.call "sstore" [.ident slotName, valExpr])] :=
  BridgedStmts_singleton
    (bridgedStmt_sstore_ident_of_bridged_val slotName valExpr hVal)

theorem BridgedStmts_cons_sstore_ident
    (slotName : String) (valExpr : Compiler.Yul.YulExpr) (hVal : BridgedExpr valExpr)
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts (.expr (.call "sstore" [.ident slotName, valExpr]) :: stmts) :=
  BridgedStmts_cons
    (bridgedStmt_sstore_ident_of_bridged_val slotName valExpr hVal) hStmts

theorem BridgedStmts_singleton_sstore_mapping
    (baseExpr keyExpr valExpr : Compiler.Yul.YulExpr)
    (hBase : BridgedExpr baseExpr) (hKey : BridgedExpr keyExpr)
    (hVal : BridgedExpr valExpr) :
    BridgedStmts
      [.expr (.call "sstore" [.call "mappingSlot" [baseExpr, keyExpr], valExpr])] :=
  BridgedStmts_singleton
    (bridgedStmt_sstore_mapping_of_bridged_args
      baseExpr keyExpr valExpr hBase hKey hVal)

theorem BridgedStmts_cons_sstore_mapping
    (baseExpr keyExpr valExpr : Compiler.Yul.YulExpr)
    (hBase : BridgedExpr baseExpr) (hKey : BridgedExpr keyExpr)
    (hVal : BridgedExpr valExpr)
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts
      (.expr (.call "sstore" [.call "mappingSlot" [baseExpr, keyExpr], valExpr])
        :: stmts) :=
  BridgedStmts_cons
    (bridgedStmt_sstore_mapping_of_bridged_args
      baseExpr keyExpr valExpr hBase hKey hVal) hStmts

theorem BridgedStmts_singleton_log
    (func : String) (args : List Compiler.Yul.YulExpr)
    (hLog : isYulLogName func = true)
    (hArgs : ∀ arg ∈ args, BridgedExpr arg) :
    BridgedStmts [.expr (.call func args)] :=
  BridgedStmts_singleton
    (bridgedStmt_log_of_bridged_args func args hLog hArgs)

theorem BridgedStmts_cons_log
    (func : String) (args : List Compiler.Yul.YulExpr)
    (hLog : isYulLogName func = true)
    (hArgs : ∀ arg ∈ args, BridgedExpr arg)
    {stmts : List Compiler.Yul.YulStmt} (hStmts : BridgedStmts stmts) :
    BridgedStmts (.expr (.call func args) :: stmts) :=
  BridgedStmts_cons
    (bridgedStmt_log_of_bridged_args func args hLog hArgs) hStmts

theorem BridgedStmts_singleton_funcDef
    (name : String) (params rets : List String)
    (body : List Compiler.Yul.YulStmt) :
    BridgedStmts [.funcDef name params rets body] :=
  BridgedStmts_singleton (bridgedStmt_funcDef name params rets body)

theorem BridgedStmts_cons_funcDef
    (name : String) (params rets : List String)
    (body stmts : List Compiler.Yul.YulStmt) (hStmts : BridgedStmts stmts) :
    BridgedStmts (.funcDef name params rets body :: stmts) :=
  BridgedStmts_cons (bridgedStmt_funcDef name params rets body) hStmts

end Compiler.Proofs.YulGeneration.Backends
