/-
  Compiler.ECM: External Call Module Framework

  External Call Modules (ECMs) package reusable external call patterns
  (ERC-20 transfers, precompile calls, callbacks, etc.) as typed, auditable
  Lean structures that the compiler can plug in without modification.

  Standard modules ship in `Compiler/Modules/`. Third parties can publish
  their own as separate Lean packages.

  See: #964
-/

import Compiler.Constants
import Compiler.ProofStatus
import Compiler.Yul.Ast

namespace Compiler.ECM

open Compiler.Yul
open Compiler.Constants (errorStringSelectorWord addressMask)

/-- Context provided to ECM compile functions beyond the argument expressions.
    This gives modules access to compiler services without coupling them to
    the full CompilationModel compilation pipeline. -/
structure CompilationContext where
  /-- Whether dynamic data comes from calldata (external functions) or memory (internal). -/
  isDynamicFromCalldata : Bool := true

/-- An External Call Module packages a reusable external call pattern.
    Module authors provide the compilation logic; the compiler provides
    the generic framework for validation, compilation, and verification. -/
structure ExternalCallModule where
  /-- Human-readable name, used in error messages and audit reports. -/
  name : String

  /-- Number of Expr arguments this module expects.
      The compiler validates argument count before calling `compile`. -/
  numArgs : Nat

  /-- Local variables this module binds (e.g., ecrecover binds a result address).
      Empty for fire-and-forget patterns like safeTransfer. -/
  resultVars : List String := []

  /-- Does this pattern write to storage or make state-changing calls?
      If true, it cannot appear in view or pure functions. -/
  writesState : Bool

  /-- Does this pattern read storage or environment variables?
      If true, it cannot appear in pure functions. -/
  readsState : Bool

  /-- Compilation function. Takes a compilation context and compiled argument
      expressions (YulExpr) and produces the Yul statement sequence implementing
      this pattern. Returns Except so modules can report argument errors. -/
  compile : CompilationContext → List YulExpr → Except String (List YulStmt)

  /-- Trust assumptions. Surfaced in compilation reports and aggregated
      across all modules used by a contract. -/
  axioms : List String := []

  /-- Proof-accounting status for this module's behavior. -/
  proofStatus : Compiler.ProofStatus := .assumed

instance : BEq ExternalCallModule where
  beq a b := a.name == b.name && a.numArgs == b.numArgs &&
    a.resultVars == b.resultVars && a.writesState == b.writesState &&
    a.readsState == b.readsState && a.axioms == b.axioms &&
    a.proofStatus == b.proofStatus

instance : Repr ExternalCallModule where
  reprPrec m _ := s!"ECM[{m.name}]"

instance : ToString ExternalCallModule where
  toString m := s!"ECM[{m.name}]"

/-! ### Shared Compilation Utilities

These helpers are used by standard modules and available to third-party modules.
They mirror the helpers in CompilationModel but are decoupled from the full compilation
pipeline so that module files only need to import `Compiler.ECM`. -/

private def bytesFromString (s : String) : List UInt8 :=
  s.toUTF8.data.toList

private def chunkBytes32 (bs : List UInt8) : List (List UInt8) :=
  if bs.isEmpty then
    []
  else
    let chunk := bs.take 32
    chunk :: chunkBytes32 (bs.drop 32)
termination_by bs.length
decreasing_by
  simp_wf
  cases bs with
  | nil => simp at *
  | cons head tail => simp; omega

private def wordFromBytes (bs : List UInt8) : Nat :=
  let padded := bs ++ List.replicate (32 - bs.length) (0 : UInt8)
  padded.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Generate Yul statements that revert with an Error(string) message.
    This is the standard Solidity revert encoding: selector + offset + length + data. -/
def revertWithMessage (message : String) : List YulStmt :=
  let bytes := bytesFromString message
  let len := bytes.length
  let paddedLen := ((len + 31) / 32) * 32
  let header := [
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit len])
  ]
  let dataStmts :=
    (chunkBytes32 bytes).zipIdx.map fun (chunk, idx) =>
      let offset := 68 + idx * 32
      let word := wordFromBytes chunk
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word])
  let totalSize := 68 + paddedLen
  header ++ dataStmts ++ [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit totalSize])]

/-- Copy dynamic data (calldata or memory) to a destination offset.
    Uses calldatacopy or a memory loop depending on `isDynamicFromCalldata`. -/
def dynamicCopyData (ctx : CompilationContext)
    (destOffset sourceOffset len : YulExpr) : List YulStmt :=
  if ctx.isDynamicFromCalldata then
    [YulStmt.expr (YulExpr.call "calldatacopy" [destOffset, sourceOffset, len])]
  else
    [YulStmt.for_
      [YulStmt.let_ "__copy_i" (YulExpr.lit 0)]
      (YulExpr.call "lt" [YulExpr.ident "__copy_i", len])
      [YulStmt.assign "__copy_i" (YulExpr.call "add" [YulExpr.ident "__copy_i", YulExpr.lit 32])]
      [YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.call "add" [destOffset, YulExpr.ident "__copy_i"],
        YulExpr.call "mload" [YulExpr.call "add" [sourceOffset, YulExpr.ident "__copy_i"]]
      ])]]

end Compiler.ECM
