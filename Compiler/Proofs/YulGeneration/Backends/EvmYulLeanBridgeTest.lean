/-
  EvmYulLeanBridgeTest: Compile-time equivalence checks for the EVMYulLean
  builtin bridge.

  Validates that `evalPureBuiltinViaEvmYulLean` (which delegates to
  EVMYulLean's UInt256 operations) agrees with Verity's `evalBuiltinCall`
  on concrete test vectors for all pure arithmetic/comparison/bitwise builtins.

  This is a smoke test, not a general equivalence proof. Full semantic
  equivalence would require proving the relationship between Verity's
  Nat-modular arithmetic and EVMYulLean's Fin-based UInt256 for all inputs.

  Run: lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeTest
-/

import Compiler.Proofs.YulGeneration.Builtins
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter

namespace Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeTest

open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends

-- Shared test parameters (state-independent for pure builtins)
private def testStorage : Nat → Nat := fun _ => 0
private def testSender : Nat := 42
private def testSelector : Nat := 0
private def testCalldata : List Nat := []

/-- Helper: evaluate a builtin via the Verity path. -/
private def verityEval (func : String) (args : List Nat) : Option Nat :=
  evalBuiltinCall testStorage testSender testSelector testCalldata func args

/-- Helper: evaluate a builtin via the EVMYulLean bridge path. -/
private def bridgeEval (func : String) (args : List Nat) : Option Nat :=
  evalPureBuiltinViaEvmYulLean func args

-- ## Arithmetic builtins

/-- add: 3 + 5 = 8 -/
example : verityEval "add" [3, 5] = bridgeEval "add" [3, 5] := by native_decide

/-- add: wrapping at 2^256 boundary -/
example : verityEval "add" [Compiler.Constants.evmModulus - 1, 1] =
          bridgeEval "add" [Compiler.Constants.evmModulus - 1, 1] := by native_decide

/-- sub: 10 - 3 = 7 -/
example : verityEval "sub" [10, 3] = bridgeEval "sub" [10, 3] := by native_decide

/-- sub: underflow wraps -/
example : verityEval "sub" [0, 1] = bridgeEval "sub" [0, 1] := by native_decide

/-- mul: 6 * 7 = 42 -/
example : verityEval "mul" [6, 7] = bridgeEval "mul" [6, 7] := by native_decide

/-- div: 42 / 7 = 6 -/
example : verityEval "div" [42, 7] = bridgeEval "div" [42, 7] := by native_decide

/-- div: division by zero returns 0 -/
example : verityEval "div" [42, 0] = bridgeEval "div" [42, 0] := by native_decide

/-- mod: 10 % 3 = 1 -/
example : verityEval "mod" [10, 3] = bridgeEval "mod" [10, 3] := by native_decide

/-- mod: modulo by zero returns 0 -/
example : verityEval "mod" [10, 0] = bridgeEval "mod" [10, 0] := by native_decide

-- ## Comparison builtins

/-- lt: 3 < 5 = 1 -/
example : verityEval "lt" [3, 5] = bridgeEval "lt" [3, 5] := by native_decide

/-- lt: 5 < 3 = 0 -/
example : verityEval "lt" [5, 3] = bridgeEval "lt" [5, 3] := by native_decide

/-- lt: 3 < 3 = 0 -/
example : verityEval "lt" [3, 3] = bridgeEval "lt" [3, 3] := by native_decide

/-- gt: 5 > 3 = 1 -/
example : verityEval "gt" [5, 3] = bridgeEval "gt" [5, 3] := by native_decide

/-- gt: 3 > 5 = 0 -/
example : verityEval "gt" [3, 5] = bridgeEval "gt" [3, 5] := by native_decide

/-- eq: 42 = 42 -/
example : verityEval "eq" [42, 42] = bridgeEval "eq" [42, 42] := by native_decide

/-- eq: 42 ≠ 43 -/
example : verityEval "eq" [42, 43] = bridgeEval "eq" [42, 43] := by native_decide

/-- eq: 2^256 ≡ 0 (word-size wraparound). -/
example : verityEval "eq" [Compiler.Constants.evmModulus, 0] =
          bridgeEval "eq" [Compiler.Constants.evmModulus, 0] := by native_decide

/-- iszero: 0 is zero -/
example : verityEval "iszero" [0] = bridgeEval "iszero" [0] := by native_decide

/-- iszero: 1 is not zero -/
example : verityEval "iszero" [1] = bridgeEval "iszero" [1] := by native_decide

/-- iszero: 2^256 ≡ 0 (word-size wraparound). -/
example : verityEval "iszero" [Compiler.Constants.evmModulus] =
          bridgeEval "iszero" [Compiler.Constants.evmModulus] := by native_decide

/-- lt: 2^256 wraps to 0, so 0 < 1. -/
example : verityEval "lt" [Compiler.Constants.evmModulus, 1] =
          bridgeEval "lt" [Compiler.Constants.evmModulus, 1] := by native_decide

/-- gt: 2^256 wraps to 0, so 0 > 2^256-1 is false. -/
example : verityEval "gt" [Compiler.Constants.evmModulus, Compiler.Constants.evmModulus - 1] =
          bridgeEval "gt" [Compiler.Constants.evmModulus, Compiler.Constants.evmModulus - 1] := by native_decide

-- ## Bitwise builtins

/-- and: 0xFF & 0x0F = 0x0F -/
example : verityEval "and" [255, 15] = bridgeEval "and" [255, 15] := by native_decide

/-- or: 0xF0 | 0x0F = 0xFF -/
example : verityEval "or" [240, 15] = bridgeEval "or" [240, 15] := by native_decide

/-- xor: 0xFF ^ 0x0F = 0xF0 -/
example : verityEval "xor" [255, 15] = bridgeEval "xor" [255, 15] := by native_decide

/-- not: bitwise NOT of 0 -/
example : verityEval "not" [0] = bridgeEval "not" [0] := by native_decide

/-- shl: 1 << 8 = 256 -/
example : verityEval "shl" [8, 1] = bridgeEval "shl" [8, 1] := by native_decide

/-- shr: 256 >> 8 = 1 -/
example : verityEval "shr" [8, 256] = bridgeEval "shr" [8, 256] := by native_decide

-- ## Scope boundary: state-dependent builtins fall through to none

/-- sload: bridge returns none (state-dependent, delegated to Verity) -/
example : bridgeEval "sload" [0] = none := by native_decide

/-- caller: bridge returns none (state-dependent) -/
example : bridgeEval "caller" [] = none := by native_decide

/-- calldataload: bridge returns none (state-dependent) -/
example : bridgeEval "calldataload" [0] = none := by native_decide

/-- mappingSlot: bridge returns none (Verity-specific helper) -/
example : bridgeEval "mappingSlot" [0, 1] = none := by native_decide

-- ## Adapter coverage: all statement types lower without error

open Compiler.Yul in
private def adapterSmokeStmts : List YulStmt := [
  .comment "test",
  .let_ "x" (.lit 42),
  .letMany ["a", "b"] (.call "foo" [.lit 1]),
  .assign "x" (.lit 99),
  .expr (.call "sstore" [.lit 0, .ident "x"]),
  .leave,
  .if_ (.ident "x") [.expr (.call "nop" [])],
  .for_ [.let_ "i" (.lit 0)] (.call "lt" [.ident "i", .lit 10])
         [.assign "i" (.call "add" [.ident "i", .lit 1])]
         [.expr (.call "nop" [])],
  .switch (.ident "x") [(0, [.leave]), (1, [.leave])] (some [.leave]),
  .block [.let_ "y" (.lit 0)],
  .funcDef "myFunc" ["a"] ["b"] [.let_ "b" (.ident "a")]
]

/-- All 11 statement types lower successfully via the adapter. -/
example : (lowerStmts adapterSmokeStmts).isOk = true := by native_decide

-- ## Summary output
def main : IO Unit := do
  IO.println "✓ Arithmetic builtins: add, sub, mul, div, mod — Verity ≡ EVMYulLean"
  IO.println "✓ Comparison builtins: lt, gt, eq, iszero — Verity ≡ EVMYulLean"
  IO.println "✓ Bitwise builtins: and, or, xor, not, shl, shr — Verity ≡ EVMYulLean"
  IO.println "✓ State-dependent builtins: sload, caller, calldataload — correctly delegated"
  IO.println "✓ Verity-specific helpers: mappingSlot — correctly delegated"
  IO.println "✓ Adapter: all 11 statement types lower without error"
  IO.println "EVMYulLean bridge test: all checks passed"

end Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeTest
