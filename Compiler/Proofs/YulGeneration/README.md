# Layer 3: Yul Code Generation Proofs

This directory contains the verification proofs for Layer 3 (IR → Yul) of the Verity compiler pipeline.

**Status**: native EVMYulLean dispatcher execution is the public Layer 3
target. The active end-to-end native surface is the
`EvmYul.Yul.callDispatcher` theorem stack in `Compiler/Proofs/EndToEnd.lean`.
The old fuel-parametric Verity-side Yul executor, preservation stack, and private
retarget bridge have been removed. Native EVMYulLean dispatch is the only
checked-in builtin semantics surface.

## File Overview

- **`Backends/EvmYulLeanNativeHarness.lean`** - Native EVMYulLean execution
  harness
  - Lowers emitted runtime code to executable EVMYulLean contracts
  - Provides the native `callDispatcher` result surface used by the active
    end-to-end theorem stack

- **`Backends/EvmYulLeanNativeLowering.lean`** - Native runtime lowering
  - Maps supported emitted Yul builtins to EVMYulLean primops
  - Lowers generated runtime statements and function definitions into native
    EVMYulLean contracts

- **`Backends/EvmYulLeanBodyClosure.lean`** - Native safe-body closure layer
  - Packages supported source fragments into `BridgedSafeStmts`
  - Proves emitted Yul fragments satisfy native bridge predicates

- **`Backends/EvmYulLeanBridgeLemmas.lean`** - Builtin agreement layer
  - Records native EVMYulLean builtin-routing facts used by bridge predicates
  - Covers the pure, environment, calldata, storage, and helper builtin cases

- **`Backends/EvmYulLeanBridgePredicates.lean`** - Native bridge predicates
  for source expressions, statements, and generated bodies

- **`Backends/EvmYulLeanCallClosure.lean`** - Function-table-aware closure
  scaffolding for external-call families that are not yet admitted into the
  public safe-body EndToEnd wrapper

- **`PatchRulesProofs.lean`** - Proof hooks for deterministic Yul patch rules
  - Defines `ExprPatchPreservesUnder` backend-agnostic proof contract for patch correctness
  - Registers evaluator-law proof obligations for the foundation patch pack (`or(x,0)`, `or(0,x)`, `xor(x,0)`, `xor(0,x)`, `and(x,0)`)

## Native Boundary

The public compiler-correctness path does not compose through a Verity-side Yul
interpreter. It lowers generated runtime Yul into EVMYulLean and compares the
projected native dispatcher result with IR/source semantics. Legacy builtin
comparison semantics have been removed; bridge predicates now discharge against
native EVMYulLean routing facts.

## References

- **Proof Inventory**: `Compiler/Proofs/README.md`
- **IR Semantics**: `Compiler/Proofs/IRGeneration/IRInterpreter.lean`
- **Verification Status**: `docs/VERIFICATION_STATUS.md`
