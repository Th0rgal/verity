# Layer 3: Yul Code Generation Proofs

This directory contains the verification proofs for Layer 3 (IR → Yul) of the Verity compiler pipeline.

**Status**: native EVMYulLean dispatcher execution is the public Layer 3
target. The active end-to-end native surface is the
`EvmYul.Yul.callDispatcher` theorem stack in `Compiler/Proofs/EndToEnd.lean`.
The old fuel-parametric custom Yul executor, preservation stack, and
`EvmYulLeanRetarget.lean` bridge have been removed. The remaining
`ReferenceOracle` files are builtin comparison helpers used below the public
trust boundary, not an alternate compiler-correctness target.

## File Overview

- **`ReferenceOracle/Builtins.lean`** - Legacy builtin comparison oracle
  - Defines the Verity-side builtin evaluator used by bridge lemmas
  - Proves agreement with the EVMYulLean-backed builtin evaluator
  - Kept out of the public EndToEnd semantic target

- **`ReferenceOracle/State.lean`** - Compatibility re-export for shared
  runtime state types

- **`Backends/EvmYulLeanNativeHarness.lean`** - Native EVMYulLean execution
  harness
  - Lowers emitted runtime code to executable EVMYulLean contracts
  - Provides the native `callDispatcher` result surface used by the active
    end-to-end theorem stack

- **`Backends/EvmYulLeanBodyClosure.lean`** - Native safe-body closure layer
  - Packages supported source fragments into `BridgedSafeStmts`
  - Proves emitted Yul fragments satisfy native bridge predicates

- **`Backends/EvmYulLeanBridgeLemmas.lean`** - Builtin agreement layer
  - Proves the Verity-side builtin comparison oracle agrees with EVMYulLean
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

The public compiler-correctness path does not compose through a custom Yul
interpreter. It lowers generated runtime Yul into EVMYulLean and compares the
projected native dispatcher result with IR/source semantics. Legacy builtin
comparison lemmas are retained only to discharge bridge predicates for emitted
fragments.

## References

- **Proof Inventory**: `Compiler/Proofs/README.md`
- **IR Semantics**: `Compiler/Proofs/IRGeneration/IRInterpreter.lean`
- **Verification Status**: `docs/VERIFICATION_STATUS.md`
