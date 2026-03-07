# Interpreter Feature-Support Matrix

This document describes the feature coverage of Verity's reference interpreters,
the EVMYulLean builtin bridge, and their proof status.

Machine-readable version: [`artifacts/interpreter_feature_matrix.json`](../artifacts/interpreter_feature_matrix.json).

---

## Interpreters

| Interpreter | File | Entry Point | Purpose |
|---|---|---|---|
| **IRInterpreter** | `Compiler/Proofs/IRGeneration/IRInterpreter.lean` | `execIRStmts` | Layer-2 preservation proofs |
| **YulSemantics** | `Compiler/Proofs/YulGeneration/Semantics.lean` | `execYulFuel` | Layer-3 Yul execution semantics |
| **EVMYulLean bridge** | `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeTest.lean` | `evalBuiltinCallViaEvmYulLean` | Pure builtin evaluation via EVMYulLean UInt256 |

The `SpecInterpreter` has been removed. EDSL semantics are now defined directly in `Verity/Core.lean` via the `Contract` monad and composed with IR/Yul layers through `SemanticBridge` proofs.

---

## Expression Features

| Feature | Constructor | Spec (basic) | Spec (fuel) | IR | EVMYulLean | Proof |
|---|---|:---:|:---:|:---:|:---:|:---:|
| Literals | `Expr.literal` | ok | ok | ok | -- | proved |
| Parameters | `Expr.param` | ok | ok | -- | -- | proved |
| Constructor args | `Expr.constructorArg` | ok | ok | -- | -- | proved |
| Storage read | `Expr.storage` | ok | ok | ok | -- | proved |
| Mapping read | `Expr.mapping` | ok | ok | ok | -- | proved |
| Mapping + word offset | `Expr.mappingWord` | ok | ok | -- | -- | proved |
| Packed mapping | `Expr.mappingPackedWord` | ok | ok | -- | -- | proved |
| Double mapping | `Expr.mapping2` | ok | ok | -- | -- | proved |
| Double mapping + word | `Expr.mapping2Word` | ok | ok | -- | -- | proved |
| Uint256-keyed mapping | `Expr.mappingUint` | ok | ok | -- | -- | proved |
| Struct member (single) | `Expr.structMember` | ok | ok | -- | -- | proved |
| Struct member (double) | `Expr.structMember2` | ok | ok | -- | -- | proved |
| `caller` | `Expr.caller` | ok | ok | ok | del | proved |
| `msg.value` | `Expr.msgValue` | ok | ok | -- | -- | proved |
| `block.timestamp` | `Expr.blockTimestamp` | ok | ok | -- | -- | proved |
| `address(this)` | `Expr.contractAddress` | **0** | **0** | -- | -- | n/m |
| `chainid` | `Expr.chainid` | **0** | **0** | -- | -- | n/m |
| `mload` | `Expr.mload` | **0** | **0** | ok | -- | partial |
| `keccak256` | `Expr.keccak256` | **0** | **0** | -- | -- | n/m |
| `call` | `Expr.call` | **0** | **0** | -- | -- | n/m |
| `staticcall` | `Expr.staticcall` | **0** | **0** | -- | -- | n/m |
| `delegatecall` | `Expr.delegatecall` | **0** | **0** | -- | -- | n/m |
| Arithmetic | `add/sub/mul/div/mod` | ok | ok | ok | ok | proved |
| Bitwise | `and/or/xor/shl/shr` | ok | ok | ok | ok | proved |
| Bitwise | `not` | ok | ok | ok | ok | partial |
| Comparison | `eq/lt/gt/le/ge` | ok | ok | ok | ok | proved |
| Logical | `logicalAnd/Or/Not` | ok | ok | -- | -- | proved |
| Fixed-point math | `mulDivDown/Up, wMulDown/wDivUp, min/max` | ok | ok | -- | -- | proved |
| Internal call (expr) | `Expr.internalCall` | **0** | ok | -- | -- | proved |
| Local variable | `Expr.localVar` | ok | ok | ok | -- | proved |
| External call (linked) | `Expr.externalCall` | ok | ok | -- | -- | assumed |
| Array length | `Expr.arrayLength` | ok | ok | -- | -- | proved |
| Array element | `Expr.arrayElement` | ok | ok | -- | -- | proved |

Legend: **ok** = supported, **0** = returns 0 (not modeled), **del** = delegated to Verity path, **--** = not applicable at this layer, **n/m** = not modeled in proofs.

---

## Statement Features

| Feature | Constructor | Spec (basic) | Spec (fuel) | IR | Proof |
|---|---|:---:|:---:|:---:|:---:|
| Let binding | `Stmt.letVar` | ok | ok | ok | proved |
| Assignment | `Stmt.assignVar` | ok | ok | ok | proved |
| Storage write | `Stmt.setStorage` | ok | ok | ok | proved |
| Mapping write | `Stmt.setMapping` | ok | ok | ok | proved |
| Mapping + word write | `Stmt.setMappingWord` | ok | ok | -- | proved |
| Packed mapping write | `Stmt.setMappingPackedWord` | ok | ok | -- | proved |
| Double mapping write | `Stmt.setMapping2` | ok | ok | -- | proved |
| Double mapping + word | `Stmt.setMapping2Word` | ok | ok | -- | proved |
| Uint256-keyed write | `Stmt.setMappingUint` | ok | ok | -- | proved |
| Struct member write | `Stmt.setStructMember` | ok | ok | -- | proved |
| Struct member 2 write | `Stmt.setStructMember2` | ok | ok | -- | proved |
| Require | `Stmt.require` | ok | ok | ok | proved |
| Require (custom error) | `Stmt.requireError` | ok | ok | -- | proved |
| Revert (custom error) | `Stmt.revertError` | ok | ok | -- | proved |
| Return (single) | `Stmt.return` | ok | ok | ok | proved |
| Return (multi) | `Stmt.returnValues` | ok | ok | -- | proved |
| Return (array) | `Stmt.returnArray` | ok | ok | -- | proved |
| Return (bytes) | `Stmt.returnBytes` | ok | ok | -- | proved |
| Return (storage words) | `Stmt.returnStorageWords` | ok | ok | -- | proved |
| Stop | `Stmt.stop` | ok | ok | ok | proved |
| If/else | `Stmt.ite` | ok | ok | ok | proved |
| For-each loop | `Stmt.forEach` | **rev** | ok | ok | proved |
| Event emission | `Stmt.emit` | ok | ok | -- | proved |
| Internal call (stmt) | `Stmt.internalCall` | **rev** | ok | -- | proved |
| Internal call assign | `Stmt.internalCallAssign` | **rev** | ok | -- | proved |
| Memory store | `Stmt.mstore` | **rev** | **rev** | ok | partial |
| Calldatacopy | `Stmt.calldatacopy` | nop | nop | -- | n/m |
| Returndatacopy | `Stmt.returndataCopy` | **rev** | **rev** | -- | n/m |
| Revert returndata | `Stmt.revertReturndata` | **rev** | **rev** | -- | n/m |
| Raw log | `Stmt.rawLog` | **rev** | **rev** | -- | n/m |
| External call bind | `Stmt.externalCallBind` | **rev** | **rev** | -- | n/m |
| ECM | `Stmt.ecm` | **rev** | **rev** | -- | n/m |

Legend: **ok** = supported, **rev** = reverts (not modeled), **nop** = no-op (codegen concern), **--** = not applicable, **n/m** = not modeled.

---

## Builtin Bridge (Verity vs EVMYulLean)

| Builtin | Verity | EVMYulLean | Agreement Proved |
|---|:---:|:---:|:---:|
| `add` | ok | ok | yes |
| `sub` | ok | ok | yes |
| `mul` | ok | ok | yes |
| `div` | ok | ok | yes |
| `mod` | ok | ok | yes |
| `lt` | ok | ok | yes |
| `gt` | ok | ok | yes |
| `eq` | ok | ok | yes |
| `iszero` | ok | ok | yes |
| `and` | ok | ok | yes |
| `or` | ok | ok | yes |
| `xor` | ok | ok | yes |
| `not` | ok | ok | yes |
| `shl` | ok | ok | yes |
| `shr` | ok | ok | yes |
| `sload` | ok | del | -- |
| `caller` | ok | del | -- |
| `calldataload` | ok | del | -- |
| `mappingSlot` | ok | del | -- |

Legend: **ok** = native evaluation, **del** = delegated to Verity path (bridge returns `none`).

15/19 builtins have bridge agreement coverage between Verity and EVMYulLean evaluation paths. 15 are discharged by universal symbolic lemmas in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean`, and none still require concrete-only regression coverage. The remaining 4 are state-dependent or Verity-specific helpers that remain on the Verity evaluation path.

---

## Proof Status Summary

| Category | Proved | Assumed | Partial | Not Modeled |
|---|---|---|---|---|
| Expression features | 25 | 1 (`externalCall`) | 1 (`mload`) | 6 |
| Statement features | 24 | 0 | 1 (`mstore`) | 7 |
| Builtins (agreement) | 15 | 0 | 0 | 4 (delegated) |

**Not-modeled features** are handled correctly by the compiler but are outside the current proof scope. They include low-level calls, returndata handling, linear memory, contract introspection, and external call modules. These features are validated by differential testing (70,000+ test vectors against actual EVM execution).

---

## Known Limitations

1. **Linear memory**: The IRInterpreter has single-word memory support. Full linear memory coverage requires EVMYulLean semantic integration.

2. **Low-level calls**: `call`/`staticcall`/`delegatecall` and `externalCallBind`/`ecm` are compiler-only features validated by Foundry testing, not modeled in proof interpreters.

---

**Last Updated**: 2026-02-27
**Machine-readable artifact**: `artifacts/interpreter_feature_matrix.json`
