# Axioms in Verity

This file is the authoritative registry of axioms used by Verity proof code.

## Policy

Axioms are exceptional. When an axiom exists, it must have:

1. Explicit documentation in this file.
2. Source comment marking it as an axiom and linking to this file.
3. CI checks that validate usage assumptions.
4. A clear elimination path, when practical.

## Current Axioms

### 1. `keccak256_first_4_bytes`

**Location**: `Compiler/Selectors.lean:41`

**Statement**:
```lean
axiom keccak256_first_4_bytes (sig : String) : Nat
```

**Purpose**:
Computes function selectors (`bytes4(keccak256(signature))`) used in ABI dispatch.

**Why this is currently an axiom**:
Selector hashing is modeled as an external cryptographic primitive rather than reimplemented and proven in Lean.

**Soundness controls**:

- CI cross-checks selectors against `solc --hashes`.
- CI runs selector fixture checks to detect regressions.
- Compilation and tests fail if selector consistency drifts.

**Risk**: Low.

### 2. `exec_calldatasizeGuard_noop`

**Location**: `Compiler/Proofs/YulGeneration/Preservation.lean:161`

**Statement**:
```lean
private axiom exec_calldatasizeGuard_noop
```

**Purpose**:
Bridges the preservation proof over the generated `calldatasizeGuard` when calldata arity is sufficient.

**Why this is currently an axiom**:
The reduction from proof-runtime `calldatasize`/`lt` normalization to the intended arity check is still not fully mechanized in this theorem path.

**Risk**: Medium.

### 3. `eval_buildSwitch_hasSelectorExpr_eq_one`

**Location**: `Compiler/Proofs/YulGeneration/Preservation.lean:195`

**Statement**:
```lean
private axiom eval_buildSwitch_hasSelectorExpr_eq_one
```

**Purpose**:
Captures that the generated dispatch prelude computes `__has_selector = 1` because runtime calldata always contains the 4-byte selector word.

**Why this is currently an axiom**:
The execution fact is understood, but the modulo-aware builtin normalization for this exact `buildSwitch` path is still incomplete.

**Risk**: Medium.

### 4. `eval_iszero_hasSelector_after_set`

**Location**: `Compiler/Proofs/YulGeneration/Preservation.lean:204`

**Statement**:
```lean
private axiom eval_iszero_hasSelector_after_set
```

**Purpose**:
Bridges the local dispatch-state fact that after setting `__has_selector := 1`, evaluating `iszero(__has_selector)` yields `0`.

**Why this is currently an axiom**:
This is a small helper fact that currently sits inside the same partially-axiomatized dispatch-step proof boundary.

**Risk**: Low.

### 5. `execBuildSwitch_none_none_aux`

**Location**: `Compiler/Proofs/YulGeneration/Preservation.lean:250`

**Statement**:
```lean
private axiom execBuildSwitch_none_none_aux
```

**Purpose**:
Connects execution of the emitted `buildSwitch ... none none` block to the corresponding selector-switch step used in contract dispatch.

**Why this is currently an axiom**:
The step-by-step execution trace is known, but proving it directly through reducible `execYulFuel` remains technically brittle.

**Risk**: Medium.

### 6. `SwitchCaseBodyBridge`

**Location**: `Compiler/Proofs/YulGeneration/Preservation.lean:311`

**Statement**:
```lean
private axiom SwitchCaseBodyBridge
```

**Purpose**:
Bridges from the single-function body equivalence theorem to the actual generated runtime-dispatch execution shape (`switchCaseBody`, `__has_selector`, rollback shaping, and arity-guarded execution).

**Why this is currently an axiom**:
This remains the last contract-level proof gap between body-level Yul equivalence and full selector-dispatch preservation.

**Risk**: Medium.

### 7. `supported_function_body_correct_from_exact_state`

**Location**: `Compiler/Proofs/IRGeneration/Function.lean:810`

**Statement**:
```lean
axiom supported_function_body_correct_from_exact_state
```

**Purpose**:
Captures the second strategy-3 Layer-2 subgoal: once runtime/storage fields match
and variable bindings are exact, executing `compileStmtList ... fn.body` simulates
`SourceSemantics.execStmtList` for any supported function body.

**Why this is currently an axiom**:
This is the remaining generic body-simulation proof over the supported fragment.
The exact parameter-state reconstruction step is now proved, and `Function.lean`
now bypasses this axiom for `StmtListCompileCore` bodies, but the repo still
needs the broader expression/statement induction library for the remaining
supported body shapes.

**Risk**: Medium.

### 8. `supported_function_execIRFunction_eq_fuel`

**Location**: `Compiler/Proofs/IRGeneration/Function.lean:850`

**Statement**:
```lean
axiom supported_function_execIRFunction_eq_fuel
```

**Purpose**:
Bridges the current body-level theorem, stated with an explicit
`execIRFunctionFuel`, back to the public `execIRFunction` entrypoint used by the
whole-contract theorem surface.

**Why this is currently an axiom**:
The current proof spine still uses `length + 1` for `bodyStmts`, but this fuel
is actually too weak once compilation introduces nested `block`s. A minimal
checked counterexample now lives at
`Compiler/Proofs/IRGeneration/IRInterpreter.lean`
(`execIRStmts_single_block_stop_length_insufficient`). So this is no longer
just a missing bridge lemma: the supported-function path needs a structural
fuel refactor (`sizeOf`-style) before it can reuse
`execIRFunctionFuel_adequate` and eliminate this axiom cleanly. The core path
of `supported_function_correct` now already takes that non-axiomatic route:
`FunctionBody.exec_compileStmtList_core_extraFuel`,
`supported_function_body_correct_from_exact_state_core_extraFuel`, and the
`compileFunctionSpec_correct_of_body_supported_extraFuel` bridge thread a
structural `extraFuel` all the way to `sizeOf`. The remaining axiom usage is
therefore outside the proven core fragment, where the generic body proof still
falls back to the old `length + 1` spine. The terminal-`ite` preparation now
also includes explicit branch-size lower bounds
(`compiled_terminal_ite_body_size_ge_branchSizeOf`) and the stronger
branch-exec-fuel bounds
(`compiled_terminal_ite_body_size_ge_branchExecFuel` in
`Compiler/Proofs/IRGeneration/FunctionBody.lean`). The latter closes the
off-by-one needed to justify entering a chosen `ite` branch with the usual
`stmt-list + 1` fuel under a top-level `sizeOf` budget, which is the exact
arithmetic layer needed for the next recursive `StmtListTerminalCore` proof
over nested compiled blocks. That arithmetic is now also normalized into the
equalities `compiled_terminal_ite_body_block_extraFuel_eq`,
`compiled_terminal_ite_body_thenBranch_extraFuel_eq`, and
`compiled_terminal_ite_body_elseBranch_extraFuel_eq`, so the next recursive
proof can invoke the block and branch induction hypotheses without redoing
the `Nat` subtraction algebra inline. The scoped-freshness handoff for the
generated `__ite_cond` temporary is now also isolated by
`pickFreshName_not_mem_scope_of_subset` and
`bindingsExactlyMatchIRVarsOnScope_setFreshTemp_irrelevant`, so the remaining
terminal-`ite` proof no longer needs to inline fresh-name reasoning just to
preserve `bindingsExactlyMatchIRVarsOnScope` across the compiler-generated
temporary binding. The newest blocker extraction also adds the direct
execution-fuel rewrites
`compiled_terminal_ite_body_thenBranch_execFuel_eq` and
`compiled_terminal_ite_body_elseBranch_execFuel_eq`, plus the nonzero-fuel
facts `compiled_terminal_ite_body_letFuel_ne_zero`,
`compiled_terminal_ite_body_thenIfFuel_ne_zero`, and
`compiled_terminal_ite_body_blockStmtFuel_ne_zero`. Those are the exact
shapes consumed by the `execIRStmt_*_nonzeroFuel` lemmas, so the next
terminal-`ite` proof attempt can plug branch results into the compiled block
without reconstructing those entry-fuel facts by hand. The newest wrapper
`compiled_terminal_ite_body_block_execFuel_eq` also puts the inner
`block [let __ite_cond; if_; if_]` body fuel in the exact direction consumed
by the remaining block-lifting step, so the next proof no longer needs to
manually invert `compiled_terminal_ite_body_block_extraFuel_eq`. The symbolic
fuel wrappers for terminal IR steps are now also in place:
`execIRStmt_mstore_of_eval_nonzeroFuel`,
`execIRStmt_return32_of_memory_nonzeroFuel`, and
`execIRStmt_stop_nonzeroFuel` in
`Compiler/Proofs/IRGeneration/FunctionBody.lean`. That removes the last local
need to destruct `fuel` manually when the terminal-core proof reaches compiled
`mstore; return` / `stop` shapes under a structural budget. The remaining
freshness precondition is now also encoded explicitly as the reusable
`scopeNamesIncluded` invariant plus its terminal-`ite` specializations
`scopeNamesIncluded_compiled_terminal_ite_usedNames`,
`compiled_terminal_ite_temp_not_mem_scope`, and
`bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant`.
That closes the last missing link between the theorem’s logical scope and the
compiler’s concrete `inScopeNames` argument, so the next terminal-core proof
attempt can preserve the on-scope bindings invariant through the generated
`__ite_cond` temporary without rebuilding that subset argument inline.
The last failed direct proof attempt also clarified one theorem-shape issue:
the recursive terminal-core theorem must generalize `extraFuel` across the
induction, because the compiled `ite` branches consume different structural
slack than the enclosing body. The generic size-of list rewrites needed for
that schema are now exported as
`yulStmtList_sizeOf_cons_ge_tailFuel` and
`yulStmtList_sizeOf_cons_extraFuel_eq`, so the next attempt can reuse them
outside the local arithmetic section instead of re-proving the head/tail fuel
decomposition ad hoc. The newest arithmetic extraction also adds
`yulStmtList_sizeOf_two_cons_extraFuel_eq` and
`yulStmtList_sizeOf_two_cons_tail_extraFuel_eq`, which package the exact
two-statement head/tail decomposition needed for the compiled terminal
`mstore; return` prefixes without redoing nested `sizeOf` subtraction
normalization inside the recursive proof. The latest theorem attempt also made
the next arithmetic gap fully explicit: the recursive terminal-core proof
needs the same decompositions in direct execution-fuel form after consuming the
first one or two head statements, not just in `= ... + 1` introduction form.
Those are now extracted as
`yulStmtList_sizeOf_cons_tailExecFuel_eq`,
`yulStmtList_sizeOf_two_cons_secondExecFuel_eq`, and
`yulStmtList_sizeOf_two_cons_tailExecFuel_eq`, so the next attempt can rewrite
tail calls straight to `sizeOf whole + extraFuel - 1` / `- 2` instead of
re-deriving that arithmetic inline. The branch-entry wrappers are now also explicit:
`execIRStmt_compiled_terminal_ite_let`,
`evalIRExpr_compiled_terminal_ite_elseCond_of_zero`,
`execIRStmt_compiled_terminal_ite_thenIf_true`,
`execIRStmt_compiled_terminal_ite_thenIf_false`, and
`execIRStmt_compiled_terminal_ite_elseIf_true` package the exact generated
`__ite_cond` control-flow steps at the structural fuel the remaining theorem
needs, so the next proof can focus on composing branch results instead of
rebuilding those local rewrites and condition evaluations inline. The `then`
composition step is now also factored as
`execIRStmts_compiled_terminal_ite_then_of_irExec`, which lifts any non-
`continue` chosen-then-branch result through the whole compiled terminal-`ite`
block. The residual `else` path is now factored too: the exact one-step-
smaller singleton fuel step is packaged as
`execIRStmt_compiled_terminal_ite_elseIf_true_tail`, and the full lift through
the generated block and enclosing statement list is now
`execIRStmts_compiled_terminal_ite_else_of_irExec`. The remaining blocker in
this subpath is therefore no longer branch composition; it is reintroducing the
recursive semantic theorem for `StmtListTerminalCore` with the right structural
fuel schema so the branch induction hypotheses line up with these new `then` and
`else` composition lemmas.

**Risk**: Medium.

## Trusted Cryptographic Primitive (Non-Axiom)

### `ffi.KEC` (keccak256 via EVMYul FFI)

**Location**: used by `Compiler/Proofs/MappingSlot.lean` (`solidityMappingSlot`)

**Role**:
- Computes mapping storage slots as `keccak256(abi.encode(key, baseSlot))`.
- Aligns proof-level mapping addressing with Solidity/EVM flat storage layout.

**Why this is not listed as a Lean axiom**:
- It is a runtime external primitive (`@[extern]`-style FFI path), not a logical axiom in Lean's kernel.
- Trust is operational (correctness of linked crypto implementation), not proof-kernel extensibility.

**Operational trust assumptions**:
- Keccak implementation correctness in the linked FFI path.
- Standard collision-resistance assumptions for mapping-slot uniqueness/non-collision, matching Solidity/EVM assumptions.
- Machine-readable trust reports surface this runtime boundary as `keccak256_memory_slice_matches_evm` when contracts use `Expr.keccak256`.

**Soundness controls**:
- Mapping-slot abstraction boundary checks in CI.
- End-to-end proof/runtime regression suites that exercise mapping reads/writes through `mappingSlot`.

## External Call Module (ECM) Axioms

ECMs introduce trust assumptions via their `axioms` field. These are not Lean
kernel axioms — they are documented interface assumptions about external contracts
and precompiles. The compiler aggregates them at compile time, surfaces them
in `--verbose` output, and can fail closed for `unchecked` surfaces via
`--deny-unchecked-dependencies`.

### Standard Module Axioms

| Module | Axiom | Meaning |
|--------|-------|---------|
| `ERC20.safeTransfer` | `erc20_transfer_interface` | Target implements ERC-20 `transfer(address,uint256)` |
| `ERC20.safeTransferFrom` | `erc20_transferFrom_interface` | Target implements ERC-20 `transferFrom(address,address,uint256)` |
| `ERC20.safeApprove` | `erc20_approve_interface` | Target implements ERC-20 `approve(address,uint256)` |
| `ERC20.balanceOf` | `erc20_balanceOf_interface` | Target implements `balanceOf(address)` and returns one ABI-encoded `uint256` |
| `ERC20.allowance` | `erc20_allowance_interface` | Target implements `allowance(address,address)` and returns one ABI-encoded `uint256` |
| `ERC20.totalSupply` | `erc20_totalSupply_interface` | Target implements `totalSupply()` and returns one ABI-encoded `uint256` |
| `ERC4626.previewDeposit` | `erc4626_previewDeposit_interface` | Target implements `previewDeposit(uint256)` and returns one ABI-encoded `uint256` |
| `ERC4626.previewMint` | `erc4626_previewMint_interface` | Target implements `previewMint(uint256)` and returns one ABI-encoded `uint256` |
| `ERC4626.previewWithdraw` | `erc4626_previewWithdraw_interface` | Target implements `previewWithdraw(uint256)` and returns one ABI-encoded `uint256` |
| `ERC4626.previewRedeem` | `erc4626_previewRedeem_interface` | Target implements `previewRedeem(uint256)` and returns one ABI-encoded `uint256` |
| `ERC4626.convertToAssets` | `erc4626_convertToAssets_interface` | Target implements `convertToAssets(uint256)` and returns one ABI-encoded `uint256` |
| `ERC4626.convertToShares` | `erc4626_convertToShares_interface` | Target implements `convertToShares(uint256)` and returns one ABI-encoded `uint256` |
| `ERC4626.totalAssets` | `erc4626_totalAssets_interface` | Target implements `totalAssets()` and returns one ABI-encoded `uint256` |
| `ERC4626.asset` | `erc4626_asset_interface` | Target implements `asset()` and returns one ABI-encoded `address` |
| `ERC4626.maxDeposit` | `erc4626_maxDeposit_interface` | Target implements `maxDeposit(address)` and returns one ABI-encoded `uint256` |
| `ERC4626.maxMint` | `erc4626_maxMint_interface` | Target implements `maxMint(address)` and returns one ABI-encoded `uint256` |
| `ERC4626.maxWithdraw` | `erc4626_maxWithdraw_interface` | Target implements `maxWithdraw(address)` and returns one ABI-encoded `uint256` |
| `ERC4626.maxRedeem` | `erc4626_maxRedeem_interface` | Target implements `maxRedeem(address)` and returns one ABI-encoded `uint256` |
| `ERC4626.deposit` | `erc4626_deposit_interface` | Target implements `deposit(uint256,address)` and returns one ABI-encoded `uint256` |
| `Oracle.oracleReadUint256` | `oracle_read_uint256_interface` | Target implements the selected read-only oracle interface and returns one ABI-encoded `uint256` |
| `Precompiles.ecrecover` | `evm_ecrecover_precompile` | EVM precompile at address 0x01 behaves per Yellow Paper |
| `Callbacks.callback` | `callback_target_interface` | Callback target processes ABI-encoded arguments correctly |
| `Calls.withReturn` | `external_call_abi_interface` | Target contract function matches declared selector and ABI |

### Third-Party Module Axioms

Third-party ECMs (external Lean packages) document their axioms in their own
`AXIOMS.md`. All axioms — standard and third-party — are aggregated and reported
at compile time. See `docs/EXTERNAL_CALL_MODULES.md` for details.

**Risk**: Low. ECM axioms are interface assumptions (not proof-kernel extensions)
scoped to contracts that use the module.

## Eliminated Axioms (Historical)

The repository removed prior axioms related to IR and Yul expression and statement equivalence and address injectivity by making interpreters total and by using a bounded-nat `Address` representation.

These removals reduced prior axiom debt. The Layer 3 switch-case bridge still has
a small explicit preservation-side axiom boundary for dispatch-step normalization
and case-body bridging; those active axioms are tracked above.

## Non-Axiom: Arithmetic Semantics

Wrapping modular arithmetic at 2^256 is **proven**, not assumed. All 15 pure builtins (add, sub, mul, div, mod, lt, gt, eq, iszero, and, or, xor, not, shl, shr) have formal wrapping proofs in `Compiler/Proofs/ArithmeticProfile.lean`. The EVMYulLean bridge currently has universal equivalence lemmas for 15 of them (`add`, `sub`, `mul`, `div`, `mod`, `lt`, `gt`, `eq`, `iszero`, `and`, `or`, `xor`, `not`, `shl`, `shr`) in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean`, with no remaining pure builtins relying only on concrete bridge checks. This is a design choice matching EVM semantics, not a trust assumption. See [`docs/ARITHMETIC_PROFILE.md`](docs/ARITHMETIC_PROFILE.md) for the full specification.

## Trust Summary

- Active axioms: 8
- Production blockers from axioms: 0
- Enforcement: `scripts/check_axioms.py` ensures this file tracks exact source location.
- Compilation-path totalization work in `Compiler/CompilationModel.lean` does not
  add, remove, or modify Lean axioms; it only replaces `partial def` recursion
  with explicit structural termination proofs (including dynamic-param scope
  checks, statement read/write analyzers, statement-list validation walkers,
  and all Expr/Stmt validation walkers: scoped-identifier, interop,
  internal-call-shape, external-call-target, and event-argument-shape).
- Macro front-end extensions (including explicit `getMappingUint` /
  `setMappingUint` translation support in `Verity/Macro/Translate.lean`) do not
  add, remove, or modify Lean axioms.
- The semantic bridge and typed-IR migration work (Issues #998 and #1060:
  `Compiler/Proofs/EndToEnd.lean`, `Compiler/Proofs/SemanticBridge.lean`,
  `Verity/Macro/Bridge.lean`, and the `Compiler/TypedIR*` pipeline)
  does not add, remove, or modify Lean axioms. `SemanticBridge.lean` now has
  zero `sorry`. The typed-IR compilation path (`Compiler/TypedIRCompiler*.lean`) also
  has zero `sorry`.

## Maintenance Rule

Any commit that adds, removes, renames, or moves an axiom must update this file in the same commit.

If this file is stale, trust analysis is stale.

**Last Updated**: 2026-03-08
