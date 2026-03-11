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

### 2. `supported_function_body_correct_from_exact_state`

**Location**: `Compiler/Proofs/IRGeneration/Function.lean:915`

**Statement**:
```lean
axiom supported_function_body_correct_from_exact_state
```

**Purpose**:
Captures the second strategy-3 Layer-2 subgoal: once runtime/storage fields match
and variable bindings are exact, executing `compileStmtList ... fn.body` simulates
`SourceSemantics.execStmtList` for a single supported non-core function body.

**Why this is currently an axiom**:
This is the remaining generic body-simulation proof over the supported fragment.
The exact parameter-state reconstruction step is now proved, and `Function.lean`
now bypasses this axiom for both `StmtListCompileCore` and `StmtListTerminalCore`
bodies. The axiom statement has therefore been narrowed twice: first to the
non-core fragment only, and now to the exact per-function
`SupportedFunction model.fields fn` witness actually consumed by the caller
instead of the larger whole-contract `SupportedSpec` package and
selector-bookkeeping context. The repo still needs the broader
expression/statement induction library for the remaining supported non-terminal
body shapes.
That closure now reaches the checked terminal-core fragment as well, so the
remaining trust surface sits outside the proved `StmtListTerminalCore` path.
The latest checked extractions here are the scope-local
whole-fuel prefix wrappers
`execIRStmts_compiled_let_core_append_wholeFuel_of_scope`,
`execIRStmts_compiled_assign_core_append_wholeFuel_of_scope`,
`execIRStmts_compiled_require_core_pass_append_wholeFuel_of_scope`,
`execIRStmts_compiled_require_core_fail_append_wholeFuel_of_scope`, and
`execIRStmts_compiled_return_core_append_wholeFuel_of_scope` in
`FunctionBody.lean`. The newest checked extractions close the next layer above
that arithmetic: `execIRStmts_compiled_let_core_tailExtraFuel_of_scope`,
`execIRStmts_compiled_assign_core_tailExtraFuel_of_scope`, and
`execIRStmts_compiled_require_core_pass_tailExtraFuel_of_scope` now package the
ordinary singleton-prefix cases directly in the tail-IH fuel shape that the
recursive `StmtListTerminalCore` theorem wants. The newest checked layer above
that arithmetic is semantic rather than fuel-only:
`stmtResultMatchesIRExec_compiled_let_core_tailExtraFuel_of_scope`,
`stmtResultMatchesIRExec_compiled_assign_core_tailExtraFuel_of_scope`,
`stmtResultMatchesIRExec_compiled_require_core_pass_tailExtraFuel_of_scope`,
`stmtResultMatchesIRExec_compiled_return_core_append_wholeFuel_of_scope`, and
`stmtResultMatchesIRExec_compiled_stop_core_append_wholeFuel` now lift those
compiled head-step facts directly into `stmtResultMatchesIRExec`. The terminal
`ite` branch-entry blocker described in issue `#1564` is now discharged:
`FunctionBody.lean` proves both the ordinary then-branch entry theorem and the
already-spent-token else-branch entry theorem, and `supported_function_correct`
uses those lemmas to bypass this axiom for `StmtListTerminalCore` bodies as
well. The remaining blocker is therefore narrower again: a generic proof that
the still-unproved supported non-terminal body shapes preserve
`stmtResultMatchesIRExec` once parameter loading has established exact state.
The highest-leverage remaining targets are storage writes, mapping writes, and
other supported fragment shapes that sit beyond the terminal-core recursion.
The newest checked layer above that is the explicit-`bodyIR`
`exec_compileStmtList_terminal_core_sizeOf_extraFuel` theorem, with
`Function.supported_function_body_correct_from_exact_state_terminal_core_extraFuel`
threading it into the generic per-function proof. The remaining blocker is now
the broader supported non-core fragment outside `StmtListTerminalCore`,
including storage and mapping writes.

This leaves the trusted statement closer to the real blocker: a local proof that
the still-unproved non-terminal supported statement shapes preserve
`stmtResultMatchesIRExec` once parameter loading has established exact state.

Note: this axiom's signature was widened with an `extraFuel : Nat` parameter
when `supported_function_execIRFunction_eq_fuel` was eliminated, but it is not
universal over arbitrary fuel anymore. The statement now requires a lower-bound
precondition `sizeOf bodyStmts - bodyStmts.length ≤ extraFuel`, matching the
structural slack needed for nested blocks. The caller in
`supported_function_correct` discharges that precondition with
`extraFuel := sizeOf irFn.body - irFn.body.length`, which lets the non-core path
bridge to `sizeOf`-style fuel via the same
`compileFunctionSpec_correct_of_body_supported_extraFuel` and
`execIRFunctionFuel_adequate` machinery that the core path already uses.

**Risk**: Medium.

_`supported_function_execIRFunction_eq_fuel` was eliminated; see Eliminated Axioms below._

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

Specifically:
- `execYulStmtsFuel_fuel_adequate` was eliminated by proving fuel-monotonicity
  via strong induction on `sizeOf target` over `execYulFuel`. The proof
  introduces a `yulStmtsLoopFree` predicate (compiled code never contains
  `for_` loops) and a key lemma `execYulFuel_succ_eq` showing that for
  loop-free Yul programs, adding one unit of fuel beyond `sizeOf body + 1`
  does not change the result. The callers (`yulCodegen_preserves_semantics`,
  `layer3_contract_preserves_semantics`, `simpleStorage_endToEnd`) now take
  a `hLoopFree` hypothesis dischargeable via `rfl` for compiled output.
- `execIRStmtsFuel_adequate` was eliminated by making the IR interpreter total
  (fuel-based). The fuel adequacy relationship is now trivially `rfl` and the
  Layer 3 proof chain flows through
  `ir_yul_function_equiv_from_state_of_stmt_equiv` without any external adequacy
  hypothesis.
- `supported_function_execIRFunction_eq_fuel` was eliminated by widening the
  `supported_function_body_correct_from_exact_state` axiom to accept an
  `extraFuel` parameter, then refactoring the non-core branch of
  `supported_function_correct` to thread `extraFuel := sizeOf irFn.body -
  irFn.body.length` through the same `sizeOf`-style fuel bridge
  (`compileFunctionSpec_correct_of_body_supported_extraFuel` and
  `execIRFunctionFuel_adequate`) that the core path already uses. This avoids
  the unsound `length + 1` fuel budget that is insufficient for nested `block`s.

These removals reduced prior axiom debt. The Layer 3 switch-case bridge no longer
uses a dedicated kernel axiom for `__has_selector` dead-variable irrelevance.
Instead, `Compiler/Proofs/YulGeneration/Preservation.lean` exposes:

- syntactic predicates `yulExprNoRef` / `yulStmtNoRef` / `yulStmtsNoRef`
- an explicit theorem hypothesis `HasSelectorDeadBridge`

That keeps the remaining trust boundary visible in theorem signatures without
adding a new Lean axiom.

## Non-Axiom: Arithmetic Semantics

Wrapping modular arithmetic at 2^256 is **proven**, not assumed. All 15 pure builtins (add, sub, mul, div, mod, lt, gt, eq, iszero, and, or, xor, not, shl, shr) have formal wrapping proofs in `Compiler/Proofs/ArithmeticProfile.lean`. The EVMYulLean bridge currently has universal equivalence lemmas for 15 of them (`add`, `sub`, `mul`, `div`, `mod`, `lt`, `gt`, `eq`, `iszero`, `and`, `or`, `xor`, `not`, `shl`, `shr`) in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean`, with no remaining pure builtins relying only on concrete bridge checks. This is a design choice matching EVM semantics, not a trust assumption. See [`docs/ARITHMETIC_PROFILE.md`](docs/ARITHMETIC_PROFILE.md) for the full specification.

## Trust Summary

- Active axioms: 2
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
  `Compiler/Proofs/EndToEnd.lean`, `Contracts/Proofs/SemanticBridge.lean`,
  `Verity/Macro/Bridge.lean`, and the `Compiler/TypedIR*` pipeline)
  does not add, remove, or modify Lean axioms. `SemanticBridge.lean` now has
  zero `sorry`. The typed-IR compilation path (`Compiler/TypedIRCompiler*.lean`) also
  has zero `sorry`.

## Maintenance Rule

Any commit that adds, removes, renames, or moves an axiom must update this file in the same commit.

If this file is stale, trust analysis is stale.

**Last Updated**: 2026-03-10
