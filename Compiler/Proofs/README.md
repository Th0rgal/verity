# Compiler Verification Proofs

Formal verification proofs for the Verity compiler, proving correctness across three layers.

**Scope**: These proofs cover the compilation path `EDSL -> CompilationModel -> IR -> Yul`. See `TRUST_ASSUMPTIONS.md` for the full trust-boundary description.

## Verification Layers

- **Layer 1: EDSL ≡ CompilationModel (`CompilationModel`)** — User contracts satisfy their compilation models (`Verity/Proofs/<Name>/` + `Compiler/Proofs/SemanticBridge.lean`). The hybrid typed-IR pipeline (`Verity/Core/Free/TypedIRCompilerCorrectness.lean`) provides a generic compilation-correctness theorem; macro-generated bridge theorems eliminate `sorry` for the supported subset.
- **Layer 2: CompilationModel (`CompilationModel`) → IR** — IR generation preserves compilation-model semantics (`Compiler/Proofs/IRGeneration/`).
- **Layer 3: IR → Yul** — All statement equivalence proofs proven (`Compiler/Proofs/YulGeneration/`).

Key entry points:

- Semantic bridge: `Compiler/Proofs/SemanticBridge.lean`
- Typed IR correctness: `Verity/Core/Free/TypedIRCompilerCorrectness.lean`
- IR generation and proofs: `Compiler/Proofs/IRGeneration/`
- Lowering boundary scaffolding proofs: `Compiler/Proofs/Lowering/`
- Yul semantics and preservation: `Compiler/Proofs/YulGeneration/`

The lowering boundary currently includes transition bridge lemmas that connect
`SupportedEDSLContract` lowering cases to existing Layer 1 correctness results
for the full currently supported subset (`SimpleStorage`, `Counter`, `Owned`,
`Ledger`, `OwnedCounter`, `SimpleToken`, `SafeCounter`), including read/write
bridge coverage across getter and mutating entrypoints in that subset
(`ledger.transfer`, `simpleToken.mint`, and `simpleToken.transfer` included),
plus explicit revert-path bridge coverage for owner-gated and
insufficient-balance behaviors in `Owned`, `OwnedCounter`, `Ledger`, and
`SimpleToken`, plus overflow/underflow revert coverage in `SafeCounter`.
Getter-side read-only state-preservation bridges are also explicit for
supported getter entrypoints. Parser-determinism lemmas are also included for
`--edsl-contract` IDs (`supportedEDSLContractName_injective`,
`parseSupportedEDSLContract_roundtrip_unique`,
`supportedEDSLContractNames_nodup`).
The same module also composes parsed CLI IDs with lowering semantics at the
API boundary (`lowerFromParsedSupportedContract_preserves_interpretSpec`).
Unknown selected-ID diagnostics are centralized at parser level via
`parseSupportedEDSLContract_eq_error_of_unknown`.
Singleton selected-ID map traversal helper lemmas are also explicit:
`lowerFromParsedSupportedContract_singleton_eq_ok`,
`lowerFromParsedSupportedContract_singleton_eq_ok_of_parse_ok`,
`lowerFromParsedSupportedContract_singleton_eq_error`,
`lowerFromParsedSupportedContract_cons_eq_ok_of_lower_ok`,
`lowerFromParsedSupportedContract_cons_eq_error_of_head_error`,
`lowerFromParsedSupportedContract_cons_eq_error_of_tail_error`,
`lowerFromParsedSupportedContract_pair_eq_ok_of_lower_ok`,
`lowerFromParsedSupportedContract_pair_eq_ok_of_parse_ok`,
`lowerFromParsedSupportedContract_mapM_eq_ok_of_parse_ok`,
`lowerFromParsedSupportedContract_append_eq_ok_of_parse_ok`,
`lowerFromParsedSupportedContract_append_eq_error_of_parse_error`.
CLI parsed-ID handling is centralized in `Compiler/Lowering/FromEDSL.lean` via
`parseSupportedEDSLContract`, `lowerFromParsedSupportedContract`, and
`lowerRequestedSupportedEDSLContracts`.
Centralized selected/default helper behavior is also explicit in proofs via
`lowerRequestedSupportedEDSLContracts_default_eq`,
`supportedEDSLContractNames_mapM_lowerFromParsed_eq_ok`,
`lowerRequestedSupportedEDSLContracts_default_eq_ok_supported`,
`lowerRequestedSupportedEDSLContracts_duplicate_eq_error`,
`lowerRequestedSupportedEDSLContracts_selected_eq`,
`lowerRequestedSupportedEDSLContracts_selected_eq_ok_of_mapM_lower_ok`,
`lowerRequestedSupportedEDSLContracts_selected_eq_ok_of_parse_ok`,
`lowerRequestedSupportedEDSLContracts_selected_append_eq_ok_of_lower_ok`,
`lowerRequestedSupportedEDSLContracts_selected_append_eq_ok_of_split_ok`,
`lowerRequestedSupportedEDSLContracts_selected_append_eq_ok_of_parse_ok`,
`lowerRequestedSupportedEDSLContracts_selected_cons_eq_ok_of_lower_ok`,
`lowerRequestedSupportedEDSLContracts_selected_cons_eq_ok_of_parse_ok`,
`lowerRequestedSupportedEDSLContracts_selected_cons_eq_ok_of_tail_ok`,
`lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_head_error`,
`lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_tail_error`,
`lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_lower_error`,
`lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_parse_error`,
`lowerRequestedSupportedEDSLContracts_selected_eq_error_of_mapM_lower_error`,
`lowerRequestedSupportedEDSLContracts_selected_append_eq_error_of_lower_error`,
`lowerRequestedSupportedEDSLContracts_selected_singleton_eq_error_of_lower_error`,
`lowerRequestedSupportedEDSLContracts_selected_singleton_eq_error_of_parse_error`,
`lowerRequestedSupportedEDSLContracts_selected_head_eq_error_of_parse_error`,
`lowerRequestedSupportedEDSLContracts_selected_tail_eq_error_of_parse_error`,
`lowerRequestedSupportedEDSLContracts_selected_append_eq_error_of_parse_error`,
`lowerRequestedSupportedEDSLContracts_selected_append_eq_error_of_prefix_parse_ok`,
`lowerRequestedSupportedEDSLContracts_selected_append_unknown_eq_error_of_prefix_parse_ok`,
`lowerRequestedSupportedEDSLContracts_selected_unknown_head_eq_error`,
`lowerRequestedSupportedEDSLContracts_selected_singleton_unknown_eq_error`,
`lowerRequestedSupportedEDSLContracts_selected_unknown_tail_eq_error`,
`lowerRequestedSupportedEDSLContracts_selected_append_unknown_eq_error`,
`lowerRequestedSupportedEDSLContracts_selected_singleton_eq_ok_of_parse_ok`,
`lowerRequestedSupportedEDSLContracts_selected_singleton_eq_ok`,
`lowerRequestedSupportedEDSLContracts_selected_pair_eq_ok`,
`lowerRequestedSupportedEDSLContracts_selected_triple_eq_ok`,
`lowerRequestedSupportedEDSLContracts_full_eq_default`.
`Compiler/CompileDriver.lean` uses this same selected/default helper path directly,
so runtime selected/default `--edsl-contract` behavior stays aligned with the
proven parsing/lowering boundary.
It also exposes API-boundary preservation lemmas for both transition entrypoints:
`lowerFromEDSLSubset_supported_preserves_interpretSpec` and
`lowerFromEDSLSubset_manualBridge_preserves_interpretSpec`.

Layer 1 proofs live in `Verity/Proofs/<Name>/Basic.lean` and `Correctness.lean`. The typed-IR compilation correctness pipeline is in `Verity/Core/Free/TypedIRCompilerCorrectness.lean`, with cross-layer bridge proofs in `Compiler/Proofs/SemanticBridge.lean`.

## Build

```bash
lake build                                      # Build everything
lake build Verity.Specs.SimpleStorage.Proofs    # Build one contract's proofs
```

All proofs complete — no `sorry` warnings expected.

## Infrastructure

### SpecInterpreter ([SpecInterpreter.lean](../../Verity/Proofs/Stdlib/SpecInterpreter.lean))

Execution semantics for the compilation-model language (`CompilationModel` today).

**Key Types**: `EvalContext` (execution environment), `SpecStorage` (abstract storage), `ExecState` (execution state with storage, return value, and halt flag).

**Key Functions**: `evalExpr` (expression evaluation), `execStmt` (statement execution), `interpretSpec` (top-level interpreter).

### Automation Library ([Automation.lean](../../Verity/Proofs/Stdlib/Automation.lean))

Proven helper lemmas for common proof patterns:

- **Safe arithmetic**: `safeAdd_some_iff_le`, `safeSub_some_iff_ge`, etc.
- **Storage operations**: `getStorage_runState`, `setStorage_runState`
- **Contract results**: `@[simp]` lemmas for `isSuccess`

## Proof Patterns

### 1. Simple Getters

```lean
theorem getter_correct (state : ContractState) (sender : Address) :
    let edslValue := (getValue.runValue { state with sender := sender }).val
    let specResult := interpretSpec spec (edslToSpecStorage state) tx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  unfold getValue Contract.runValue spec interpretSpec
  simp [getStorage, execFunction, execStmt, evalExpr]
```

### 2. Storage Updates

```lean
theorem setter_correct (state : ContractState) (value : Uint256) (sender : Address) :
    let finalState := (setValue value).runState { state with sender := sender }
    finalState.storage slot = value := by
  unfold setValue Contract.runState
  simp [setStorage]
```

### 3. Boundary Conditions with Safe Arithmetic

```lean
theorem safe_op_succeeds (state : ContractState) (sender : Address)
    (h : condition) :
    let result := operation.run { state with sender := sender }
    result.isSuccess = true := by
  unfold operation Contract.run
  have h_safe : (safeOp a b).isSome := by
    rw [safeOp_some_iff_condition]; exact h
  simp [h_safe]
```

### 4. Access Control

```lean
theorem authorized_operation (state : ContractState) (sender : Address)
    (h : state.storageAddr ownerSlot = sender) :
    let result := operation.run { state with sender := sender }
    result.isSuccess = true := by
  unfold operation onlyOwner
  simp [h, msgSender, require]
```

## Common Tactics

| Tactic | Use case |
|--------|----------|
| `omega` | Linear arithmetic on naturals/integers |
| `simp [lemmas]` | Automatic simplification (prefer `simp only` for complex goals) |
| `unfold f` | Unfold definitions incrementally |
| `cases h : expr` | Case analysis on conditions or datatypes |
| `by_cases h : p` | Split proof on a Boolean condition |

## Resources

- [Lean 4 Documentation](https://lean-lang.org/documentation/)
- [Lean 4 Theorem Proving](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathlib Tactics](https://leanprover-community.github.io/mathlib4_docs/tactics.html)
