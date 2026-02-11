# Dumb Contracts Research Status

## Current State: 277 Theorems, 7/7 Contracts Verified (2026-02-10)

### Summary
**Full Verification Achieved**: All 277 theorems proven with zero `sorry`, zero axioms, zero errors. Guard modeling via `ContractResult` type enables complete verification of `require`-guarded operations. Every contract now has both Basic.lean and Correctness.lean proof files. Supply conservation proofs, balance conservation proofs, storage isolation proofs, and safe arithmetic correctness proofs extend verification depth.

All 7 contract patterns verified at 100%:
- SimpleStorage (19 theorems: 12 basic + 7 correctness) — 100% proven
- Counter (29 theorems: 19 basic + 10 correctness) — 100% proven
- Owned (22 theorems: 18 basic + 4 correctness) — 100% proven
- SimpleToken (64 theorems: 36 basic + 10 correctness + 9 supply conservation + 9 isolation) — 100% proven
- OwnedCounter (48 theorems: 29 basic + 5 correctness + 14 isolation) — 100% proven
- Ledger (40 theorems: 21 basic + 6 correctness + 13 conservation) — 100% proven
- SafeCounter (30 theorems: 22 basic + 8 correctness) — 100% proven

Additional:
- Stdlib/Math (25 theorems: safeAdd + safeSub + safeMul + safeDiv correctness) — 100% proven

**Total: 277/277 theorems fully proven (100%) — zero sorry, zero axioms**

### Verification Tiers Achieved

**Tier 1: Safety Properties**
- Balance non-negativity (implicit via Nat)
- Access control respected (mint reverts when not owner)
- No overdrafts (transfer reverts with insufficient balance)
- Overflow/underflow protection (SafeCounter revert proofs)
- Safe arithmetic bounds (safeAdd/safeSub/safeMul/safeDiv result bounds)

**Tier 2: Functional Correctness**
- Transfer moves exact amount (sender decreases, recipient increases)
- Mint increases supply correctly
- All state transitions match specifications
- Constructor initializes correctly
- safeAdd/safeSub/safeMul/safeDiv return correct results or none on overflow/underflow/div-by-zero
- Decrement at zero saturates to zero (Counter edge case)

**Tier 3: Invariants**
- WellFormedState preserved by all operations (constructor, mint, transfer, transferOwnership, reads)
- Owner stability (mint and transfer don't change owner)
- Storage isolation proven standalone for all contracts (SimpleStorage, Counter, SafeCounter)
- **Storage isolation proven for SimpleToken** (supply_storage_isolated, balance_mapping_isolated, owner_addr_isolated for constructor/mint/transfer)
- **Storage isolation proven for OwnedCounter** (count_preserves_owner, owner_preserves_count, context_preserved, mapping isolation for constructor/increment/decrement/transferOwnership)
- Context preservation (sender, thisAddress) proven standalone for all contracts
- Address/mapping storage isolation proven standalone (SimpleStorage, Counter)
- state_preserved_except_count invariant proven (Counter)
- Bounds preservation (SafeCounter count stays within MAX_UINT256)
- Transfer preserves non-mapping storage (Ledger)
- Constructor establishes supply_bounds_balances invariant (SimpleToken)

**Tier 4: Composition**
- mint→balanceOf returns expected balance
- mint→getTotalSupply returns expected supply
- transfer→balanceOf returns expected sender/recipient balances
- constructor→getCount, constructor→getOwner end-to-end
- store→retrieve roundtrip (SimpleStorage, matching exact spec form)
- increment→getCount, decrement→getCount (Counter, SafeCounter)
- increment→decrement cancellation (Counter, SafeCounter)
- two_increments adds 2 (Counter)
- withdraw→getBalance, transfer→getBalance (Ledger)
- deposit→withdraw cancellation (Ledger)
- Cross-operation guard interaction: transferOwnership locks out old owner from increment/decrement/re-transfer (OwnedCounter)
- Counter value survives ownership transfer (OwnedCounter isolation)

**Tier 5: Conservation Laws**
- **SimpleToken supply conservation**:
  - Mint exact sum equation: new_sum = old_sum + count(to, addrs) * amount
  - Transfer exact sum conservation: new_sum + count(sender)*amt = old_sum + count(to)*amt
  - Transfer sum bounded: new_sum <= old_sum + count(to)*amount
- **Ledger balance conservation**:
  - Deposit exact sum equation: new_sum = old_sum + count(sender, addrs) * amount
  - Withdraw exact sum equation: new_sum + count(sender, addrs) * amount = old_sum
  - Transfer exact sum conservation: new_sum + count(sender)*amt = old_sum + count(to)*amt
  - Transfer sum preserved for NoDup lists (unique sender & to): new_sum = old_sum
  - Deposit-withdraw sum cancellation: deposit then withdraw preserves total sum

### Key Achievements

- **SimpleStorage**: store/retrieve correctness, state isolation
- **Counter**: Arithmetic operations, composition (increment_twice_adds_two), decrement-at-zero edge case
- **Owned**: Access control, ownership management, guard-protected transferOwnership
- **SimpleToken**: Constructor, mint (owner-guarded), transfer (balance-guarded), all reads, invariant preservation, revert proofs, end-to-end composition, supply conservation equations, **storage isolation (3 types × 3 operations)**
- **OwnedCounter**: Composed ownership + counter patterns, storage isolation (count_preserves_owner, owner_preserves_count, context_preserved, mapping isolation for all 4 operations)
- **Ledger**: Mapping-based deposit/withdraw/transfer, balance guards, **balance conservation laws (deposit/withdraw/transfer sum equations)**
- **SafeCounter**: Checked arithmetic with safeAdd/safeSub, overflow/underflow reverts, bounds preservation
- **Stdlib/Math**: All 4 safe arithmetic operations (25 theorems: safeAdd/safeSub/safeMul/safeDiv with overflow/underflow/div-by-zero detection, identity elements, commutativity, result bounds)
- **Guard Modeling**: `ContractResult` type with explicit success/revert
- **Zero Sorry**: All 277 proofs machine-checked, no axioms

### Proof Architecture

```
edsl/
└── DumbContracts/
    ├── Core.lean (212 lines — ContractResult, require, simp lemmas)
    └── Stdlib/Math.lean — Safe arithmetic (safeAdd, safeSub, safeMul, safeDiv, MAX_UINT256)

examples/lean/
└── DumbContracts/
    ├── Examples/ — 7 contract implementations
    ├── Specs/
    │   ├── SimpleStorage/ (Spec.lean, Invariants.lean)
    │   ├── Counter/ (Spec.lean, Invariants.lean)
    │   ├── Owned/ (Spec.lean, Invariants.lean)
    │   ├── SimpleToken/ (Spec.lean, Invariants.lean)
    │   ├── OwnedCounter/ (Spec.lean, Invariants.lean)
    │   ├── Ledger/ (Spec.lean, Invariants.lean)
    │   └── SafeCounter/ (Spec.lean, Invariants.lean)
    └── Proofs/
        ├── Stdlib/Math.lean (25 theorems — safeAdd/safeSub/safeMul/safeDiv correctness)
        ├── SimpleStorage/Basic.lean (12), Correctness.lean (7)
        ├── Counter/Basic.lean (19), Correctness.lean (10)
        ├── Owned/Basic.lean (18), Correctness.lean (4)
    ├── SimpleToken/Basic.lean (36), Correctness.lean (10), Supply.lean (9), Isolation.lean (9)
    ├── OwnedCounter/Basic.lean (29), Correctness.lean (5), Isolation.lean (14)
    ├── Ledger/Basic.lean (21), Correctness.lean (6), Conservation.lean (13)
    ├── SafeCounter/Basic.lean (22), Correctness.lean (8)
```

### Proof Techniques

- **Full unfolding**: `simp only [op, bind, Bind.bind, Pure.pure, Contract.run, ContractResult.snd, ...]`
- **Private unfold helpers**: Pre-compute exact result state when guards pass
- **Boolean equality conversion**: `beq_iff_eq` converts `(x == y) = true` to `x = y`
- **Slot preservation**: `intro slot h_neq h_eq; exact absurd h_eq h_neq`
- **Safe arithmetic helpers**: `safeAdd_some`/`safeSub_some` with `Nat.not_lt.mpr` for MAX_UINT256
- **Spec derivation**: Prove `meets_spec` first, then derive individual properties from it
- **List sum reasoning**: `Nat.add_assoc`/`Nat.add_comm`/`Nat.add_left_comm` chains (omega can't handle `List.sum` or variable*variable multiplication)
- **countOcc helpers**: Pre-proven `countOcc_cons_eq`/`countOcc_cons_ne` to avoid `if True then 1 else 0` issues
- **unfold + split for isolation**: `unfold supply_storage_isolated; intro h_ne; simp only [...]; split`

### Known Limitations
- Transfer theorems require `sender ≠ to` (self-transfer overwrites sender deduction)
- `ContractResult.fst` requires `[Inhabited α]` constraint
- `supply_bounds_balances` (∀ lists, sum ≤ supply) not preserved by mint/transfer for lists with duplicates — exact sum equations proven instead
- `omega` can't see through `MAX_UINT256` def — use `Nat.not_lt.mpr`
- `omega` can't handle `List.sum` or variable*variable multiplication — use explicit `Nat.add_*` lemma chains
- No Mathlib: `push_neg`, `set`, `ring`, `linarith` unavailable — use `by_cases`, explicit witnesses, `Nat.add_*` chains
- `let` is transparent to `omega` in Lean 4 — named terms don't hide multiplication from omega
- `let s' := ...` in theorem conclusions prevents `unfold` from working on definitions — inline the expression directly

### CI/CD
- **Proof verification**: `.github/workflows/verify.yml` — runs `lake build` + sorry check
- **Docs build**: `.github/workflows/docs.yml` — checks docs-site builds
- **Deployment**: Vercel (automatic on push to main)

## Compilation Status

### Generic Compilation (Completed 2026-02-10) ✅

**Achievement**: Fully automatic compilation from declarative contract specifications to Yul bytecode.

**Status**:
- ✅ All 7 contracts compile automatically without manual IR definitions
- ✅ All 76 Foundry tests pass (100%)
- ✅ All 252 Lean proofs verify (100%)
- ✅ Generated code more optimized than manual translations

**Implementation** (561 lines):
- `Compiler/ContractSpec.lean` (219 lines) — Declarative DSL + automatic IR compiler
- `Compiler/Specs.lean` (238 lines) — All 7 contract specifications
- `Compiler/Selector.lean` (75 lines) — Function selector computation
- `Compiler/Main.lean` (27 lines) — New compilation entry point

**Features**:
- Automatic storage slot inference (assigned from field order)
- Constructor parameter support (bytecode argument loading)
- Function selector management (Solidity keccak256-compatible)
- Type-safe expression/statement DSL
- Code optimization (expression inlining)

**Test Results**:
```
Proofs: 252/252 passing (100%)
Foundry: 76/76 tests passing (100%)
  - 62 EDSL tests (contracts from Examples/)
  - 14 Yul tests (contracts from declarative specs)
```

**Metrics**:
- Manual IR eliminated: 266 lines → 0 lines (-100%)
- Time to add new contract: ~30 min → ~5 min (-83%)
- Code quality: More concise, optimized, type-safe

**Usage**:
```bash
lake build dumbcontracts-compiler    # Build new compiler
lake exe dumbcontracts-compiler      # Generate all contracts
cd compiler/yul && forge test  # Run tests
```

### Differential Testing (Roadmap Item 2 - Completed 2026-02-11) ✅
**Goal**: High confidence that compiled EVM matches verified EDSL semantics.

**Status**:
- ✅ Lean interpreter covers all 7 contracts
- ✅ Random transaction generator supports all contract types
- ✅ 10,000+ random transactions per contract in Foundry (Random10000)
- ✅ Zero mismatches across all contracts

**Test Results**:
```
Foundry differential suites: 7/7 contracts
Random10000 per contract: 70k+ total random txs
Result: 0 mismatches
```

### Future Directions
1. Self-transfer support (model as identity operation)
2. Supply = sum of balances (requires finite address model with NoDup lists)
3. Extended tokens (approval/transferFrom verification)
4. Gas modeling (add consumption tracking to ContractResult)
5. Cross-contract composition proofs
6. Property extraction (252 theorems → 252 Foundry property tests)
7. Compiler verification (formal proof of compilation correctness)
