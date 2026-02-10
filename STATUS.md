# Dumb Contracts Research Status

## Current State: 230 Theorems, 7/7 Contracts Verified (2026-02-10)

### Summary
**Full Verification Achieved**: All 230 theorems proven with zero `sorry`, zero axioms, zero errors. Guard modeling via `ContractResult` type enables complete verification of `require`-guarded operations. Every contract now has both Basic.lean and Correctness.lean proof files. Supply conservation proofs and safe arithmetic correctness proofs extend verification depth.

All 7 contract patterns verified at 100%:
- SimpleStorage (19 theorems: 12 basic + 7 correctness) — 100% proven
- Counter (29 theorems: 19 basic + 10 correctness) — 100% proven
- Owned (22 theorems: 18 basic + 4 correctness) — 100% proven
- SimpleToken (52 theorems: 33 basic + 10 correctness + 9 supply conservation) — 100% proven
- OwnedCounter (31 theorems: 26 basic + 5 correctness) — 100% proven
- Ledger (24 theorems: 18 basic + 6 correctness) — 100% proven
- SafeCounter (24 theorems: 16 basic + 8 correctness) — 100% proven

Additional:
- Stdlib/Math (14 theorems: safeMul + safeDiv correctness) — 100% proven
- Private helper lemmas (15 across all files) — 100% proven

**Total: 230/230 theorems fully proven (100%) — zero sorry, zero axioms**

### Verification Tiers Achieved

**Tier 1: Safety Properties**
- Balance non-negativity (implicit via Nat)
- Access control respected (mint reverts when not owner)
- No overdrafts (transfer reverts with insufficient balance)
- Overflow/underflow protection (SafeCounter revert proofs)
- Safe arithmetic bounds (safeMul result bounded, safeDiv result bounded)

**Tier 2: Functional Correctness**
- Transfer moves exact amount (sender decreases, recipient increases)
- Mint increases supply correctly
- All state transitions match specifications
- Constructor initializes correctly
- safeMul/safeDiv return correct results or none on overflow/div-by-zero
- Decrement at zero saturates to zero (Counter edge case)

**Tier 3: Invariants**
- WellFormedState preserved by all operations (constructor, mint, transfer, transferOwnership, reads)
- Owner stability (mint and transfer don't change owner)
- Storage isolation proven standalone for all contracts (SimpleStorage, Counter, SafeCounter)
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

**Tier 5: Supply Conservation**
- Mint exact sum equation: new_sum = old_sum + count(to, addrs) * amount
- Transfer exact sum conservation: new_sum + count(sender)*amt = old_sum + count(to)*amt
- Transfer sum bounded: new_sum <= old_sum + count(to)*amount

### Key Achievements

- **SimpleStorage**: store/retrieve correctness, state isolation
- **Counter**: Arithmetic operations, composition (increment_twice_adds_two), decrement-at-zero edge case
- **Owned**: Access control, ownership management, guard-protected transferOwnership
- **SimpleToken**: Constructor, mint (owner-guarded), transfer (balance-guarded), all reads, invariant preservation, revert proofs, end-to-end composition, supply conservation equations
- **OwnedCounter**: Composed ownership + counter patterns, storage isolation
- **Ledger**: Mapping-based deposit/withdraw/transfer, balance guards
- **SafeCounter**: Checked arithmetic with safeAdd/safeSub, overflow/underflow reverts, bounds preservation
- **Stdlib/Math**: safeMul/safeDiv correctness (14 theorems: overflow detection, identity elements, commutativity, result bounds)
- **Guard Modeling**: `ContractResult` type with explicit success/revert
- **Zero Sorry**: All 230 proofs machine-checked, no axioms

### Proof Architecture

```
DumbContracts/
├── Core.lean (212 lines — ContractResult, require, simp lemmas)
├── Stdlib/Math.lean — Safe arithmetic (safeAdd, safeSub, safeMul, safeDiv, MAX_UINT256)
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
    ├── Stdlib/Math.lean (14 theorems — safeMul/safeDiv correctness)
    ├── SimpleStorage/Basic.lean (12 theorems)
    ├── SimpleStorage/Correctness.lean (7 theorems)
    ├── Counter/Basic.lean (19 theorems)
    ├── Counter/Correctness.lean (10 theorems)
    ├── Owned/Basic.lean (18 theorems)
    ├── Owned/Correctness.lean (4 theorems)
    ├── SimpleToken/Basic.lean (33 theorems)
    ├── SimpleToken/Correctness.lean (10 theorems)
    ├── SimpleToken/Supply.lean (9 theorems — supply conservation)
    ├── OwnedCounter/Basic.lean (26 theorems)
    ├── OwnedCounter/Correctness.lean (5 theorems)
    ├── Ledger/Basic.lean (18 theorems)
    ├── Ledger/Correctness.lean (6 theorems)
    ├── SafeCounter/Basic.lean (16 theorems)
    └── SafeCounter/Correctness.lean (8 theorems)
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

### Known Limitations
- Transfer theorems require `sender ≠ to` (self-transfer overwrites sender deduction)
- `ContractResult.fst` requires `[Inhabited α]` constraint
- `supply_bounds_balances` (∀ lists, sum ≤ supply) not preserved by mint/transfer for lists with duplicates — exact sum equations proven instead
- `omega` can't see through `MAX_UINT256` def — use `Nat.not_lt.mpr`
- `omega` can't handle `List.sum` or variable*variable multiplication — use explicit `Nat.add_*` lemma chains
- No Mathlib: `push_neg`, `set`, `ring`, `linarith` unavailable — use `by_cases`, explicit witnesses, `Nat.add_*` chains
- `let` is transparent to `omega` in Lean 4 — named terms don't hide multiplication from omega

### CI/CD
- **Proof verification**: `.github/workflows/verify.yml` — runs `lake build` + sorry check
- **Docs build**: `.github/workflows/docs.yml` — checks docs-site builds
- **Deployment**: Vercel (automatic on push to main)

### Future Directions
1. Self-transfer support (model as identity operation)
2. Supply = sum of balances (requires finite address model with NoDup lists)
3. Extended tokens (approval/transferFrom verification)
4. Gas modeling (add consumption tracking to ContractResult)
5. Cross-contract composition proofs
