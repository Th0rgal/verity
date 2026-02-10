# Dumb Contracts: EDSL Extension & Advanced Verification Mission

You are a smart contract verification researcher continuing work on the Dumb Contracts project.

## Mission Context

The formal verification mission has been completed with **64 theorems proven** across 4 contract patterns (SimpleStorage, Counter, Owned, SimpleToken). However, **9 theorems remain partially proven** due to limitations in the EDSL.

**Current Status:**
- ✅ 55/64 theorems fully proven (85.9%)
- ⚠️ 9 theorems require guard modeling (mint, transfer, transferOwnership operations)
- ✅ All proofs type-check and build successfully
- ✅ Clean architecture: Specs, Implementations, Proofs separated

## Your Mission: Extend the EDSL for Complete Verification

Pick ONE of these extensions to implement (in order of priority):

### Priority 1: Guard Modeling (HIGHEST IMPACT)
**Problem:** Cannot prove correctness of operations with `require` guards
- 7 SimpleToken theorems (mint, transfer operations)
- 2 Owned theorems (transferOwnership operations)

**What to Do:**
1. **Extend Core.lean** to model `require` behavior:
   ```lean
   -- Current (implicit failure):
   def require (cond : Bool) (msg : String) : Contract Unit := ...

   -- Needed (explicit success/failure):
   inductive ContractResult (α : Type) where
     | success : α → ContractState → ContractResult α
     | revert : String → ContractState → ContractResult α

   def require (cond : Bool) (msg : String) : Contract Unit :=
     fun s => if cond then .success () s else .revert msg s
   ```

2. **Update affected operations** (mint, transfer, onlyOwner) to use new semantics

3. **Complete the 9 partial proofs** by proving:
   - `mint_meets_spec_when_owner` - Mint increases balance and supply when caller is owner
   - `mint_increases_balance` - Mint adds correct amount to recipient
   - `mint_increases_supply` - Mint adds correct amount to total supply
   - `transfer_meets_spec_when_sufficient` - Transfer works when balance sufficient
   - `transfer_preserves_supply_when_sufficient` - Transfer doesn't change total supply
   - `transfer_decreases_sender_balance` - Transfer deducts from sender
   - `transfer_increases_recipient_balance` - Transfer adds to recipient
   - `transferOwnership_meets_spec_when_owner` (Owned) - Ownership transfer works
   - `transferOwnership_changes_owner_when_allowed` (Owned) - Owner changes correctly

4. **Remove axioms** from:
   - `DumbContracts/Proofs/SimpleToken/Basic.lean` (line 129: `require_succeeds` axiom)
   - `DumbContracts/Proofs/Owned/Basic.lean` (similar axiom)

**Success Criteria:**
- ✅ All 9 partial theorems become fully proven
- ✅ No axioms remain (except for trusted core)
- ✅ Build succeeds
- ✅ Update VERIFICATION_ITERATION_5_SUMMARY.md

**Files to Modify:**
- `DumbContracts/Core.lean` - Add ContractResult type and update require
- `DumbContracts/Examples/SimpleToken.lean` - Update mint, transfer if needed
- `DumbContracts/Examples/Owned.lean` - Update transferOwnership if needed
- `DumbContracts/Proofs/SimpleToken/Basic.lean` - Complete 7 proofs, remove axiom
- `DumbContracts/Proofs/Owned/Basic.lean` - Complete 2 proofs, remove axiom

---

### Priority 2: Overflow Handling
**Problem:** Uint256 arithmetic overflow not modeled

**What to Do:**
1. **Add overflow-safe operations** to Core.lean:
   ```lean
   def safeAdd (a b : Uint256) : Contract Uint256 :=
     if a + b < a then revert "Overflow" else pure (a + b)

   def safeSub (a b : Uint256) : Contract Uint256 :=
     if a < b then revert "Underflow" else pure (a - b)

   def safeMul (a b : Uint256) : Contract Uint256 :=
     if b ≠ 0 ∧ a > UInt256.max / b then revert "Overflow"
     else pure (a * b)
   ```

2. **Update contracts** to use safe operations:
   - Counter: `increment`, `decrement`
   - SimpleToken: `mint`, `transfer`

3. **Prove overflow safety**:
   - `safeAdd_no_overflow` - Result is valid or reverts
   - `safeSub_no_underflow` - Result is valid or reverts
   - `safeMul_no_overflow` - Result is valid or reverts

4. **Update existing proofs** to account for overflow checks

**Success Criteria:**
- ✅ All arithmetic operations use safe variants
- ✅ Overflow safety theorems proven
- ✅ Existing 64 theorems still pass
- ✅ Update VERIFICATION_ITERATION_6_SUMMARY.md

---

### Priority 3: Complex Invariant Infrastructure
**Problem:** Cannot prove `totalSupply = Σ balances[addr]` invariant

**What to Do:**
1. **Add finite address model** to Specs/SimpleToken/Invariants.lean:
   ```lean
   -- Track set of addresses with non-zero balances
   def activeAddresses (s : ContractState) : Finset Address := sorry

   -- Sum over active addresses only
   def sumBalances (s : ContractState) : Uint256 :=
     (activeAddresses s).sum (fun addr => s.storageMap 1 addr)

   -- The key invariant
   def supply_equals_sum (s : ContractState) : Prop :=
     s.storage 2 = sumBalances s
   ```

2. **Prove invariant initialization**:
   - `constructor_establishes_invariant` - Constructor sets supply = 0, no balances

3. **Prove invariant preservation**:
   - `mint_preserves_invariant` - Mint adds to both supply and sum
   - `transfer_preserves_invariant` - Transfer moves balance, sum unchanged

4. **Add to WellFormedState**:
   ```lean
   structure WellFormedState (s : ContractState) : Prop where
     sender_nonempty : s.sender ≠ ""
     contract_nonempty : s.thisAddress ≠ ""
     owner_nonempty : s.storageAddr 0 ≠ ""
     supply_invariant : supply_equals_sum s  -- NEW
   ```

**Success Criteria:**
- ✅ Supply invariant formalized
- ✅ Invariant proven for constructor
- ✅ Invariant preservation proven (requires guard modeling first!)
- ✅ Update VERIFICATION_ITERATION_7_SUMMARY.md

**Dependencies:**
- Requires Priority 1 (guard modeling) to be completed first

---

### Priority 4: Access Control Enforcement
**Problem:** Cannot prove only owner can mint/transfer ownership

**What to Do:**
1. **Formalize access control properties** in Specs/SimpleToken/Invariants.lean:
   ```lean
   -- Only owner can successfully call mint
   def mint_requires_owner (s s' : ContractState) (to : Address) (amount : Uint256) : Prop :=
     (mint to amount).run s = .success _ s' → s.sender = s.storageAddr 0

   -- Non-owner calls to mint revert
   def mint_rejects_non_owner (s : ContractState) (to : Address) (amount : Uint256) : Prop :=
     s.sender ≠ s.storageAddr 0 →
     ∃ msg, (mint to amount).run s = .revert msg s
   ```

2. **Prove access control theorems**:
   - `mint_enforces_ownership` - Only owner can mint
   - `transferOwnership_enforces_ownership` - Only owner can transfer

3. **Add authorization proofs**:
   - `onlyOwner_authorizes_owner` - onlyOwner succeeds for owner
   - `onlyOwner_rejects_others` - onlyOwner reverts for non-owners

**Success Criteria:**
- ✅ Access control properties formalized
- ✅ Enforcement theorems proven
- ✅ Update VERIFICATION_ITERATION_8_SUMMARY.md

**Dependencies:**
- Requires Priority 1 (guard modeling) to be completed first

---

## Implementation Strategy

### Step 1: Pick Your Priority
Choose ONE extension to work on (recommend Priority 1: Guard Modeling)

### Step 2: Read Existing Work
- Read all 4 VERIFICATION_ITERATION_*_SUMMARY.md files
- Understand current proof patterns
- Review files with `sorry` markers:
  - `DumbContracts/Proofs/SimpleToken/Basic.lean` (7 sorry, 1 axiom)
  - `DumbContracts/Proofs/Owned/Basic.lean` (2 sorry, 1 axiom)

### Step 3: Extend the EDSL
- Modify `DumbContracts/Core.lean` carefully
- Test with simple examples first
- Ensure backward compatibility with existing proofs

### Step 4: Update Proofs
- Replace `sorry` with real proofs
- Remove axioms
- Verify build succeeds

### Step 5: Document
- Create VERIFICATION_ITERATION_N_SUMMARY.md
- Update STATUS.md
- Commit with clear message

---

## Constraints

**DO:**
- ✅ Maintain clean separation (Specs/Implementations/Proofs)
- ✅ Keep backward compatibility with existing 55 proven theorems
- ✅ Document all design decisions
- ✅ Run `lake build` after every change
- ✅ Use descriptive theorem names

**DON'T:**
- ❌ Break existing proofs
- ❌ Mix verification code with implementations
- ❌ Leave undocumented axioms
- ❌ Make monolithic proof files

---

## Success Metrics

### For Priority 1 (Guard Modeling):
- 9 → 0 theorems with sorry
- 64 → 64 fully proven theorems (100%)
- 2 axioms removed
- Build time: ~5-6 seconds (slight increase expected)

### For Priority 2 (Overflow):
- 64 → 70+ theorems (add 6+ overflow safety theorems)
- All arithmetic operations proven safe
- Zero overflow vulnerabilities

### For Priority 3 (Invariants):
- Add 3+ complex invariant theorems
- Prove supply conservation across all operations
- Establish invariant preservation patterns

### For Priority 4 (Access Control):
- Add 4+ access control enforcement theorems
- Prove authorization works correctly
- Prove unauthorized calls revert

---

## Example: Guard Modeling Extension (Priority 1)

Here's a concrete example of what to implement:

```lean
-- In DumbContracts/Core.lean

inductive ContractResult (α : Type) where
  | success : α → ContractState → ContractResult α
  | revert : String → ContractState → ContractResult α

abbrev Contract (α : Type) := ContractState → ContractResult α

def require (cond : Bool) (msg : String) : Contract Unit :=
  fun s => if cond
           then ContractResult.success () s
           else ContractResult.revert msg s

-- Update bind to handle revert
def bind {α β : Type} (ma : Contract α) (f : α → Contract β) : Contract β :=
  fun s => match ma s with
    | .success a s' => f a s'
    | .revert msg s' => .revert msg s'
```

Then in proofs:
```lean
-- In DumbContracts/Proofs/SimpleToken/Basic.lean

theorem mint_meets_spec_when_owner (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) :
  ∃ s', (mint to amount).run s = .success () s' ∧
        mint_spec to amount s s' := by
  simp [mint, onlyOwner, isOwner, msgSender, require, h_owner]
  -- Now we can reason about the success case explicitly
  sorry -- Complete this proof
```

---

## Resources

**Existing Verification Work:**
- 4 complete verification iteration summaries
- 64 proven theorems (55 fully, 9 partial)
- Clean proof architecture established
- Reusable lemma patterns documented

**Files to Reference:**
- `DumbContracts/Core.lean` - EDSL core (82 lines, minimal)
- `DumbContracts/Specs/*/` - Formal specifications
- `DumbContracts/Proofs/*/` - Existing proof patterns
- `VERIFICATION_ITERATION_*_SUMMARY.md` - Detailed documentation

**Key Proof Tactics:**
- `simp` - Simplification and unfolding
- `exact` - Direct proof application
- `constructor` - Building structures
- `intro` + `contradiction` - Impossible cases
- `have` + `rw` - Intermediate steps
- `obtain` - Destructuring

---

## Git Workflow

1. **Create branch**: `git checkout -b verification-guards` (or similar)
2. **Commit incrementally**: After each proof completed
3. **Clear messages**: "Add guard modeling to require" / "Prove mint_meets_spec_when_owner"
4. **Push regularly**: Keep backup of work
5. **Merge when complete**: After all tests pass and documentation updated

---

## Expected Timeline

### Priority 1 (Guard Modeling): ~4-6 hours
- 1h: Design and implement ContractResult type
- 1h: Update Core.lean and affected contracts
- 2-3h: Complete 9 partial proofs
- 1h: Documentation and testing

### Priority 2 (Overflow): ~3-4 hours
- 1h: Implement safe arithmetic operations
- 1-2h: Prove overflow safety theorems
- 1h: Update existing proofs

### Priority 3 (Invariants): ~5-7 hours
- 2h: Design finite address model
- 2-3h: Prove invariant initialization and preservation
- 1-2h: Integration with existing proofs

### Priority 4 (Access Control): ~2-3 hours
- 1h: Formalize access control properties
- 1-2h: Prove enforcement theorems

---

## Questions to Consider

1. **ContractResult Design**: Should revert preserve or discard state changes?
2. **Backward Compatibility**: How to update existing 55 proofs with minimal changes?
3. **Finite Model**: How to track active addresses efficiently?
4. **Overflow**: Should safe operations be default or opt-in?
5. **Testing**: Should we add runtime tests for new features?

---

## Success Criteria Summary

**You succeed when:**
1. ✅ Choose ONE priority and implement it fully
2. ✅ All new theorems proven (no sorry, no new axioms)
3. ✅ Existing 55 theorems still pass
4. ✅ Build succeeds (`lake build`)
5. ✅ Documentation complete (new VERIFICATION_ITERATION_N_SUMMARY.md)
6. ✅ STATUS.md updated
7. ✅ Work committed and pushed

**Bonus Success:**
- ✅ Complete multiple priorities
- ✅ Add new contracts with complete verification
- ✅ Improve proof automation with custom tactics

---

## Final Notes

The formal verification work so far has been excellent - 85.9% of theorems fully proven with clean architecture. Your mission is to **complete the remaining 14.1%** by extending the EDSL's capabilities.

**Priority 1 (Guard Modeling) is the highest impact** - it unblocks 9 theorems and enables all future work.

Focus on **incremental progress** - get one proof working, then apply the pattern to others. The foundation is solid, you're adding the missing pieces.

Good luck! 🚀

---

**Mission Status Reference:**
- Current: 64 theorems (55 fully proven, 9 with sorry)
- Target: 64 theorems (64 fully proven, 0 sorry) for Priority 1
- Target: 70+ theorems (all fully proven) for Priority 2-4

**Next Agent: Start with Priority 1 (Guard Modeling)**
