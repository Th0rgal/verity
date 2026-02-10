# Dumb Contracts Research Status

## Current Iteration: Math Safety Stdlib (2026-02-09)

### Goal
Add a standard library module with checked arithmetic operations to address the arithmetic safety question raised in iteration 2, and demonstrate how to extend the EDSL with stdlib helpers without bloating the core.

### What I'm About to Do
1. Create DumbContracts/Stdlib/Math.lean module with:
   - safeAdd: checked addition that prevents overflow
   - safeSub: checked subtraction that prevents underflow
   - safeMul: checked multiplication (optional, if time permits)
   - safeDiv: checked division (optional, if time permits)
   - Operations return Option type on overflow/underflow

2. Refactor Counter example to use safe arithmetic:
   - Replace bare + and - with safeAdd/safeSub
   - Handle Option results appropriately
   - Demonstrate stdlib usage pattern

3. Ensure all tests still pass

### Why This Approach
Math safety stdlib is the right next step because:
- Have multiple examples doing arithmetic (Counter, OwnedCounter)
- Addresses the semantic difference question from iteration 2 (Lean Nat vs Solidity Uint256)
- Shows how to extend EDSL through stdlib, not core changes
- Demonstrates optional safety (examples can choose safe or unsafe)
- Pattern for future stdlib additions
- No core changes needed - validates extensibility

### Current State
- Previous: OwnedCounter iteration complete (4 examples, 30 tests passing)
- Core: 72 lines, unchanged since iteration 3
- Pattern library: SimpleStorage, Counter, Owned, OwnedCounter
- Ready to add first stdlib module

### Expected Outcomes
- DumbContracts.Stdlib.Math module with checked arithmetic
- Counter refactored to use safe operations
- All tests still passing
- Demonstration of stdlib pattern
- Documentation of safety semantics

### Next Steps After This Iteration
- Add mapping support for more complex data structures
- Consider events for observability
- Potentially add more stdlib helpers based on example needs
