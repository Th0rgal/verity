# Dumb Contracts Research Status

## Current Iteration: Counter Pattern (2026-02-09)

### Goal
Add a Counter contract to demonstrate arithmetic operations and identify opportunities for math safety helpers.

### What I'm About to Do
1. Create a Counter example contract that:
   - Stores a counter value
   - Implements increment function
   - Implements decrement function
   - Implements a getter function

2. Create Solidity reference implementation and Foundry tests

3. Identify if we need math safety helpers (checked arithmetic)

### Why This Approach
The Counter pattern is a natural next step because:
- It's the second-most common smart contract pattern (after storage)
- It introduces arithmetic operations (add/subtract)
- It will reveal whether we need overflow protection
- It demonstrates how the EDSL handles stateful updates
- It's simple enough to keep the iteration focused

### Current State
- Previous: Bootstrap iteration complete (SimpleStorage working)
- Now: Starting Counter pattern iteration
- Ready to implement arithmetic operations

### Expected Outcomes
- Counter contract demonstrating increment/decrement
- Insight into whether we need checked arithmetic
- Growing library of example contracts
- Continued validation of EDSL design

### Next Steps After This Iteration
- Potentially add math safety stdlib if Counter reveals the need
- Add ownership pattern (msg.sender checks)
- Consider events for observability
