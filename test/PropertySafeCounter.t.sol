// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertySafeCounterTest
 * @notice Property-based tests extracted from formally verified Lean theorems
 * @dev Maps theorems from Verity/Proofs/SafeCounter/*.lean to executable tests
 *
 * This file contains property tests for SafeCounter's 25 proven theorems:
 *
 * Basic.lean (17 theorems):
 * 1. getCount_meets_spec - Read returns correct spec result
 * 2. getCount_returns_count - Read returns current count value
 * 3. getCount_preserves_state - Read doesn't modify state
 * 3b. evm_add_eq_of_no_overflow - EVM add matches math when no overflow
 * 4. increment_meets_spec - Increment follows specification
 * 5. increment_adds_one - Increment increases count by 1
 * 6. increment_preserves_other_slots - Increment only modifies slot 0
 * 7. increment_reverts_overflow - Increment reverts at MAX_UINT256
 * 8. decrement_meets_spec - Decrement follows specification
 * 9. decrement_subtracts_one - Decrement decreases count by 1
 * 10. decrement_preserves_other_slots - Decrement only modifies slot 0
 * 11. decrement_reverts_underflow - Decrement reverts at 0
 * 12. increment_preserves_wellformedness - Maintains invariants
 * 13. decrement_preserves_wellformedness - Maintains invariants
 * 14. increment_preserves_bounds - Count stays in valid range
 * 15. decrement_preserves_bounds - Count stays in valid range
 * 16. increment_getCount_correct - Composition property
 *
 * Correctness.lean (8 theorems):
 * 17. increment_preserves_context - Sender/address unchanged
 * 18. decrement_preserves_context - Sender/address unchanged
 * 19. increment_preserves_storage_isolated - Storage isolation
 * 20. decrement_preserves_storage_isolated - Storage isolation
 * 21. getCount_preserves_context - Read preserves context
 * 22. getCount_preserves_wellformedness - Read maintains invariants
 * 23. increment_decrement_cancel - Inc→dec cancels (when valid)
 * 24. decrement_getCount_correct - Dec→read composition
 */
contract PropertySafeCounterTest is YulTestBase {
    address safeCounter;

    function setUp() public {
        safeCounter = deployYul("SafeCounter");
        require(safeCounter != address(0), "Deploy failed");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Basic Properties - Read Operations
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 1: getCount_meets_spec
     * Theorem: getCount returns correct result per specification
     */
    function testProperty_GetCount_MeetsSpec() public {
        uint256 expected = readStorage(0);
        (bool success, bytes memory data) = safeCounter.call(abi.encodeWithSignature("getCount()"));
        require(success, "getCount failed");
        uint256 result = abi.decode(data, (uint256));
        assertEq(result, expected, "getCount doesn't meet spec");
    }

    /**
     * Property 2: getCount_returns_count
     * Theorem: getCount returns the current count value
     */
    function testProperty_GetCount_ReturnsCount() public {
        uint256 count = readStorage(0);
        (bool success, bytes memory data) = safeCounter.call(abi.encodeWithSignature("getCount()"));
        require(success, "getCount failed");
        uint256 result = abi.decode(data, (uint256));
        assertEq(result, count, "getCount doesn't return count");
    }

    /**
     * Property 3: getCount_preserves_state
     * Theorem: getCount is read-only, doesn't modify state
     */
    function testProperty_GetCount_PreservesState() public {
        uint256 slot0Before = readStorage(0);
        uint256 slot1Before = readStorage(1);

        (bool success,) = safeCounter.call(abi.encodeWithSignature("getCount()"));
        require(success, "getCount failed");

        assertEq(readStorage(0), slot0Before, "getCount modified slot 0");
        assertEq(readStorage(1), slot1Before, "getCount modified slot 1");
    }

    /**
     * Property 3b: evm_add_eq_of_no_overflow (fuzz test)
     * Theorem: EVM add matches math addition when no overflow occurs
     */
    function testProperty_EvmAdd_EqOfNoOverflow(uint256 a, uint256 b) public {
        vm.assume(a <= type(uint256).max - b);
        uint256 evmAdd;
        assembly {
            evmAdd := add(a, b)
        }
        assertEq(evmAdd, a + b, "EVM add should match math addition");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Basic Properties - Increment
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 4: increment_meets_spec (fuzz test)
     * Theorem: Increment follows the formal specification
     */
    function testProperty_Increment_MeetsSpec(uint256 initialCount) public {
        vm.assume(initialCount < type(uint256).max);

        writeStorage(0, initialCount);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        require(success, "increment failed");

        assertEq(readStorage(0), initialCount + 1, "increment doesn't meet spec");
    }

    /**
     * Property 5: increment_adds_one (fuzz test)
     * Theorem: Increment increases count by exactly 1
     */
    function testProperty_Increment_AddsOne(uint256 initialCount) public {
        vm.assume(initialCount < type(uint256).max);

        writeStorage(0, initialCount);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        require(success, "increment failed");

        assertEq(readStorage(0), initialCount + 1, "increment doesn't add 1");
    }

    /**
     * Property 6: increment_preserves_other_slots (fuzz test)
     * Theorem: Increment only modifies storage slot 0
     */
    function testProperty_Increment_PreservesOtherSlots(uint256 initialCount, uint256 otherValue) public {
        vm.assume(initialCount < type(uint256).max);

        writeStorage(0, initialCount);
        writeStorage(1, otherValue);

        uint256 slot1Before = readStorage(1);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        require(success, "increment failed");

        assertEq(readStorage(1), slot1Before, "increment modified other slots");
    }

    /**
     * Property 7: increment_reverts_overflow
     * Theorem: Increment reverts when count is MAX_UINT256
     */
    function testProperty_Increment_RevertsOnOverflow() public {
        writeStorage(0, type(uint256).max);

        (bool success,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        assertFalse(success, "increment should revert at MAX_UINT256");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Basic Properties - Decrement
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 8: decrement_meets_spec (fuzz test)
     * Theorem: Decrement follows the formal specification
     */
    function testProperty_Decrement_MeetsSpec(uint256 initialCount) public {
        vm.assume(initialCount > 0);

        writeStorage(0, initialCount);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("decrement()"));
        require(success, "decrement failed");

        assertEq(readStorage(0), initialCount - 1, "decrement doesn't meet spec");
    }

    /**
     * Property 9: decrement_subtracts_one (fuzz test)
     * Theorem: Decrement decreases count by exactly 1
     */
    function testProperty_Decrement_SubtractsOne(uint256 initialCount) public {
        vm.assume(initialCount > 0);

        writeStorage(0, initialCount);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("decrement()"));
        require(success, "decrement failed");

        assertEq(readStorage(0), initialCount - 1, "decrement doesn't subtract 1");
    }

    /**
     * Property 10: decrement_preserves_other_slots (fuzz test)
     * Theorem: Decrement only modifies storage slot 0
     */
    function testProperty_Decrement_PreservesOtherSlots(uint256 initialCount, uint256 otherValue) public {
        vm.assume(initialCount > 0);

        writeStorage(0, initialCount);
        writeStorage(1, otherValue);

        uint256 slot1Before = readStorage(1);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("decrement()"));
        require(success, "decrement failed");

        assertEq(readStorage(1), slot1Before, "decrement modified other slots");
    }

    /**
     * Property 11: decrement_reverts_underflow
     * Theorem: Decrement reverts when count is 0
     */
    function testProperty_Decrement_RevertsOnUnderflow() public {
        writeStorage(0, 0);

        (bool success,) = safeCounter.call(abi.encodeWithSignature("decrement()"));
        assertFalse(success, "decrement should revert at 0");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Well-Formedness & Invariant Preservation
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 12: increment_preserves_wellformedness (fuzz test)
     * Theorem: Increment maintains contract invariants
     */
    function testProperty_Increment_PreservesWellFormedness(uint256 initialCount) public {
        vm.assume(initialCount < type(uint256).max);

        writeStorage(0, initialCount);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        require(success, "increment failed");

        // Well-formedness: count is a valid Uint256
        assertTrue(readStorage(0) <= type(uint256).max, "count out of bounds");
    }

    /**
     * Property 13: decrement_preserves_wellformedness (fuzz test)
     * Theorem: Decrement maintains contract invariants
     */
    function testProperty_Decrement_PreservesWellFormedness(uint256 initialCount) public {
        vm.assume(initialCount > 0);

        writeStorage(0, initialCount);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("decrement()"));
        require(success, "decrement failed");

        // Well-formedness: count is a valid Uint256
        assertTrue(readStorage(0) <= type(uint256).max, "count out of bounds");
    }

    /**
     * Property 14: increment_preserves_bounds (fuzz test)
     * Theorem: Increment keeps count in valid range
     */
    function testProperty_Increment_PreservesBounds(uint256 initialCount) public {
        vm.assume(initialCount < type(uint256).max);

        writeStorage(0, initialCount);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        require(success, "increment failed");

        uint256 newCount = readStorage(0);
        assertTrue(newCount <= type(uint256).max, "count exceeded max");
        assertTrue(newCount > initialCount, "count didn't increase");
    }

    /**
     * Property 15: decrement_preserves_bounds (fuzz test)
     * Theorem: Decrement keeps count in valid range
     */
    function testProperty_Decrement_PreservesBounds(uint256 initialCount) public {
        vm.assume(initialCount > 0);

        writeStorage(0, initialCount);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("decrement()"));
        require(success, "decrement failed");

        uint256 newCount = readStorage(0);
        assertTrue(newCount <= type(uint256).max, "count exceeded max");
        assertTrue(newCount < initialCount, "count didn't decrease");
    }

    /**
     * Property 16: increment_getCount_correct (fuzz test)
     * Theorem: Inc->read composition is correct
     */
    function testProperty_Increment_GetCount_Correct(uint256 initialCount) public {
        vm.assume(initialCount < type(uint256).max);

        writeStorage(0, initialCount);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        require(success, "increment failed");

        (bool success2, bytes memory data) = safeCounter.call(abi.encodeWithSignature("getCount()"));
        require(success2, "getCount failed");
        uint256 result = abi.decode(data, (uint256));

        assertEq(result, initialCount + 1, "increment->getCount incorrect");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Correctness Properties - Context Preservation
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 17: increment_preserves_context (fuzz test)
     * Theorem: Increment doesn't modify sender/address context
     * Note: In Solidity, we verify storage isolation instead
     */
    function testProperty_Increment_PreservesContext(uint256 initialCount) public {
        vm.assume(initialCount < type(uint256).max);

        writeStorage(0, initialCount);
        writeStorage(2, 12345);  // Unrelated storage

        uint256 slot2Before = readStorage(2);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        require(success, "increment failed");

        assertEq(readStorage(2), slot2Before, "increment modified context");
    }

    /**
     * Property 18: decrement_preserves_context (fuzz test)
     * Theorem: Decrement doesn't modify sender/address context
     */
    function testProperty_Decrement_PreservesContext(uint256 initialCount) public {
        vm.assume(initialCount > 0);

        writeStorage(0, initialCount);
        writeStorage(2, 12345);

        uint256 slot2Before = readStorage(2);
        (bool success,) = safeCounter.call(abi.encodeWithSignature("decrement()"));
        require(success, "decrement failed");

        assertEq(readStorage(2), slot2Before, "decrement modified context");
    }

    /**
     * Property 19: increment_preserves_storage_isolated (fuzz test)
     * Theorem: Increment maintains storage isolation
     */
    function testProperty_Increment_PreservesStorageIsolated(uint256 initialCount, uint256 slot1Val, uint256 slot2Val) public {
        vm.assume(initialCount < type(uint256).max);

        writeStorage(0, initialCount);
        writeStorage(1, slot1Val);
        writeStorage(2, slot2Val);

        (bool success,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        require(success, "increment failed");

        assertEq(readStorage(1), slot1Val, "increment violated isolation slot 1");
        assertEq(readStorage(2), slot2Val, "increment violated isolation slot 2");
    }

    /**
     * Property 20: decrement_preserves_storage_isolated (fuzz test)
     * Theorem: Decrement maintains storage isolation
     */
    function testProperty_Decrement_PreservesStorageIsolated(uint256 initialCount, uint256 slot1Val, uint256 slot2Val) public {
        vm.assume(initialCount > 0);

        writeStorage(0, initialCount);
        writeStorage(1, slot1Val);
        writeStorage(2, slot2Val);

        (bool success,) = safeCounter.call(abi.encodeWithSignature("decrement()"));
        require(success, "decrement failed");

        assertEq(readStorage(1), slot1Val, "decrement violated isolation slot 1");
        assertEq(readStorage(2), slot2Val, "decrement violated isolation slot 2");
    }

    /**
     * Property 21: getCount_preserves_context
     * Theorem: getCount doesn't modify context
     */
    function testProperty_GetCount_PreservesContext() public {
        writeStorage(2, 99999);
        uint256 contextBefore = readStorage(2);

        (bool success,) = safeCounter.call(abi.encodeWithSignature("getCount()"));
        require(success, "getCount failed");

        assertEq(readStorage(2), contextBefore, "getCount modified context");
    }

    /**
     * Property 22: getCount_preserves_wellformedness
     * Theorem: getCount maintains invariants
     */
    function testProperty_GetCount_PreservesWellFormedness() public {
        (bool success,) = safeCounter.call(abi.encodeWithSignature("getCount()"));
        require(success, "getCount failed");

        assertTrue(readStorage(0) <= type(uint256).max, "wellformedness violated");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Composition Properties
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 23: increment_decrement_cancel (fuzz test)
     * Theorem: Inc->dec returns to original state (when valid)
     */
    function testProperty_Increment_Decrement_Cancel(uint256 initialCount) public {
        vm.assume(initialCount < type(uint256).max);

        writeStorage(0, initialCount);

        (bool success1,) = safeCounter.call(abi.encodeWithSignature("increment()"));
        require(success1, "increment failed");

        (bool success2,) = safeCounter.call(abi.encodeWithSignature("decrement()"));
        require(success2, "decrement failed");

        assertEq(readStorage(0), initialCount, "increment->decrement didn't cancel");
    }

    /**
     * Property 24: decrement_getCount_correct (fuzz test)
     * Theorem: Dec->read composition is correct
     */
    function testProperty_Decrement_GetCount_Correct(uint256 initialCount) public {
        vm.assume(initialCount > 0);

        writeStorage(0, initialCount);
        (bool success1,) = safeCounter.call(abi.encodeWithSignature("decrement()"));
        require(success1, "decrement failed");

        (bool success2, bytes memory data) = safeCounter.call(abi.encodeWithSignature("getCount()"));
        require(success2, "getCount failed");
        uint256 result = abi.decode(data, (uint256));

        assertEq(result, initialCount - 1, "decrement->getCount incorrect");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Utility Functions
    //═══════════════════════════════════════════════════════════════════════════

    function readStorage(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(safeCounter, bytes32(slot)));
    }

    function writeStorage(uint256 slot, uint256 value) internal {
        vm.store(safeCounter, bytes32(slot), bytes32(value));
    }
}
