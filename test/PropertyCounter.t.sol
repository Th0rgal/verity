// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyCounterTest
 * @notice Property-based tests extracted from formally verified Lean theorems
 * @dev Maps theorems from Verity/Proofs/Counter/Correctness.lean to executable tests
 *
 * This file contains 10 property tests corresponding to 10 proven theorems:
 * 1. increment_state_preserved_except_count
 * 2. decrement_state_preserved_except_count
 * 3. getCount_state_preserved
 * 4. increment_getCount_meets_spec
 * 5. decrement_getCount_meets_spec
 * 6. two_increments_meets_spec
 * 7. increment_decrement_meets_cancel
 * 8. getCount_preserves_wellformedness
 * 9. decrement_getCount_correct
 * 10. decrement_at_zero_wraps_max
 */
contract PropertyCounterTest is YulTestBase {
    address counter;

    function setUp() public {
        // Deploy Counter from Yul using YulTestBase helper
        counter = deployYul("Counter");
        require(counter != address(0), "Deploy failed");
    }

    /**
     * Property 1: increment_state_preserved_except_count
     * Property: increment_adds_one
     * Property: increment_preserves_wellformedness
     * Property: setStorage_preserves_other_slots
     * Theorem: Increment only modifies storage slot 0 (count)
     * All other state (sender, this, msgValue, blockTimestamp) unchanged
     */
    function testProperty_Increment_OnlyModifiesCount() public {
        // Setup: Read all storage slots before
        uint256 countBefore = readStorage(0);
        uint256 slot1Before = readStorage(1);
        uint256 slot2Before = readStorage(2);

        // Action: Increment
        (bool success,) = counter.call(abi.encodeWithSignature("increment()"));
        require(success, "increment failed");

        // Assert: Only slot 0 changed
        uint256 countAfter = readStorage(0);
        uint256 slot1After = readStorage(1);
        uint256 slot2After = readStorage(2);

        assertEq(countAfter, countBefore + 1, "Count should increment by 1");
        assertEq(slot1After, slot1Before, "Slot 1 should be unchanged");
        assertEq(slot2After, slot2Before, "Slot 2 should be unchanged");
    }

    /**
     * Property 2: decrement_state_preserved_except_count
     * Property: decrement_subtracts_one
     * Property: decrement_preserves_wellformedness
     * Theorem: Decrement only modifies storage slot 0 (count)
     */
    function testProperty_Decrement_OnlyModifiesCount() public {
        // Setup: Increment to have non-zero count
        (bool success,) = counter.call(abi.encodeWithSignature("increment()"));
        require(success);

        uint256 countBefore = readStorage(0);
        uint256 slot1Before = readStorage(1);
        uint256 slot2Before = readStorage(2);

        // Action: Decrement
        (success,) = counter.call(abi.encodeWithSignature("decrement()"));
        require(success);

        // Assert: Only slot 0 changed
        uint256 countAfter = readStorage(0);
        assertEq(countAfter, countBefore - 1, "Count should decrement by 1");
        assertEq(readStorage(1), slot1Before, "Slot 1 unchanged");
        assertEq(readStorage(2), slot2Before, "Slot 2 unchanged");
    }

    /**
     * Property 3: getCount_state_preserved
     * Property: getCount_preserves_state
     * Property: getCount_reads_count_value
     * Theorem: getCount is read-only, preserves all state
     */
    function testProperty_GetCount_PreservesState() public {
        // Setup
        uint256 slot0Before = readStorage(0);
        uint256 slot1Before = readStorage(1);
        uint256 slot2Before = readStorage(2);

        // Action: Call getCount
        (, bytes memory data) = counter.call(abi.encodeWithSignature("getCount()"));
        uint256 returnedCount = abi.decode(data, (uint256));

        // Assert: All storage unchanged
        assertEq(readStorage(0), slot0Before, "Slot 0 unchanged");
        assertEq(readStorage(1), slot1Before, "Slot 1 unchanged");
        assertEq(readStorage(2), slot2Before, "Slot 2 unchanged");
        assertEq(returnedCount, slot0Before, "Returned count matches storage");
    }

    /**
     * Property 4: increment_getCount_meets_spec
     * Property: increment_getCount_correct
     * Property: increment_meets_spec
     * Theorem: Increment followed by getCount returns count + 1
     */
    function testProperty_Increment_GetCount_ReturnsIncremented() public {
        uint256 countBefore = readStorage(0);

        // Action: Increment
        (bool success,) = counter.call(abi.encodeWithSignature("increment()"));
        require(success);

        // Action: GetCount
        (, bytes memory data) = counter.call(abi.encodeWithSignature("getCount()"));
        uint256 countAfter = abi.decode(data, (uint256));

        // Assert
        assertEq(countAfter, countBefore + 1, "getCount after increment = initial + 1");
    }

    /**
     * Property 5: decrement_getCount_meets_spec
     * Property: getCount_meets_spec
     * Property: decrement_meets_spec
     * Theorem: Decrement followed by getCount returns count - 1
     */
    function testProperty_Decrement_GetCount_ReturnsDecremented() public {
        // Setup: Start with count > 0
        (bool success,) = counter.call(abi.encodeWithSignature("increment()"));
        require(success);

        uint256 countBefore = readStorage(0);

        // Action: Decrement
        (success,) = counter.call(abi.encodeWithSignature("decrement()"));
        require(success);

        // Action: GetCount
        (, bytes memory data) = counter.call(abi.encodeWithSignature("getCount()"));
        uint256 countAfter = abi.decode(data, (uint256));

        // Assert
        assertEq(countAfter, countBefore - 1, "getCount after decrement = initial - 1");
    }

    /**
     * Property 6: two_increments_meets_spec
     * Property: increment_twice_adds_two
     * Theorem: Two increments add 2 to the count (modular arithmetic)
     */
    function testProperty_TwoIncrements_AddsTwo() public {
        uint256 countBefore = readStorage(0);

        // Action: Increment twice
        (bool success,) = counter.call(abi.encodeWithSignature("increment()"));
        require(success);
        (success,) = counter.call(abi.encodeWithSignature("increment()"));
        require(success);

        uint256 countAfter = readStorage(0);

        // Assert: count increased by 2 (with wraparound)
        assertEq(countAfter, countBefore + 2, "Two increments add 2");
    }

    /**
     * Property 7: increment_decrement_meets_cancel
     * Property: increment_decrement_cancel
     * Theorem: Increment then decrement cancels (when no overflow)
     */
    function testProperty_Increment_Decrement_Cancels() public {
        vm.assume(readStorage(0) < type(uint256).max); // Prevent overflow

        uint256 countBefore = readStorage(0);

        // Action: Increment then decrement
        (bool success,) = counter.call(abi.encodeWithSignature("increment()"));
        require(success);
        (success,) = counter.call(abi.encodeWithSignature("decrement()"));
        require(success);

        uint256 countAfter = readStorage(0);

        // Assert: count unchanged
        assertEq(countAfter, countBefore, "Increment then decrement cancels");
    }

    /**
     * Property 8: getCount_preserves_wellformedness
     * Theorem: getCount preserves contract invariants (trivial for Counter)
     * Note: Counter has no complex invariants, so this just confirms read-only
     */
    function testProperty_GetCount_PreservesInvariants() public {
        // This is essentially the same as property 3 for Counter
        // For more complex contracts, this would verify invariants hold
        testProperty_GetCount_PreservesState();
    }

    /**
     * Property 9: decrement_getCount_correct
     * Theorem: decrement → getCount returns count - 1
     * (Similar to property 5 but focuses on the composition)
     */
    function testProperty_Decrement_GetCount_Composition() public {
        // Setup: Set a known count
        uint256 initialCount = 42;
        vm.store(counter, bytes32(uint256(0)), bytes32(initialCount));

        // Action: Decrement then getCount
        (bool success,) = counter.call(abi.encodeWithSignature("decrement()"));
        require(success);

        (, bytes memory data) = counter.call(abi.encodeWithSignature("getCount()"));
        uint256 result = abi.decode(data, (uint256));

        // Assert
        assertEq(result, initialCount - 1, "Decrement-getCount composition correct");
    }

    /**
     * Property 10: decrement_at_zero_wraps_max
     * Theorem: Decrementing at zero wraps to MAX_UINT256 (EVM modular arithmetic)
     * This is a critical edge case property
     */
    function testProperty_Decrement_AtZero_WrapsToMax() public {
        // Setup: Ensure count is 0
        vm.store(counter, bytes32(uint256(0)), bytes32(uint256(0)));
        assertEq(readStorage(0), 0, "Initial count is 0");

        // Action: Decrement
        (bool success,) = counter.call(abi.encodeWithSignature("decrement()"));
        require(success);

        // Assert: Count wrapped to MAX_UINT256
        assertEq(readStorage(0), type(uint256).max, "Decrement at 0 wraps to MAX");
    }

    /**
     * Additional fuzzing property: Increment-decrement cancellation holds for all valid counts
     */
    function testFuzz_Increment_Decrement_Cancels(uint256 initialCount) public {
        vm.assume(initialCount < type(uint256).max); // Prevent overflow

        // Setup
        vm.store(counter, bytes32(uint256(0)), bytes32(initialCount));

        // Action: Increment then decrement
        (bool success,) = counter.call(abi.encodeWithSignature("increment()"));
        require(success);
        (success,) = counter.call(abi.encodeWithSignature("decrement()"));
        require(success);

        // Assert: Returns to initial
        assertEq(readStorage(0), initialCount, "Inc-dec cancels for any count");
    }

    /**
     * Additional fuzzing property: Double increment always adds 2
     */
    function testFuzz_TwoIncrements_AddsTwo(uint256 initialCount) public {
        vm.assume(initialCount <= type(uint256).max - 2); // Prevent overflow

        // Setup
        vm.store(counter, bytes32(uint256(0)), bytes32(initialCount));

        // Action: Increment twice
        (bool success,) = counter.call(abi.encodeWithSignature("increment()"));
        require(success);
        (success,) = counter.call(abi.encodeWithSignature("increment()"));
        require(success);

        // Assert
        assertEq(readStorage(0), initialCount + 2, "Two increments always add 2");
    }

    // Helper function to read storage
    function readStorage(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(counter, bytes32(slot)));
    }
}
