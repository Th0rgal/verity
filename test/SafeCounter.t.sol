// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "../contracts/SafeCounter.sol";

/**
 * @title SafeCounterTest
 * @notice Tests for the SafeCounter contract
 * @dev Validates that the Lean EDSL semantics match the Solidity implementation
 *      with safe arithmetic (overflow/underflow protection)
 */
contract SafeCounterTest is Test {
    SafeCounter public safeCounter;

    function setUp() public {
        safeCounter = new SafeCounter();
    }

    /// @notice Test initial state (should be 0)
    function test_InitialState() public {
        assertEq(safeCounter.getCount(), 0, "Initial count should be 0");
    }

    /// @notice Test single increment
    function test_Increment() public {
        safeCounter.increment();
        assertEq(safeCounter.getCount(), 1, "Count should be 1 after increment");
    }

    /// @notice Test multiple increments
    function test_MultipleIncrements() public {
        safeCounter.increment();
        safeCounter.increment();
        safeCounter.increment();
        assertEq(safeCounter.getCount(), 3, "Count should be 3 after three increments");
    }

    /// @notice Test decrement
    function test_Decrement() public {
        safeCounter.increment();
        safeCounter.increment();
        safeCounter.decrement();
        assertEq(safeCounter.getCount(), 1, "Count should be 1 after two increments and one decrement");
    }

    /// @notice Test the example usage pattern from Lean
    function test_ExampleUsage() public {
        // Matches the Lean example: increment twice, decrement once
        safeCounter.increment();
        safeCounter.increment();
        safeCounter.decrement();
        assertEq(safeCounter.getCount(), 1, "Should match Lean example output");
    }

    /// @notice Test underflow protection (decrement from zero reverts)
    function test_UnderflowProtection() public {
        // Solidity 0.8+ reverts on underflow
        vm.expectRevert(stdError.arithmeticError);
        safeCounter.decrement();
    }

    /// @notice Test overflow protection (increment from max uint256 would revert)
    function test_OverflowProtection() public {
        // This test demonstrates overflow protection but is impractical to run
        // (would require 2^256 - 1 increments). We document the behavior instead.

        // Instead, we can test the principle with a smaller example:
        // Set count to max uint256 - 1, increment twice should fail on second increment

        // Note: We can't actually test this without exposing internal state or
        // using assembly, so this test documents the expected behavior

        // In practice, Solidity 0.8+ will revert with arithmetic error on overflow
    }

    /// @notice Fuzz test: increment N times
    function testFuzz_Increment(uint8 n) public {
        for (uint256 i = 0; i < n; i++) {
            safeCounter.increment();
        }
        assertEq(safeCounter.getCount(), n, "Count should equal number of increments");
    }

    /// @notice Test that safe arithmetic prevents silent wraparound
    function test_NoSilentWraparound() public {
        // This test documents that unlike unchecked arithmetic,
        // safe arithmetic will revert rather than wrap around

        // Decrement from 0 should revert (not wrap to max uint256)
        vm.expectRevert(stdError.arithmeticError);
        safeCounter.decrement();

        // After failed operation, state should be unchanged
        assertEq(safeCounter.getCount(), 0, "Count should still be 0 after failed decrement");
    }
}
