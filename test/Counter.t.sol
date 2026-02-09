// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "../contracts/Counter.sol";

/**
 * @title CounterTest
 * @notice Tests for the Counter contract
 * @dev Validates that the Lean EDSL semantics match the Solidity implementation
 */
contract CounterTest is Test {
    Counter public counter;

    function setUp() public {
        counter = new Counter();
    }

    /// @notice Test initial state (should be 0)
    function test_InitialState() public {
        assertEq(counter.getCount(), 0, "Initial count should be 0");
    }

    /// @notice Test single increment
    function test_Increment() public {
        counter.increment();
        assertEq(counter.getCount(), 1, "Count should be 1 after increment");
    }

    /// @notice Test multiple increments
    function test_MultipleIncrements() public {
        counter.increment();
        counter.increment();
        counter.increment();
        assertEq(counter.getCount(), 3, "Count should be 3 after three increments");
    }

    /// @notice Test decrement
    function test_Decrement() public {
        counter.increment();
        counter.increment();
        counter.decrement();
        assertEq(counter.getCount(), 1, "Count should be 1 after two increments and one decrement");
    }

    /// @notice Test the example usage pattern from Lean
    function test_ExampleUsage() public {
        // Matches the Lean example: increment twice, decrement once
        counter.increment();
        counter.increment();
        counter.decrement();
        assertEq(counter.getCount(), 1, "Should match Lean example output");
    }

    /// @notice Test decrement from zero (underflow protection)
    function test_DecrementFromZero() public {
        // In Solidity 0.8+, this will REVERT due to underflow protection
        // This is the correct behavior - we want to prevent underflows
        // Note: This test expects a revert
        vm.expectRevert(stdError.arithmeticError);
        counter.decrement();
    }

    /// @notice Fuzz test: increment N times
    function testFuzz_Increment(uint8 n) public {
        for (uint256 i = 0; i < n; i++) {
            counter.increment();
        }
        assertEq(counter.getCount(), n, "Count should equal number of increments");
    }
}
