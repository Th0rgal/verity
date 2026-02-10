// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "../examples/solidity/OwnedCounter.sol";

/**
 * @title OwnedCounterTest
 * @notice Tests for the OwnedCounter contract
 * @dev Validates pattern composition and that Lean EDSL semantics match Solidity
 */
contract OwnedCounterTest is Test {
    OwnedCounter public ownedCounter;
    address public alice = address(0xA11CE);
    address public bob = address(0xB0B);
    address public charlie = address(0xC4A411E);

    function setUp() public {
        // Deploy with Alice as owner
        ownedCounter = new OwnedCounter(alice);
    }

    /// @notice Test initial state
    function test_InitialState() public {
        assertEq(ownedCounter.getOwner(), alice, "Initial owner should be Alice");
        assertEq(ownedCounter.getCount(), 0, "Initial count should be 0");
    }

    /// @notice Test owner can increment
    function test_OwnerCanIncrement() public {
        vm.prank(alice);
        ownedCounter.increment();
        assertEq(ownedCounter.getCount(), 1, "Count should be 1");
    }

    /// @notice Test owner can decrement
    function test_OwnerCanDecrement() public {
        // First increment to have something to decrement
        vm.prank(alice);
        ownedCounter.increment();

        vm.prank(alice);
        ownedCounter.decrement();
        assertEq(ownedCounter.getCount(), 0, "Count should be back to 0");
    }

    /// @notice Test non-owner cannot increment
    function test_NonOwnerCannotIncrement() public {
        vm.prank(bob);
        vm.expectRevert(OwnedCounter.NotOwner.selector);
        ownedCounter.increment();
    }

    /// @notice Test non-owner cannot decrement
    function test_NonOwnerCannotDecrement() public {
        vm.prank(bob);
        vm.expectRevert(OwnedCounter.NotOwner.selector);
        ownedCounter.decrement();
    }

    /// @notice Test the example usage pattern from Lean
    function test_ExampleUsage() public {
        // Matches the Lean example: Alice increments twice, transfers to Bob
        vm.startPrank(alice);
        ownedCounter.increment();
        ownedCounter.increment();
        ownedCounter.transferOwnership(bob);
        vm.stopPrank();

        assertEq(ownedCounter.getCount(), 2, "Count should be 2");
        assertEq(ownedCounter.getOwner(), bob, "Owner should be Bob");
    }

    /// @notice Test ownership transfer changes who can increment
    function test_OwnershipTransferChangesAccess() public {
        // Alice increments
        vm.prank(alice);
        ownedCounter.increment();
        assertEq(ownedCounter.getCount(), 1, "Count should be 1");

        // Alice transfers to Bob
        vm.prank(alice);
        ownedCounter.transferOwnership(bob);

        // Alice can no longer increment
        vm.prank(alice);
        vm.expectRevert(OwnedCounter.NotOwner.selector);
        ownedCounter.increment();

        // Bob can increment
        vm.prank(bob);
        ownedCounter.increment();
        assertEq(ownedCounter.getCount(), 2, "Count should be 2");
    }

    /// @notice Test multiple increments and decrements
    function test_MultipleOperations() public {
        vm.startPrank(alice);
        ownedCounter.increment();
        ownedCounter.increment();
        ownedCounter.increment();
        assertEq(ownedCounter.getCount(), 3, "Count should be 3");

        ownedCounter.decrement();
        assertEq(ownedCounter.getCount(), 2, "Count should be 2");
        vm.stopPrank();
    }

    /// @notice Test that patterns don't interfere with each other
    function test_PatternsIndependent() public {
        // Counter operations don't affect ownership
        vm.prank(alice);
        ownedCounter.increment();
        assertEq(ownedCounter.getOwner(), alice, "Owner should still be Alice");

        // Ownership transfer doesn't affect count
        vm.prank(alice);
        ownedCounter.transferOwnership(bob);
        assertEq(ownedCounter.getCount(), 1, "Count should still be 1");
    }

    /// @notice Fuzz test: only owner can perform operations
    function testFuzz_OnlyOwnerCanOperate(address nonOwner) public {
        vm.assume(nonOwner != alice);

        vm.prank(nonOwner);
        vm.expectRevert(OwnedCounter.NotOwner.selector);
        ownedCounter.increment();

        vm.prank(nonOwner);
        vm.expectRevert(OwnedCounter.NotOwner.selector);
        ownedCounter.decrement();
    }

    /// @notice Fuzz test: increment N times as owner
    function testFuzz_IncrementN(uint8 n) public {
        vm.startPrank(alice);
        for (uint256 i = 0; i < n; i++) {
            ownedCounter.increment();
        }
        vm.stopPrank();

        assertEq(ownedCounter.getCount(), n, "Count should equal number of increments");
    }
}
