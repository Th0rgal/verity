// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "../examples/solidity/Owned.sol";

/**
 * @title OwnedTest
 * @notice Tests for the Owned contract
 * @dev Validates that the Lean EDSL semantics match the Solidity implementation
 */
contract OwnedTest is Test {
    Owned public owned;
    address public alice = address(0xA11CE);
    address public bob = address(0xB0B);
    address public charlie = address(0xC4A411E);

    function setUp() public {
        // Deploy with Alice as owner
        owned = new Owned(alice);
    }

    /// @notice Test initial owner is set correctly
    function test_InitialOwner() public {
        assertEq(owned.getOwner(), alice, "Initial owner should be Alice");
    }

    /// @notice Test owner can transfer ownership
    function test_TransferOwnership() public {
        vm.prank(alice);
        owned.transferOwnership(bob);
        assertEq(owned.getOwner(), bob, "Owner should be Bob after transfer");
    }

    /// @notice Test the example usage pattern from Lean
    function test_ExampleUsage() public {
        // Matches the Lean example: Alice transfers to Bob
        vm.prank(alice);
        owned.transferOwnership(bob);
        assertEq(owned.getOwner(), bob, "Should match Lean example output");
    }

    /// @notice Test non-owner cannot transfer ownership
    function test_NonOwnerCannotTransfer() public {
        vm.prank(bob);
        vm.expectRevert(Owned.NotOwner.selector);
        owned.transferOwnership(charlie);
    }

    /// @notice Test new owner can transfer ownership
    function test_NewOwnerCanTransfer() public {
        // Alice transfers to Bob
        vm.prank(alice);
        owned.transferOwnership(bob);

        // Bob transfers to Charlie
        vm.prank(bob);
        owned.transferOwnership(charlie);

        assertEq(owned.getOwner(), charlie, "Charlie should be the new owner");
    }

    /// @notice Test original owner loses access after transfer
    function test_OriginalOwnerLosesAccess() public {
        // Alice transfers to Bob
        vm.prank(alice);
        owned.transferOwnership(bob);

        // Alice can no longer transfer
        vm.prank(alice);
        vm.expectRevert(Owned.NotOwner.selector);
        owned.transferOwnership(charlie);
    }

    /// @notice Fuzz test: ownership can be transferred to any address
    function testFuzz_TransferOwnership(address newOwner) public {
        vm.prank(alice);
        owned.transferOwnership(newOwner);
        assertEq(owned.getOwner(), newOwner, "Owner should be updated to fuzzed address");
    }

    /// @notice Fuzz test: only owner can transfer
    function testFuzz_OnlyOwnerCanTransfer(address nonOwner) public {
        vm.assume(nonOwner != alice);

        vm.prank(nonOwner);
        vm.expectRevert(Owned.NotOwner.selector);
        owned.transferOwnership(bob);
    }
}
