// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "../examples/solidity/SimpleToken.sol";

contract SimpleTokenTest is Test {
    SimpleToken public token;
    address alice = address(0xA11CE);
    address bob = address(0xB0B);
    address charlie = address(0xC);

    function setUp() public {
        vm.prank(alice);
        token = new SimpleToken(alice);
    }

    // Test initial state
    function test_InitialState() public view {
        assertEq(token.owner(), alice, "Owner should be Alice");
        assertEq(token.totalSupply(), 0, "Initial supply should be 0");
        assertEq(token.balances(alice), 0, "Alice balance should be 0");
    }

    // Test owner can mint
    function test_OwnerCanMint() public {
        vm.prank(alice);
        token.mint(alice, 1000);

        assertEq(token.balances(alice), 1000, "Alice should have 1000");
        assertEq(token.totalSupply(), 1000, "Total supply should be 1000");
    }

    // Test non-owner cannot mint
    function test_NonOwnerCannotMint() public {
        vm.prank(bob);
        vm.expectRevert(SimpleToken.NotOwner.selector);
        token.mint(bob, 1000);
    }

    // Test transfer
    function test_Transfer() public {
        // Alice mints 1000 to herself
        vm.prank(alice);
        token.mint(alice, 1000);

        // Alice transfers 300 to Bob
        vm.prank(alice);
        token.transfer(bob, 300);

        assertEq(token.balances(alice), 700, "Alice should have 700");
        assertEq(token.balances(bob), 300, "Bob should have 300");
        assertEq(token.totalSupply(), 1000, "Total supply should still be 1000");
    }

    // Test transfer with insufficient balance
    function test_TransferInsufficientBalance() public {
        vm.prank(alice);
        token.mint(alice, 100);

        vm.prank(alice);
        vm.expectRevert(SimpleToken.InsufficientBalance.selector);
        token.transfer(bob, 200);
    }

    // Test balanceOf
    function test_BalanceOf() public {
        vm.prank(alice);
        token.mint(alice, 500);

        assertEq(token.balanceOf(alice), 500, "balanceOf should return 500");
        assertEq(token.balanceOf(bob), 0, "Bob balance should be 0");
    }

    // Test example usage from Lean
    function test_ExampleUsage() public {
        // Alice creates token (constructor called in setUp)
        // Alice mints 1000 to herself
        vm.prank(alice);
        token.mint(alice, 1000);

        // Alice transfers 300 to Bob
        vm.prank(alice);
        token.transfer(bob, 300);

        // Check final state
        assertEq(token.balances(alice), 700, "Alice should have 700");
        assertEq(token.balances(bob), 300, "Bob should have 300");
        assertEq(token.totalSupply(), 1000, "Total supply should be 1000");
    }

    // Test multiple mints increase supply
    function test_MultipleMints() public {
        vm.prank(alice);
        token.mint(alice, 500);

        vm.prank(alice);
        token.mint(bob, 300);

        assertEq(token.balances(alice), 500, "Alice should have 500");
        assertEq(token.balances(bob), 300, "Bob should have 300");
        assertEq(token.totalSupply(), 800, "Total supply should be 800");
    }

    // Test transfer to multiple recipients
    function test_MultipleTransfers() public {
        vm.prank(alice);
        token.mint(alice, 1000);

        vm.prank(alice);
        token.transfer(bob, 300);

        vm.prank(alice);
        token.transfer(charlie, 200);

        assertEq(token.balances(alice), 500, "Alice should have 500");
        assertEq(token.balances(bob), 300, "Bob should have 300");
        assertEq(token.balances(charlie), 200, "Charlie should have 200");
        assertEq(token.totalSupply(), 1000, "Total supply should be 1000");
    }

    // Test minting doesn't affect other balances
    function test_MintingIndependence() public {
        vm.prank(alice);
        token.mint(alice, 500);

        vm.prank(alice);
        token.mint(bob, 300);

        // Alice's balance should not change when minting to Bob
        assertEq(token.balances(alice), 500, "Alice balance unchanged");
    }

    // Fuzz test: mint arbitrary amount
    function testFuzz_Mint(uint128 amount) public {
        vm.prank(alice);
        token.mint(alice, amount);

        assertEq(token.balances(alice), amount, "Balance should equal minted amount");
        assertEq(token.totalSupply(), amount, "Total supply should equal minted amount");
    }

    // Fuzz test: transfer arbitrary amount
    function testFuzz_Transfer(uint128 mintAmount, uint128 transferAmount) public {
        vm.assume(transferAmount <= mintAmount);

        vm.prank(alice);
        token.mint(alice, mintAmount);

        vm.prank(alice);
        token.transfer(bob, transferAmount);

        assertEq(token.balances(alice), mintAmount - transferAmount, "Alice balance correct");
        assertEq(token.balances(bob), transferAmount, "Bob balance correct");
        assertEq(token.totalSupply(), mintAmount, "Total supply unchanged by transfer");
    }
}
