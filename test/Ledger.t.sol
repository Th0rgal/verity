// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "../examples/solidity/Ledger.sol";

contract LedgerTest is Test {
    Ledger public ledger;
    address alice = address(0xA11CE);
    address bob = address(0xB0B);

    function setUp() public {
        ledger = new Ledger();
    }

    // Test initial state
    function test_InitialBalance() public view {
        assertEq(ledger.balances(alice), 0, "Initial balance should be 0");
    }

    // Test deposit
    function test_Deposit() public {
        vm.prank(alice);
        ledger.deposit(100);
        assertEq(ledger.balances(alice), 100, "Balance should be 100 after deposit");
    }

    // Test withdraw
    function test_Withdraw() public {
        vm.prank(alice);
        ledger.deposit(100);

        vm.prank(alice);
        ledger.withdraw(30);

        assertEq(ledger.balances(alice), 70, "Balance should be 70 after withdraw");
    }

    // Test insufficient balance for withdraw
    function test_WithdrawInsufficientBalance() public {
        vm.prank(alice);
        ledger.deposit(100);

        vm.prank(alice);
        vm.expectRevert(Ledger.InsufficientBalance.selector);
        ledger.withdraw(200);
    }

    // Test transfer
    function test_Transfer() public {
        vm.prank(alice);
        ledger.deposit(100);

        vm.prank(alice);
        ledger.transfer(bob, 50);

        assertEq(ledger.balances(alice), 50, "Alice balance should be 50");
        assertEq(ledger.balances(bob), 50, "Bob balance should be 50");
    }

    // Test transfer with insufficient balance
    function test_TransferInsufficientBalance() public {
        vm.prank(alice);
        ledger.deposit(100);

        vm.prank(alice);
        vm.expectRevert(Ledger.InsufficientBalance.selector);
        ledger.transfer(bob, 200);
    }

    // Test example usage from Lean: deposit 100, withdraw 30, transfer 50
    function test_ExampleUsage() public {
        // Alice deposits 100
        vm.prank(alice);
        ledger.deposit(100);

        // Alice withdraws 30 (balance: 70)
        vm.prank(alice);
        ledger.withdraw(30);

        // Alice transfers 50 to Bob (Alice: 20, Bob: 50)
        vm.prank(alice);
        ledger.transfer(bob, 50);

        // Check final balances
        assertEq(ledger.balances(alice), 20, "Alice should have 20");
        assertEq(ledger.balances(bob), 50, "Bob should have 50");
    }

    // Test getBalance function
    function test_GetBalance() public {
        vm.prank(alice);
        ledger.deposit(100);

        assertEq(ledger.getBalance(alice), 100, "getBalance should return 100");
    }

    // Test multiple deposits
    function test_MultipleDeposits() public {
        vm.prank(alice);
        ledger.deposit(50);

        vm.prank(alice);
        ledger.deposit(30);

        assertEq(ledger.balances(alice), 80, "Balance should be 80 after two deposits");
    }

    // Fuzz test: deposit and withdraw
    function testFuzz_DepositWithdraw(uint128 amount) public {
        vm.prank(alice);
        ledger.deposit(amount);

        vm.prank(alice);
        ledger.withdraw(amount);

        assertEq(ledger.balances(alice), 0, "Balance should be 0 after depositing and withdrawing same amount");
    }

    // Fuzz test: transfer
    function testFuzz_Transfer(uint128 amount) public {
        vm.prank(alice);
        ledger.deposit(amount);

        vm.prank(alice);
        ledger.transfer(bob, amount);

        assertEq(ledger.balances(alice), 0, "Alice should have 0");
        assertEq(ledger.balances(bob), amount, "Bob should have the transferred amount");
    }
}
