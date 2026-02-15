// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "../examples/solidity/ReentrancyExample.sol";

/**
 * @title PropertyReentrancyExampleTest
 * @notice Property-based tests for the reentrancy example contracts
 * @dev Maps theorems from Verity/Examples/ReentrancyExample.lean to executable tests
 *
 * These tests validate proven Lean theorems against Solidity implementations:
 *
 * VulnerableBank (namespace VulnerableBank):
 * 1. vulnerable_attack_exists         — Supply invariant breaks after withdraw
 * 2. withdraw_maintains_supply_UNPROVABLE — Universal invariant is false
 *
 * SafeBank (namespace SafeBank):
 * 3. withdraw_maintains_supply        — Withdraw preserves supply invariant
 * 4. deposit_maintains_supply         — Deposit preserves supply invariant
 */
contract PropertyReentrancyExampleTest is Test {
    VulnerableBank vulnerable;
    SafeBank safe;

    address alice = address(0xA11CE);
    address bob = address(0xB0B);

    function setUp() public {
        vulnerable = new VulnerableBank();
        safe = new SafeBank();
    }

    //═══════════════════════════════════════════════════════════════════════════
    // VulnerableBank: Proven vulnerability properties
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 1: vulnerable_attack_exists
     * Theorem: There exists a state where the supply invariant holds before
     *          withdraw but breaks after withdraw (due to double totalSupply
     *          decrement modeling reentrancy).
     *
     * The Lean proof constructs a concrete counterexample with MAX_UINT256
     * balance and supply. After withdraw, totalSupply wraps to 1 while
     * balance wraps to 0, breaking totalSupply == sum(balances).
     */
    function testProperty_VulnerableBank_AttackExists() public {
        // Setup: Establish invariant (totalSupply == alice's balance)
        vm.prank(alice);
        vulnerable.deposit(100);

        // Verify invariant holds before withdraw
        assertEq(
            vulnerable.totalSupply(),
            vulnerable.balances(alice),
            "Invariant should hold before withdraw"
        );

        // Action: Withdraw (triggers double totalSupply decrement)
        vm.prank(alice);
        vulnerable.withdraw(50);

        // Assert: Invariant BROKEN (totalSupply decremented twice, balance once)
        // totalSupply = 100 - 50 - 50 = 0
        // balances[alice] = 100 - 50 = 50
        assertEq(vulnerable.totalSupply(), 0, "totalSupply should be 0 (decremented twice)");
        assertEq(vulnerable.balances(alice), 50, "Balance should be 50 (decremented once)");
        assertTrue(
            vulnerable.totalSupply() != vulnerable.balances(alice),
            "Invariant should be broken: totalSupply != balance"
        );
    }

    /**
     * Property 2: withdraw_maintains_supply_UNPROVABLE
     * Theorem: The universal supply preservation property is FALSE for
     *          VulnerableBank. For any amount > 0, the invariant breaks.
     *
     * This is a fuzz test that demonstrates the invariant breaks for
     * arbitrary (non-zero) deposit and withdrawal amounts.
     */
    function testFuzz_VulnerableBank_InvariantBreaks(uint256 depositAmt, uint256 withdrawAmt) public {
        // Constrain inputs to avoid trivial cases
        vm.assume(depositAmt > 0 && depositAmt < type(uint128).max);
        vm.assume(withdrawAmt > 0 && withdrawAmt <= depositAmt);

        // Setup: Establish invariant
        vm.prank(alice);
        vulnerable.deposit(depositAmt);
        assertEq(vulnerable.totalSupply(), vulnerable.balances(alice));

        // Action: Withdraw (uses unchecked wrapping arithmetic like Lean's sub)
        vm.prank(alice);
        vulnerable.withdraw(withdrawAmt);

        // Assert: Invariant broken (totalSupply short by withdrawAmt)
        // totalSupply = depositAmt - 2*withdrawAmt (wrapping at 2^256)
        // balance = depositAmt - withdrawAmt
        uint256 expectedSupply;
        unchecked {
            expectedSupply = depositAmt - 2 * withdrawAmt;
        }
        assertEq(
            vulnerable.totalSupply(),
            expectedSupply,
            "totalSupply decremented twice (wrapping)"
        );
        assertEq(
            vulnerable.balances(alice),
            depositAmt - withdrawAmt,
            "Balance decremented once"
        );
    }

    /**
     * Property: Vulnerable withdraw reverts on insufficient balance
     * Matches the EDSL: revert "Insufficient balance" when bal < amount
     */
    function testProperty_VulnerableBank_RevertsInsufficientBalance() public {
        vm.prank(alice);
        vulnerable.deposit(100);

        // Withdraw more than balance should revert
        vm.expectRevert("Insufficient balance");
        vm.prank(alice);
        vulnerable.withdraw(101);
    }

    //═══════════════════════════════════════════════════════════════════════════
    // SafeBank: Proven safety properties
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 3: withdraw_maintains_supply
     * Theorem: For all states where the supply invariant holds and the
     *          sender has sufficient balance, withdraw preserves the invariant.
     *
     * supplyInvariant s [s.sender] →
     * s.storageMap balances.slot s.sender ≥ amount →
     * supplyInvariant (withdraw amount).runState s) [s.sender]
     */
    function testProperty_SafeBank_WithdrawMaintainsSupply() public {
        // Setup: Establish invariant
        vm.prank(alice);
        safe.deposit(100);
        assertEq(safe.totalSupply(), safe.balances(alice), "Pre: invariant");

        // Action: Withdraw
        vm.prank(alice);
        safe.withdraw(50);

        // Assert: Invariant preserved
        assertEq(
            safe.totalSupply(),
            safe.balances(alice),
            "Post: supply invariant should hold after withdraw"
        );
    }

    /**
     * Property 3 (fuzz): withdraw_maintains_supply
     * Fuzz version that tests with arbitrary amounts.
     */
    function testFuzz_SafeBank_WithdrawMaintainsSupply(uint256 depositAmt, uint256 withdrawAmt) public {
        vm.assume(depositAmt > 0 && depositAmt < type(uint128).max);
        vm.assume(withdrawAmt > 0 && withdrawAmt <= depositAmt);

        // Setup: Establish invariant
        vm.prank(alice);
        safe.deposit(depositAmt);
        assertEq(safe.totalSupply(), safe.balances(alice));

        // Action: Withdraw
        vm.prank(alice);
        safe.withdraw(withdrawAmt);

        // Assert: Invariant preserved
        assertEq(
            safe.totalSupply(),
            safe.balances(alice),
            "Supply invariant must hold after withdraw"
        );
        assertEq(safe.totalSupply(), depositAmt - withdrawAmt);
    }

    /**
     * Property 4: deposit_maintains_supply
     * Theorem: For all states where the supply invariant holds,
     *          deposit preserves the invariant.
     *
     * supplyInvariant s [s.sender] →
     * supplyInvariant ((deposit amount).runState s) [s.sender]
     */
    function testProperty_SafeBank_DepositMaintainsSupply() public {
        // Multiple deposits should maintain invariant
        vm.prank(alice);
        safe.deposit(100);
        assertEq(safe.totalSupply(), safe.balances(alice), "After deposit 1");

        vm.prank(alice);
        safe.deposit(200);
        assertEq(safe.totalSupply(), safe.balances(alice), "After deposit 2");
    }

    /**
     * Property 4 (fuzz): deposit_maintains_supply
     * Fuzz version that tests with arbitrary amounts.
     */
    function testFuzz_SafeBank_DepositMaintainsSupply(uint256 amount1, uint256 amount2) public {
        vm.assume(amount1 < type(uint128).max);
        vm.assume(amount2 < type(uint128).max);

        vm.prank(alice);
        safe.deposit(amount1);
        assertEq(safe.totalSupply(), safe.balances(alice), "After first deposit");

        vm.prank(alice);
        safe.deposit(amount2);
        assertEq(safe.totalSupply(), safe.balances(alice), "After second deposit");
        assertEq(safe.totalSupply(), amount1 + amount2);
    }

    /**
     * Property: Safe withdraw reverts on insufficient balance
     */
    function testProperty_SafeBank_RevertsInsufficientBalance() public {
        vm.prank(alice);
        safe.deposit(100);

        vm.expectRevert("Insufficient balance");
        vm.prank(alice);
        safe.withdraw(101);
    }

    /**
     * Property: Deposit then withdraw cancels out (SafeBank)
     * Combined property showing full lifecycle preserves invariant
     */
    function testFuzz_SafeBank_DepositWithdrawCancel(uint256 amount) public {
        vm.assume(amount > 0 && amount < type(uint128).max);

        vm.prank(alice);
        safe.deposit(amount);

        vm.prank(alice);
        safe.withdraw(amount);

        assertEq(safe.totalSupply(), 0, "Supply should return to 0");
        assertEq(safe.balances(alice), 0, "Balance should return to 0");
        assertEq(safe.totalSupply(), safe.balances(alice), "Invariant holds");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Multi-user invariant tests
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property: SafeBank supply invariant holds with multiple users
     * Extension of the single-user invariant to multi-user scenarios
     */
    function testProperty_SafeBank_MultiUserInvariant() public {
        vm.prank(alice);
        safe.deposit(100);

        vm.prank(bob);
        safe.deposit(200);

        assertEq(
            safe.totalSupply(),
            safe.balances(alice) + safe.balances(bob),
            "Supply should equal sum of all balances"
        );

        vm.prank(alice);
        safe.withdraw(30);

        assertEq(
            safe.totalSupply(),
            safe.balances(alice) + safe.balances(bob),
            "Invariant holds after partial withdrawal"
        );
    }

    /**
     * Property: VulnerableBank invariant breaks with multiple users
     */
    function testProperty_VulnerableBank_MultiUserInvariantBreaks() public {
        vm.prank(alice);
        vulnerable.deposit(100);

        vm.prank(bob);
        vulnerable.deposit(200);

        assertEq(
            vulnerable.totalSupply(),
            vulnerable.balances(alice) + vulnerable.balances(bob),
            "Invariant holds before attack"
        );

        // Alice withdraws — triggers vulnerability
        vm.prank(alice);
        vulnerable.withdraw(50);

        // Invariant is now broken
        assertTrue(
            vulnerable.totalSupply() !=
                vulnerable.balances(alice) + vulnerable.balances(bob),
            "Invariant should be broken"
        );
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Comparative tests: VulnerableBank vs SafeBank
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property: Same operations produce different invariant outcomes
     * Demonstrates that the ordering of state updates matters
     */
    function testFuzz_Comparison_SameOps_DifferentOutcome(uint256 depositAmt, uint256 withdrawAmt) public {
        vm.assume(depositAmt > 0 && depositAmt < type(uint128).max);
        vm.assume(withdrawAmt > 0 && withdrawAmt <= depositAmt);

        // Same operations on both contracts
        vm.prank(alice);
        vulnerable.deposit(depositAmt);
        vm.prank(alice);
        safe.deposit(depositAmt);

        vm.prank(alice);
        vulnerable.withdraw(withdrawAmt);
        vm.prank(alice);
        safe.withdraw(withdrawAmt);

        // SafeBank invariant holds
        assertEq(
            safe.totalSupply(),
            safe.balances(alice),
            "SafeBank invariant should hold"
        );

        // VulnerableBank invariant broken
        assertTrue(
            vulnerable.totalSupply() != vulnerable.balances(alice),
            "VulnerableBank invariant should be broken"
        );
    }
}
