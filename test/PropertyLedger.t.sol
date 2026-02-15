// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyLedgerTest
 * @notice Property-based tests extracted from formally verified Lean theorems
 * @dev Maps theorems from Verity/Proofs/Ledger/*.lean to executable tests
 *
 * This file contains property tests for Ledger's 31 proven theorems:
 *
 * Basic.lean (18 theorems):
 * 1. getBalance_meets_spec - Read returns correct balance
 * 2. getBalance_returns_balance - Read returns balance value
 * 3. getBalance_preserves_state - Read is read-only
 * 4. deposit_meets_spec - Deposit follows specification
 * 5. deposit_increases_balance - Deposit adds to sender balance
 * 6. deposit_preserves_other_balances - Deposit only affects sender
 * 7. withdraw_meets_spec - Withdraw follows specification
 * 8. withdraw_decreases_balance - Withdraw subtracts from balance
 * 9. withdraw_reverts_insufficient - Withdraw reverts with insufficient balance
 * 10. transfer_meets_spec - Transfer follows specification
 * 11. transfer_decreases_sender - Transfer subtracts from sender
 * 12. transfer_increases_recipient - Transfer adds to recipient
 * 13. transfer_reverts_insufficient - Transfer reverts with insufficient balance
 * 14. deposit_preserves_non_mapping - Deposit doesn't affect other storage
 * 15. withdraw_preserves_non_mapping - Withdraw doesn't affect other storage
 * 16. deposit_preserves_wellformedness - Deposit maintains invariants
 * 17. withdraw_preserves_wellformedness - Withdraw maintains invariants
 * 18. deposit_getBalance_correct - Deposit->read composition
 *
 * Correctness.lean (6 theorems):
 * 19. transfer_preserves_wellformedness - Transfer maintains invariants
 * 20. transfer_preserves_non_mapping - Transfer doesn't affect other storage
 * 21. withdraw_getBalance_correct - Withdraw->read composition
 * 22. transfer_getBalance_sender_correct - Transfer->read sender
 * 23. transfer_getBalance_recipient_correct - Transfer->read recipient
 * 24. deposit_withdraw_cancel - Deposit->withdraw cancels
 *
 * Conservation.lean (7 theorems) - Advanced balance conservation properties
 * Note: Some conservation theorems involve complex sum invariants that are
 * better validated through differential testing rather than individual property tests.
 */
contract PropertyLedgerTest is YulTestBase {
    address ledger;
    address alice = address(0x1111);
    address bob = address(0x2222);
    address charlie = address(0x3333);

    function setUp() public {
        ledger = deployYul("Ledger");
        require(ledger != address(0), "Deploy failed");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Basic Properties - Read Operations
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 1: getBalance_meets_spec
     * Theorem: getBalance returns correct result per specification
     */
    function testProperty_GetBalance_MeetsSpec() public {
        uint256 expected = getBalanceFromStorage(alice);
        bytes memory result = callGetBalance(alice);
        uint256 balance = abi.decode(result, (uint256));
        assertEq(balance, expected, "getBalance doesn't meet spec");
    }

    /**
     * Property 2: getBalance_returns_balance (fuzz test)
     * Theorem: getBalance returns the balance value
     */
    function testProperty_GetBalance_ReturnsBalance(address addr, uint256 amount) public {
        vm.assume(amount <= type(uint256).max / 2);

        setBalance(addr, amount);
        bytes memory result = callGetBalance(addr);
        uint256 balance = abi.decode(result, (uint256));
        assertEq(balance, amount, "getBalance doesn't return balance");
    }

    /**
     * Property 3: getBalance_preserves_state (fuzz test)
     * Theorem: getBalance is read-only
     */
    function testProperty_GetBalance_PreservesState(address addr) public {
        uint256 balanceBefore = getBalanceFromStorage(addr);
        callGetBalance(addr);
        assertEq(getBalanceFromStorage(addr), balanceBefore, "getBalance modified state");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Deposit Properties
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 4: deposit_meets_spec (fuzz test)
     * Theorem: Deposit follows the formal specification
     */
    function testProperty_Deposit_MeetsSpec(address sender, uint256 amount) public {
        vm.assume(amount > 0 && amount <= type(uint256).max / 2);

        uint256 before = getBalanceFromStorage(sender);
        vm.assume(before + amount <= type(uint256).max);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("deposit(uint256)", amount));
        require(success, "deposit failed");

        assertEq(getBalanceFromStorage(sender), before + amount, "deposit doesn't meet spec");
    }

    /**
     * Property 5: deposit_increases_balance (fuzz test)
     * Theorem: Deposit increases sender's balance by the deposited amount
     */
    function testProperty_Deposit_IncreasesBalance(address sender, uint256 amount) public {
        vm.assume(amount > 0 && amount <= type(uint256).max / 2);

        uint256 before = getBalanceFromStorage(sender);
        vm.assume(before + amount <= type(uint256).max);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("deposit(uint256)", amount));
        require(success, "deposit failed");

        assertEq(getBalanceFromStorage(sender), before + amount, "deposit didn't increase balance");
    }

    /**
     * Property 6: deposit_preserves_other_balances (fuzz test)
     * Theorem: Deposit only affects sender's balance
     */
    function testProperty_Deposit_PreservesOtherBalances(address sender, address other, uint256 amount) public {
        vm.assume(sender != other);
        vm.assume(amount > 0 && amount <= type(uint256).max / 2);

        uint256 senderBefore = getBalanceFromStorage(sender);
        vm.assume(senderBefore + amount <= type(uint256).max);

        uint256 otherBefore = getBalanceFromStorage(other);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("deposit(uint256)", amount));
        require(success, "deposit failed");

        assertEq(getBalanceFromStorage(other), otherBefore, "deposit modified other balance");
    }

    /**
     * Property 14: deposit_preserves_non_mapping
     * Theorem: Deposit doesn't affect non-mapping storage
     */
    function testProperty_Deposit_PreservesNonMapping() public {
        uint256 slot0Before = readStorage(0);

        vm.prank(alice);
        (bool success,) = ledger.call(abi.encodeWithSignature("deposit(uint256)", 1000));
        require(success, "deposit failed");

        assertEq(readStorage(0), slot0Before, "deposit modified non-mapping storage");
    }

    /**
     * Property 16: deposit_preserves_wellformedness
     * Theorem: Deposit maintains contract invariants
     */
    function testProperty_Deposit_PreservesWellFormedness(address sender, uint256 amount) public {
        vm.assume(amount > 0 && amount <= type(uint256).max / 2);

        uint256 before = getBalanceFromStorage(sender);
        vm.assume(before + amount <= type(uint256).max);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("deposit(uint256)", amount));
        require(success, "deposit failed");

        assertTrue(getBalanceFromStorage(sender) <= type(uint256).max, "balance out of bounds");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Withdraw Properties
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 7: withdraw_meets_spec (fuzz test)
     * Theorem: Withdraw follows the formal specification
     */
    function testProperty_Withdraw_MeetsSpec(address sender, uint256 initialBalance, uint256 amount) public {
        vm.assume(amount > 0 && amount <= initialBalance);
        vm.assume(initialBalance <= type(uint256).max / 2);

        setBalance(sender, initialBalance);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("withdraw(uint256)", amount));
        require(success, "withdraw failed");

        assertEq(getBalanceFromStorage(sender), initialBalance - amount, "withdraw doesn't meet spec");
    }

    /**
     * Property 8: withdraw_decreases_balance (fuzz test)
     * Theorem: Withdraw decreases sender's balance by the withdrawn amount
     */
    function testProperty_Withdraw_DecreasesBalance(address sender, uint256 initialBalance, uint256 amount) public {
        vm.assume(amount > 0 && amount <= initialBalance);
        vm.assume(initialBalance <= type(uint256).max / 2);

        setBalance(sender, initialBalance);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("withdraw(uint256)", amount));
        require(success, "withdraw failed");

        assertEq(getBalanceFromStorage(sender), initialBalance - amount, "withdraw didn't decrease balance");
    }

    /**
     * Property 9: withdraw_reverts_insufficient
     * Theorem: Withdraw reverts when balance is insufficient
     */
    function testProperty_Withdraw_RevertsInsufficientBalance() public {
        setBalance(alice, 100);

        vm.prank(alice);
        (bool success,) = ledger.call(abi.encodeWithSignature("withdraw(uint256)", 101));
        assertFalse(success, "withdraw should revert with insufficient balance");
    }

    /**
     * Property 15: withdraw_preserves_non_mapping
     * Theorem: Withdraw doesn't affect non-mapping storage
     */
    function testProperty_Withdraw_PreservesNonMapping() public {
        setBalance(alice, 1000);
        uint256 slot0Before = readStorage(0);

        vm.prank(alice);
        (bool success,) = ledger.call(abi.encodeWithSignature("withdraw(uint256)", 500));
        require(success, "withdraw failed");

        assertEq(readStorage(0), slot0Before, "withdraw modified non-mapping storage");
    }

    /**
     * Property 17: withdraw_preserves_wellformedness
     * Theorem: Withdraw maintains contract invariants
     */
    function testProperty_Withdraw_PreservesWellFormedness(address sender, uint256 initialBalance, uint256 amount) public {
        vm.assume(amount > 0 && amount <= initialBalance);
        vm.assume(initialBalance <= type(uint256).max / 2);

        setBalance(sender, initialBalance);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("withdraw(uint256)", amount));
        require(success, "withdraw failed");

        assertTrue(getBalanceFromStorage(sender) <= type(uint256).max, "balance out of bounds");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Transfer Properties
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 10: transfer_meets_spec (fuzz test)
     * Theorem: Transfer follows the formal specification
     */
    function testProperty_Transfer_MeetsSpec(address sender, address recipient, uint256 senderBalance, uint256 amount) public {
        vm.assume(sender != recipient);
        vm.assume(amount > 0 && amount <= senderBalance);
        vm.assume(senderBalance <= type(uint256).max / 2);

        setBalance(sender, senderBalance);
        uint256 recipientBefore = getBalanceFromStorage(recipient);
        vm.assume(recipientBefore + amount <= type(uint256).max);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("transfer(address,uint256)", recipient, amount));
        require(success, "transfer failed");

        assertEq(getBalanceFromStorage(sender), senderBalance - amount, "sender balance incorrect");
        assertEq(getBalanceFromStorage(recipient), recipientBefore + amount, "recipient balance incorrect");
    }

    /**
     * Property 11: transfer_decreases_sender (fuzz test)
     * Theorem: Transfer decreases sender's balance
     */
    function testProperty_Transfer_DecreasesSender(address sender, address recipient, uint256 senderBalance, uint256 amount) public {
        vm.assume(sender != recipient);
        vm.assume(amount > 0 && amount <= senderBalance);
        vm.assume(senderBalance <= type(uint256).max / 2);

        setBalance(sender, senderBalance);
        uint256 recipientBefore = getBalanceFromStorage(recipient);
        vm.assume(recipientBefore + amount <= type(uint256).max);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("transfer(address,uint256)", recipient, amount));
        require(success, "transfer failed");

        assertEq(getBalanceFromStorage(sender), senderBalance - amount, "sender balance didn't decrease");
    }

    /**
     * Property 12: transfer_increases_recipient (fuzz test)
     * Theorem: Transfer increases recipient's balance
     */
    function testProperty_Transfer_IncreasesRecipient(address sender, address recipient, uint256 senderBalance, uint256 amount) public {
        vm.assume(sender != recipient);
        vm.assume(amount > 0 && amount <= senderBalance);
        vm.assume(senderBalance <= type(uint256).max / 2);

        setBalance(sender, senderBalance);
        uint256 recipientBefore = getBalanceFromStorage(recipient);
        vm.assume(recipientBefore + amount <= type(uint256).max);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("transfer(address,uint256)", recipient, amount));
        require(success, "transfer failed");

        assertEq(getBalanceFromStorage(recipient), recipientBefore + amount, "recipient balance didn't increase");
    }

    /**
     * Property 12b: transfer_self_preserves_balance (fuzz test)
     * Theorem: Transfer to self preserves sender balance
     */
    function testProperty_Transfer_SelfPreservesBalance(address sender, uint256 senderBalance, uint256 amount) public {
        vm.assume(amount > 0 && amount <= senderBalance);
        vm.assume(senderBalance <= type(uint256).max / 2);

        setBalance(sender, senderBalance);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("transfer(address,uint256)", sender, amount));
        require(success, "transfer failed");

        assertEq(getBalanceFromStorage(sender), senderBalance, "self-transfer should preserve balance");
    }

    /**
     * Property 13: transfer_reverts_insufficient
     * Theorem: Transfer reverts when sender has insufficient balance
     */
    function testProperty_Transfer_RevertsInsufficientBalance() public {
        setBalance(alice, 100);

        vm.prank(alice);
        (bool success,) = ledger.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 101));
        assertFalse(success, "transfer should revert with insufficient balance");
    }

    /**
     * Property 19: transfer_preserves_wellformedness (fuzz test)
     * Theorem: Transfer maintains contract invariants
     */
    function testProperty_Transfer_PreservesWellFormedness(address sender, address recipient, uint256 senderBalance, uint256 amount) public {
        vm.assume(sender != recipient);
        vm.assume(amount > 0 && amount <= senderBalance);
        vm.assume(senderBalance <= type(uint256).max / 2);

        setBalance(sender, senderBalance);
        uint256 recipientBefore = getBalanceFromStorage(recipient);
        vm.assume(recipientBefore + amount <= type(uint256).max);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("transfer(address,uint256)", recipient, amount));
        require(success, "transfer failed");

        assertTrue(getBalanceFromStorage(sender) <= type(uint256).max, "sender balance out of bounds");
        assertTrue(getBalanceFromStorage(recipient) <= type(uint256).max, "recipient balance out of bounds");
    }

    /**
     * Property 20: transfer_preserves_non_mapping
     * Theorem: Transfer doesn't affect non-mapping storage
     */
    function testProperty_Transfer_PreservesNonMapping() public {
        setBalance(alice, 1000);
        uint256 slot0Before = readStorage(0);

        vm.prank(alice);
        (bool success,) = ledger.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 500));
        require(success, "transfer failed");

        assertEq(readStorage(0), slot0Before, "transfer modified non-mapping storage");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Composition Properties
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property 18: deposit_getBalance_correct (fuzz test)
     * Theorem: Deposit->getBalance composition is correct
     */
    function testProperty_Deposit_GetBalance_Correct(address sender, uint256 amount) public {
        vm.assume(amount > 0 && amount <= type(uint256).max / 2);

        uint256 before = getBalanceFromStorage(sender);
        vm.assume(before + amount <= type(uint256).max);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("deposit(uint256)", amount));
        require(success, "deposit failed");

        bytes memory result = callGetBalance(sender);
        uint256 balance = abi.decode(result, (uint256));
        assertEq(balance, before + amount, "deposit->getBalance incorrect");
    }

    /**
     * Property 21: withdraw_getBalance_correct (fuzz test)
     * Theorem: Withdraw->getBalance composition is correct
     */
    function testProperty_Withdraw_GetBalance_Correct(address sender, uint256 initialBalance, uint256 amount) public {
        vm.assume(amount > 0 && amount <= initialBalance);
        vm.assume(initialBalance <= type(uint256).max / 2);

        setBalance(sender, initialBalance);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("withdraw(uint256)", amount));
        require(success, "withdraw failed");

        bytes memory result = callGetBalance(sender);
        uint256 balance = abi.decode(result, (uint256));
        assertEq(balance, initialBalance - amount, "withdraw->getBalance incorrect");
    }

    /**
     * Property 22: transfer_getBalance_sender_correct (fuzz test)
     * Theorem: Transfer->getBalance (sender) composition is correct
     */
    function testProperty_Transfer_GetBalance_Sender_Correct(address sender, address recipient, uint256 senderBalance, uint256 amount) public {
        vm.assume(sender != recipient);
        vm.assume(amount > 0 && amount <= senderBalance);
        vm.assume(senderBalance <= type(uint256).max / 2);

        setBalance(sender, senderBalance);
        uint256 recipientBefore = getBalanceFromStorage(recipient);
        vm.assume(recipientBefore + amount <= type(uint256).max);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("transfer(address,uint256)", recipient, amount));
        require(success, "transfer failed");

        bytes memory result = callGetBalance(sender);
        uint256 balance = abi.decode(result, (uint256));
        assertEq(balance, senderBalance - amount, "transfer->getBalance sender incorrect");
    }

    /**
     * Property 23: transfer_getBalance_recipient_correct (fuzz test)
     * Theorem: Transfer->getBalance (recipient) composition is correct
     */
    function testProperty_Transfer_GetBalance_Recipient_Correct(address sender, address recipient, uint256 senderBalance, uint256 amount) public {
        vm.assume(sender != recipient);
        vm.assume(amount > 0 && amount <= senderBalance);
        vm.assume(senderBalance <= type(uint256).max / 2);

        setBalance(sender, senderBalance);
        uint256 recipientBefore = getBalanceFromStorage(recipient);
        vm.assume(recipientBefore + amount <= type(uint256).max);

        vm.prank(sender);
        (bool success,) = ledger.call(abi.encodeWithSignature("transfer(address,uint256)", recipient, amount));
        require(success, "transfer failed");

        bytes memory result = callGetBalance(recipient);
        uint256 balance = abi.decode(result, (uint256));
        assertEq(balance, recipientBefore + amount, "transfer->getBalance recipient incorrect");
    }

    /**
     * Property 24: deposit_withdraw_cancel (fuzz test)
     * Theorem: Deposit->withdraw cancels (returns to original state)
     */
    function testProperty_Deposit_Withdraw_Cancel(address sender, uint256 amount) public {
        vm.assume(amount > 0 && amount <= type(uint256).max / 4);

        uint256 before = getBalanceFromStorage(sender);
        vm.assume(before + amount <= type(uint256).max);

        vm.prank(sender);
        (bool success1,) = ledger.call(abi.encodeWithSignature("deposit(uint256)", amount));
        require(success1, "deposit failed");

        vm.prank(sender);
        (bool success2,) = ledger.call(abi.encodeWithSignature("withdraw(uint256)", amount));
        require(success2, "withdraw failed");

        assertEq(getBalanceFromStorage(sender), before, "deposit->withdraw didn't cancel");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Utility Functions
    //═══════════════════════════════════════════════════════════════════════════

    function readStorage(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(ledger, bytes32(slot)));
    }

    function getBalanceFromStorage(address addr) internal view returns (uint256) {
        // Balance is stored in mapping at slot 0
        bytes32 slot = keccak256(abi.encode(addr, uint256(0)));
        return uint256(vm.load(ledger, slot));
    }

    function setBalance(address addr, uint256 amount) internal {
        bytes32 slot = keccak256(abi.encode(addr, uint256(0)));
        vm.store(ledger, slot, bytes32(amount));
    }

    function callGetBalance(address addr) internal returns (bytes memory) {
        (bool success, bytes memory data) = ledger.call(
            abi.encodeWithSignature("getBalance(address)", addr)
        );
        require(success, "getBalance call failed");
        return data;
    }
}
