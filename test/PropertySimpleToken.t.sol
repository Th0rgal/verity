// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertySimpleTokenTest
 * @notice Property-based tests extracted from formally verified Lean theorems
 * @dev Maps theorems from Verity/Proofs/SimpleToken/*.lean to executable tests
 *
 * This file extracts 57 proven theorems into Foundry property tests:
 * - Basic properties (constructor, mint, transfer, getters)
 * - Supply conservation (total supply invariant)
 * - Isolation properties (storage independence)
 * - Correctness properties (access control, balance updates)
 */
contract PropertySimpleTokenTest is YulTestBase {
    address token;
    address owner = address(0xA11CE);
    address alice = address(0xA11CE);
    address bob = address(0xB0B);
    address charlie = address(0xC4A12);

    uint256 constant MAX_UINT256 = type(uint256).max;

    function setUp() public {
        // Deploy SimpleToken with alice as owner
        vm.prank(owner);
        token = deployYulWithArgs("SimpleToken", abi.encode(owner));
        require(token != address(0), "Deploy failed");
    }

    /**
     * Property: constructor_sets_owner
     * Property: constructor_meets_spec
     * Theorem: Constructor sets owner to initialOwner parameter
     */
    function testProperty_Constructor_SetsOwner() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(bob));
        (bool success, bytes memory data) = newToken.call(abi.encodeWithSignature("owner()"));
        require(success);
        address tokenOwner = abi.decode(data, (address));
        assertEq(tokenOwner, bob, "Owner should be bob");
    }

    /**
     * Property: constructor_sets_supply_zero
     * Theorem: Constructor initializes total supply to 0
     */
    function testProperty_Constructor_InitializesSupplyToZero() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(alice));
        (bool success, bytes memory data) = newToken.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supply = abi.decode(data, (uint256));
        assertEq(supply, 0, "Initial supply should be 0");
    }

    /**
     * Property: constructor_getTotalSupply_correct
     * Theorem: After construction, getTotalSupply returns 0
     */
    function testProperty_Constructor_GetTotalSupplyReturnsZero() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(owner));
        (bool success, bytes memory data) = newToken.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supply = abi.decode(data, (uint256));
        assertEq(supply, 0, "getTotalSupply should return 0 after construction");
    }

    /**
     * Property: constructor_getOwner_correct
     * Theorem: After construction, getOwner returns initialOwner
     */
    function testProperty_Constructor_GetOwnerCorrect() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(bob));
        (bool success, bytes memory data) = newToken.call(abi.encodeWithSignature("owner()"));
        require(success);
        address tokenOwner = abi.decode(data, (address));
        assertEq(tokenOwner, bob, "getOwner should return initial owner");
    }

    /**
     * Property: getTotalSupply_returns_supply
     * Property: getTotalSupply_meets_spec
     * Theorem: getTotalSupply returns storage slot 0 (total supply)
     */
    function testProperty_GetTotalSupply_ReturnsStorageValue() public {
        uint256 storageSupply = readStorage(2);
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 returned = abi.decode(data, (uint256));
        assertEq(returned, storageSupply, "getTotalSupply should return storage[0]");
    }

    /**
     * Property: getTotalSupply_preserves_state
     * Theorem: getTotalSupply is a pure read that doesn't modify state
     */
    function testProperty_GetTotalSupply_PreservesState() public {
        uint256 supplyBefore = readStorage(2);
        address ownerBefore = readStorageAddr(0);

        (bool success,) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);

        assertEq(readStorage(2), supplyBefore, "Supply unchanged");
        assertEq(readStorageAddr(0), ownerBefore, "Owner unchanged");
    }

    /**
     * Property: getOwner_returns_owner
     * Property: getOwner_meets_spec
     * Theorem: getOwner returns storage slot 1 (owner address)
     */
    function testProperty_GetOwner_ReturnsStorageValue() public {
        address storageOwner = readStorageAddr(0);
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("owner()"));
        require(success);
        address returned = abi.decode(data, (address));
        assertEq(returned, storageOwner, "getOwner should return storage[1]");
    }

    /**
     * Property: getOwner_preserves_state
     * Theorem: getOwner is a pure read that doesn't modify state
     */
    function testProperty_GetOwner_PreservesState() public {
        uint256 supplyBefore = readStorage(2);
        address ownerBefore = readStorageAddr(0);

        (bool success,) = token.call(abi.encodeWithSignature("owner()"));
        require(success);

        assertEq(readStorage(2), supplyBefore, "Supply unchanged");
        assertEq(readStorageAddr(0), ownerBefore, "Owner unchanged");
    }

    /**
     * Property: balanceOf_returns_balance
     * Property: balanceOf_meets_spec
     * Theorem: balanceOf(addr) returns the mapping value for addr
     */
    function testProperty_BalanceOf_ReturnsBalance() public {
        // Mint some tokens to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);
        uint256 balance = abi.decode(data, (uint256));
        assertEq(balance, 100, "balanceOf should return minted amount");
    }

    /**
     * Property: balanceOf_preserves_state
     * Theorem: balanceOf is a pure read that doesn't modify state
     */
    function testProperty_BalanceOf_PreservesState() public {
        uint256 supplyBefore = readStorage(2);
        address ownerBefore = readStorageAddr(0);

        (bool success,) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);

        assertEq(readStorage(2), supplyBefore, "Supply unchanged");
        assertEq(readStorageAddr(0), ownerBefore, "Owner unchanged");
    }

    /**
     * Property: mint_increases_balance
     * Property: mint_meets_spec_when_owner
     * Theorem: mint(to, amount) increases balanceOf(to) by amount
     */
    function testProperty_Mint_IncreasesBalance() public {
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("balanceOf(address)", bob));
        require(success);
        uint256 balanceBefore = abi.decode(data, (uint256));

        vm.prank(owner);
        (success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", bob, 50));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", bob));
        require(success);
        uint256 balanceAfter = abi.decode(data, (uint256));

        assertEq(balanceAfter, balanceBefore + 50, "Balance should increase by mint amount");
    }

    /**
     * Property: mint_increases_supply
     * Theorem: mint(to, amount) increases totalSupply by amount
     */
    function testProperty_Mint_IncreasesTotalSupply() public {
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyBefore = abi.decode(data, (uint256));

        vm.prank(owner);
        (success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 75));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyAfter = abi.decode(data, (uint256));

        assertEq(supplyAfter, supplyBefore + 75, "Total supply should increase by mint amount");
    }

    /**
     * Property: mint_reverts_when_not_owner
     * Theorem: mint called by non-owner reverts
     */
    function testProperty_Mint_RevertsWhenNotOwner() public {
        vm.prank(bob);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", bob, 100));
        assertFalse(success, "Mint should revert for non-owner");
    }

    /**
     * Property: mint_reverts_balance_overflow
     * Theorem: mint reverts when recipient balance + amount would overflow uint256
     */
    function testProperty_Mint_RevertsBalanceOverflow() public {
        // First mint near-max to bob
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", bob, MAX_UINT256));
        require(success, "First mint should succeed");

        // Second mint to bob should overflow the balance
        vm.prank(owner);
        (success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", bob, 1));
        assertFalse(success, "Mint should revert on balance overflow");
    }

    /**
     * Property: mint_reverts_supply_overflow
     * Theorem: mint reverts when totalSupply + amount would overflow uint256
     */
    function testProperty_Mint_RevertsSupplyOverflow() public {
        // Mint max to alice (balance = MAX, supply = MAX)
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, MAX_UINT256));
        require(success, "First mint should succeed");

        // Mint 1 to bob — bob's balance won't overflow, but totalSupply will
        vm.prank(owner);
        (success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", bob, 1));
        assertFalse(success, "Mint should revert on supply overflow");
    }

    /**
     * Property: mint_preserves_owner
     * Theorem: mint doesn't change the owner address
     */
    function testProperty_Mint_PreservesOwner() public {
        address ownerBefore = readStorageAddr(0);

        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        assertEq(readStorageAddr(0), ownerBefore, "Owner should be preserved");
    }

    /**
     * Property: mint_then_balanceOf_correct
     * Theorem: After mint(to, amount), balanceOf(to) reflects the increase
     */
    function testProperty_MintThenBalanceOf_Correct() public {
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", charlie, 200));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", charlie));
        require(success);
        uint256 balance = abi.decode(data, (uint256));

        assertEq(balance, 200, "balanceOf should return minted amount");
    }

    /**
     * Property: mint_then_getTotalSupply_correct
     * Theorem: After mint(to, amount), getTotalSupply reflects the increase
     */
    function testProperty_MintThenGetTotalSupply_Correct() public {
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyBefore = abi.decode(data, (uint256));

        vm.prank(owner);
        (success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 150));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyAfter = abi.decode(data, (uint256));

        assertEq(supplyAfter, supplyBefore + 150, "Total supply should reflect mint");
    }

    /**
     * Property: transfer_decreases_sender_balance
     * Property: transfer_meets_spec_when_sufficient
     * Theorem: transfer(to, amount) decreases sender balance by amount
     */
    function testProperty_Transfer_DecreasesSenderBalance() public {
        // Setup: mint to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);
        uint256 balanceBefore = abi.decode(data, (uint256));

        // Transfer from alice to bob
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 30));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);
        uint256 balanceAfter = abi.decode(data, (uint256));

        assertEq(balanceAfter, balanceBefore - 30, "Sender balance should decrease");
    }

    /**
     * Property: transfer_increases_recipient_balance
     * Theorem: transfer(to, amount) increases recipient balance by amount
     */
    function testProperty_Transfer_IncreasesRecipientBalance() public {
        // Setup: mint to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", bob));
        require(success);
        uint256 bobBalanceBefore = abi.decode(data, (uint256));

        // Transfer from alice to bob
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 40));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", bob));
        require(success);
        uint256 bobBalanceAfter = abi.decode(data, (uint256));

        assertEq(bobBalanceAfter, bobBalanceBefore + 40, "Recipient balance should increase");
    }

    /**
     * Property: transfer_self_preserves_balance
     * Theorem: transfer(to == sender, amount) leaves sender balance unchanged
     */
    function testProperty_Transfer_Self_PreservesBalance() public {
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", alice, 40));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);
        uint256 balance = abi.decode(data, (uint256));
        assertEq(balance, 100, "Self-transfer should not change balance");
    }

    /**
     * Property: transfer_preserves_supply_when_sufficient
     * Theorem: transfer doesn't change total supply
     */
    function testProperty_Transfer_PreservesTotalSupply() public {
        // Setup: mint to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyBefore = abi.decode(data, (uint256));

        // Transfer
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 50));
        require(success);

        (success, data) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);
        uint256 supplyAfter = abi.decode(data, (uint256));

        assertEq(supplyAfter, supplyBefore, "Total supply should be preserved");
    }

    /**
     * Property: transfer_reverts_recipient_overflow
     * Theorem: transfer reverts when recipient balance + amount would overflow uint256
     */
    function testProperty_Transfer_RevertsRecipientOverflow() public {
        // Use a fresh token to control total supply
        address freshToken = deployYulWithArgs("SimpleToken", abi.encode(owner));
        require(freshToken != address(0), "Deploy failed");

        // Mint MAX to bob so his balance is at max
        vm.prank(owner);
        (bool success,) = freshToken.call(abi.encodeWithSignature("mint(address,uint256)", bob, MAX_UINT256));
        require(success, "Mint to bob should succeed");

        // Directly set alice's balance via storage (bypass supply overflow check)
        bytes32 aliceSlot = keccak256(abi.encode(alice, uint256(1)));
        vm.store(freshToken, aliceSlot, bytes32(uint256(1)));

        // Alice tries to transfer 1 to bob — bob's balance would overflow
        vm.prank(alice);
        (success,) = freshToken.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 1));
        assertFalse(success, "Transfer should revert on recipient overflow");
    }

    /**
     * Property: transfer_reverts_insufficient_balance
     * Theorem: transfer reverts when sender balance < amount
     */
    function testProperty_Transfer_RevertsInsufficientBalance() public {
        // Alice has 0 tokens, tries to transfer 10
        vm.prank(alice);
        (bool success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 10));
        assertFalse(success, "Transfer should revert with insufficient balance");
    }

    /**
     * Property: transfer_preserves_owner
     * Theorem: transfer doesn't change the owner address
     */
    function testProperty_Transfer_PreservesOwner() public {
        // Setup: mint to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        address ownerBefore = readStorageAddr(0);

        // Transfer
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 20));
        require(success);

        assertEq(readStorageAddr(0), ownerBefore, "Owner should be preserved");
    }

    /**
     * Property: transfer_then_balanceOf_sender_correct
     * Theorem: After transfer, sender balanceOf is correctly reduced
     */
    function testProperty_TransferThenBalanceOf_SenderCorrect() public {
        // Mint 100 to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        // Transfer 25 to bob
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 25));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);
        uint256 balance = abi.decode(data, (uint256));

        assertEq(balance, 75, "Alice balance should be 75 after transfer");
    }

    /**
     * Property: transfer_then_balanceOf_recipient_correct
     * Theorem: After transfer, recipient balanceOf is correctly increased
     */
    function testProperty_TransferThenBalanceOf_RecipientCorrect() public {
        // Mint 100 to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        // Transfer 60 to charlie
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", charlie, 60));
        require(success);

        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", charlie));
        require(success);
        uint256 balance = abi.decode(data, (uint256));

        assertEq(balance, 60, "Charlie balance should be 60 after transfer");
    }

    /**
     * Property: constructor_preserves_wellformedness
     * Theorem: Constructor produces a well-formed state
     */
    function testProperty_Constructor_PreservesWellformedness() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(alice));
        address tokenOwner = readStorageAddr(newToken, 0);
        uint256 supply = readStorage(newToken, 2);

        assertEq(tokenOwner, alice, "Owner is set to initialOwner");
        assertEq(supply, 0, "Supply is 0");
    }

    /**
     * Property: constructor_establishes_supply_bounds
     * Theorem: Constructor initializes supply to 0 (establishes bounds)
     */
    function testProperty_Constructor_EstablishesSupplyBounds() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(owner));
        uint256 supply = readStorage(newToken, 2);

        assertEq(supply, 0, "Supply is 0 initially (upper bound established)");
    }

    /**
     * Property: getTotalSupply_preserves_wellformedness
     * Theorem: getTotalSupply maintains well-formed state
     */
    function testProperty_GetTotalSupply_PreservesWellformedness() public {
        (bool success,) = token.call(abi.encodeWithSignature("totalSupply()"));
        require(success);

        address tokenOwner = readStorageAddr(0);
        uint256 supply = readStorage(2);
        assertEq(tokenOwner, owner, "Owner preserved");
        assertEq(supply, 0, "Supply still 0 (read-only operation)");
    }

    /**
     * Property: getOwner_preserves_wellformedness
     * Theorem: getOwner maintains well-formed state
     */
    function testProperty_GetOwner_PreservesWellformedness() public {
        (bool success,) = token.call(abi.encodeWithSignature("owner()"));
        require(success);

        address tokenOwner = readStorageAddr(0);
        uint256 supply = readStorage(2);
        assertEq(tokenOwner, owner, "Owner preserved");
        assertEq(supply, 0, "Supply still 0 (read-only operation)");
    }

    /**
     * Property: balanceOf_preserves_wellformedness
     * Theorem: balanceOf maintains well-formed state
     */
    function testProperty_BalanceOf_PreservesWellformedness() public {
        (bool success,) = token.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(success);

        address tokenOwner = readStorageAddr(0);
        uint256 supply = readStorage(2);
        assertEq(tokenOwner, owner, "Owner preserved");
        assertEq(supply, 0, "Supply still 0 (read-only operation)");
    }

    /**
     * Property: mint_preserves_wellformedness
     * Theorem: mint maintains well-formed state
     */
    function testProperty_Mint_PreservesWellformedness() public {
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        address tokenOwner = readStorageAddr(0);
        uint256 supply = readStorage(2);
        assertEq(tokenOwner, owner, "Owner preserved");
        assertEq(supply, 100, "Supply increased to 100");
    }

    /**
     * Property: transfer_preserves_wellformedness
     * Theorem: transfer maintains well-formed state
     */
    function testProperty_Transfer_PreservesWellformedness() public {
        // Setup: mint to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        // Transfer
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 50));
        require(success);

        address tokenOwner = readStorageAddr(0);
        uint256 supply = readStorage(2);
        assertEq(tokenOwner, owner, "Owner still valid");
        assertEq(supply, 100, "Supply preserved");
    }

    /**
     * Property: constructor_owner_addr_isolated
     * Theorem: Constructor setting owner doesn't affect supply storage
     */
    function testProperty_Constructor_OwnerAddrIsolated() public {
        address token1 = deployYulWithArgs("SimpleToken", abi.encode(alice));
        address token2 = deployYulWithArgs("SimpleToken", abi.encode(bob));

        uint256 supply1 = readStorage(token1, 2);
        uint256 supply2 = readStorage(token2, 2);

        assertEq(supply1, 0, "Supply unchanged regardless of owner");
        assertEq(supply2, 0, "Supply unchanged regardless of owner");
    }

    /**
     * Property: constructor_supply_storage_isolated
     * Theorem: Constructor doesn't affect mapping storage
     */
    function testProperty_Constructor_SupplyStorageIsolated() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(alice));

        // Check that balance mapping slots are untouched
        bytes32 aliceBalanceSlot = keccak256(abi.encode(alice, uint256(1)));
        uint256 aliceBalance = uint256(vm.load(newToken, aliceBalanceSlot));

        assertEq(aliceBalance, 0, "Mapping storage isolated");
    }

    /**
     * Property: constructor_balance_mapping_isolated
     * Theorem: Constructor doesn't modify balance mapping
     */
    function testProperty_Constructor_BalanceMappingIsolated() public {
        address newToken = deployYulWithArgs("SimpleToken", abi.encode(owner));

        // Check various mapping slots are 0
        bytes32 slot1 = keccak256(abi.encode(alice, uint256(1)));
        bytes32 slot2 = keccak256(abi.encode(bob, uint256(1)));

        assertEq(uint256(vm.load(newToken, slot1)), 0, "Alice balance 0");
        assertEq(uint256(vm.load(newToken, slot2)), 0, "Bob balance 0");
    }

    /**
     * Property: mint_owner_addr_isolated
     * Theorem: mint doesn't modify owner storage
     */
    function testProperty_Mint_OwnerAddrIsolated() public {
        address ownerBefore = readStorageAddr(0);

        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        assertEq(readStorageAddr(0), ownerBefore, "Owner storage isolated");
    }

    /**
     * Property: mint_supply_storage_isolated
     * Theorem: mint updates supply but not other non-balance storage
     */
    function testProperty_Mint_SupplyStorageIsolated() public {
        address ownerBefore = readStorageAddr(0);

        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", bob, 50));
        require(success);

        // Owner slot should be unchanged
        assertEq(readStorageAddr(0), ownerBefore, "Non-supply storage isolated");
    }

    /**
     * Property: mint_balance_mapping_isolated
     * Theorem: mint to one address doesn't affect other addresses' balances
     */
    function testProperty_Mint_BalanceMappingIsolated() public {
        // Get charlie's balance before
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("balanceOf(address)", charlie));
        require(success);
        uint256 charlieBefore = abi.decode(data, (uint256));

        // Mint to alice
        vm.prank(owner);
        (success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        // Charlie's balance should be unchanged
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", charlie));
        require(success);
        uint256 charlieAfter = abi.decode(data, (uint256));

        assertEq(charlieAfter, charlieBefore, "Other balances isolated");
    }

    /**
     * Property: transfer_owner_addr_isolated
     * Theorem: transfer doesn't modify owner storage
     */
    function testProperty_Transfer_OwnerAddrIsolated() public {
        // Setup
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        address ownerBefore = readStorageAddr(0);

        // Transfer
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 30));
        require(success);

        assertEq(readStorageAddr(0), ownerBefore, "Owner storage isolated");
    }

    /**
     * Property: transfer_supply_storage_isolated
     * Theorem: transfer doesn't modify supply storage
     */
    function testProperty_Transfer_SupplyStorageIsolated() public {
        // Setup
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        uint256 supplyBefore = readStorage(2);

        // Transfer
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 40));
        require(success);

        assertEq(readStorage(2), supplyBefore, "Supply storage isolated");
    }

    /**
     * Property: transfer_balance_mapping_isolated
     * Theorem: transfer between two addresses doesn't affect third party balances
     */
    function testProperty_Transfer_BalanceMappingIsolated() public {
        // Setup: mint to alice and charlie
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        require(success);

        vm.prank(owner);
        (success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", charlie, 50));
        require(success);

        // Get charlie's balance before
        bytes memory data;
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", charlie));
        require(success);
        uint256 charlieBefore = abi.decode(data, (uint256));

        // Transfer from alice to bob
        vm.prank(alice);
        (success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, 30));
        require(success);

        // Charlie's balance should be unchanged
        (success, data) = token.call(abi.encodeWithSignature("balanceOf(address)", charlie));
        require(success);
        uint256 charlieAfter = abi.decode(data, (uint256));

        assertEq(charlieAfter, charlieBefore, "Third party balances isolated");
    }

    /**
     * Property: isOwner_true_when_owner
     * Theorem: isOwner returns true when caller is the owner
     * Note: SimpleToken doesn't expose isOwner, but we can test ownership via mint access control
     */
    function testProperty_IsOwner_TrueWhenOwner() public {
        // Owner can mint (proves isOwner returns true for owner)
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, 100));
        assertTrue(success, "Owner can mint (isOwner check passes)");

        // Non-owner cannot mint (proves isOwner returns false for non-owner)
        vm.prank(bob);
        (success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", bob, 100));
        assertFalse(success, "Non-owner cannot mint (isOwner check fails)");
    }

    //═══════════════════════════════════════════════════════════════════════════
    // Conservation Properties (Sum Invariants)
    // Maps theorems from Verity/Proofs/SimpleToken/Supply.lean
    //═══════════════════════════════════════════════════════════════════════════

    /**
     * Property: mint_sum_equation
     * Theorem: For a list of unique addresses, minting to `to` increases the
     *          total balance sum by exactly `amount` (when `to` appears once).
     */
    function testProperty_Mint_SumEquation(uint256 amount) public {
        vm.assume(amount > 0 && amount <= type(uint256).max / 4);

        // Mint initial balances
        vm.prank(owner);
        (bool s1,) = token.call(abi.encodeWithSignature("mint(address,uint256)", bob, 200));
        require(s1);
        vm.prank(owner);
        (bool s2,) = token.call(abi.encodeWithSignature("mint(address,uint256)", charlie, 300));
        require(s2);

        // Read balances before
        uint256 sumBefore = getBalance(alice) + getBalance(bob) + getBalance(charlie);

        // Mint to alice
        vm.prank(owner);
        (bool success,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, amount));
        require(success, "mint failed");

        uint256 sumAfter = getBalance(alice) + getBalance(bob) + getBalance(charlie);

        // Sum increases by exactly `amount` (alice appears once)
        assertEq(sumAfter, sumBefore + amount, "mint_sum_equation: sum should increase by amount");
    }

    /**
     * Property: transfer_sum_equation
     * Theorem: Transfer preserves the total balance sum across unique addresses.
     *          When sender and recipient each appear once, the sum is preserved.
     */
    function testProperty_Transfer_SumEquation(uint256 aliceAmount, uint256 transferAmount) public {
        vm.assume(aliceAmount > 0 && aliceAmount <= type(uint256).max / 4);
        vm.assume(transferAmount > 0 && transferAmount <= aliceAmount);

        // Set up balances via minting
        vm.prank(owner);
        (bool s1,) = token.call(abi.encodeWithSignature("mint(address,uint256)", alice, aliceAmount));
        require(s1);
        vm.prank(owner);
        (bool s2,) = token.call(abi.encodeWithSignature("mint(address,uint256)", bob, 200));
        require(s2);
        vm.prank(owner);
        (bool s3,) = token.call(abi.encodeWithSignature("mint(address,uint256)", charlie, 300));
        require(s3);

        uint256 sumBefore = getBalance(alice) + getBalance(bob) + getBalance(charlie);

        // Transfer from alice to bob
        vm.prank(alice);
        (bool success,) = token.call(abi.encodeWithSignature("transfer(address,uint256)", bob, transferAmount));
        require(success, "transfer failed");

        uint256 sumAfter = getBalance(alice) + getBalance(bob) + getBalance(charlie);

        // Sum is preserved exactly
        assertEq(sumAfter, sumBefore, "transfer_sum_equation: total sum should be preserved");
    }

    // Helper: read balance via contract call
    function getBalance(address addr) internal returns (uint256) {
        (bool success, bytes memory data) = token.call(abi.encodeWithSignature("balanceOf(address)", addr));
        require(success, "balanceOf failed");
        return abi.decode(data, (uint256));
    }

    // Helper functions
    function readStorageAddr(uint256 slot) internal view returns (address) {
        return readStorageAddr(token, slot);
    }

    function readStorageAddr(address target, uint256 slot) internal view returns (address) {
        bytes32 value = vm.load(target, bytes32(slot));
        return address(uint160(uint256(value)));
    }

    function readStorage(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(token, bytes32(slot)));
    }

    function readStorage(address target, uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(target, bytes32(slot)));
    }
}
