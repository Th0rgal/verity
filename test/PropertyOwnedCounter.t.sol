// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyOwnedCounterTest
 * @notice Property-based tests extracted from formally verified Lean theorems
 * @dev Maps theorems from Verity/Proofs/OwnedCounter/*.lean to executable tests
 *
 * This file extracts 48 proven theorems into Foundry property tests:
 * - Basic properties (correctness, state preservation)
 * - Isolation properties (field independence, context preservation)
 * - Access control properties (owner-only operations)
 * - Integration properties (multi-step operations)
 */
contract PropertyOwnedCounterTest is YulTestBase {
    address ownedCounter;
    address alice = address(0xA11CE);
    address bob = address(0xB0B);

    function setUp() public {
        // Deploy OwnedCounter with alice as initial owner
        vm.prank(alice);
        ownedCounter = deployYulWithArgs("OwnedCounter", abi.encode(alice));
        require(ownedCounter != address(0), "Deploy failed");
    }

    /**
     * Property: constructor_sets_owner
     * Property: constructor_meets_spec
     * Theorem: Constructor correctly sets the owner to initialOwner parameter
     */
    function testProperty_Constructor_SetsOwner() public {
        address newContract = deployYulWithArgs("OwnedCounter", abi.encode(bob));
        (bool success, bytes memory data) = newContract.call(abi.encodeWithSignature("getOwner()"));
        require(success, "getOwner failed");
        address owner = abi.decode(data, (address));
        assertEq(owner, bob, "Owner should be bob");
    }

    /**
     * Property: constructor_preserves_count
     * Theorem: Constructor initializes count to 0
     */
    function testProperty_Constructor_InitializesCountToZero() public {
        address newContract = deployYulWithArgs("OwnedCounter", abi.encode(alice));
        uint256 count = readStorage(newContract, 1);
        assertEq(count, 0, "Count should be 0 afterValue construction");
    }

    /**
     * Property: getCount_returns_count
     * Property: getCount_meets_spec
     * Theorem: getCount() returns the value in storage slot 1
     */
    function testProperty_GetCount_ReturnsStorageValue() public {
        uint256 storageValue = readStorage(1);
        (bool success, bytes memory data) = ownedCounter.call(abi.encodeWithSignature("getCount()"));
        require(success);
        uint256 returned = abi.decode(data, (uint256));
        assertEq(returned, storageValue, "getCount should return storage[1]");
    }

    /**
     * Property: getCount_preserves_state
     * Theorem: getCount() is a pure read that doesn't modify state
     */
    function testProperty_GetCount_PreservesState() public {
        uint256 countBefore = readStorage(1);
        address ownerBefore = readStorageAddr(0);

        (bool success,) = ownedCounter.call(abi.encodeWithSignature("getCount()"));
        require(success);

        assertEq(readStorage(1), countBefore, "Count unchanged");
        assertEq(readStorageAddr(0), ownerBefore, "Owner unchanged");
    }

    /**
     * Property: getOwner_returns_owner
     * Property: getOwner_meets_spec
     * Theorem: getOwner() returns the value in storage slot 0
     */
    function testProperty_GetOwner_ReturnsStorageValue() public {
        address storageOwner = readStorageAddr(0);
        (bool success, bytes memory data) = ownedCounter.call(abi.encodeWithSignature("getOwner()"));
        require(success);
        address returned = abi.decode(data, (address));
        assertEq(returned, storageOwner, "getOwner should return storage[0]");
    }

    /**
     * Property: getOwner_preserves_state
     * Theorem: getOwner() is a pure read that doesn't modify state
     */
    function testProperty_GetOwner_PreservesState() public {
        uint256 countBefore = readStorage(1);
        address ownerBefore = readStorageAddr(0);

        (bool success,) = ownedCounter.call(abi.encodeWithSignature("getOwner()"));
        require(success);

        assertEq(readStorage(1), countBefore, "Count unchanged");
        assertEq(readStorageAddr(0), ownerBefore, "Owner unchanged");
    }

    /**
     * Property: increment_adds_one_when_owner
     * Property: increment_meets_spec_when_owner
     * Theorem: When called by owner, increment increases count by 1
     */
    function testProperty_Increment_AddsOneWhenOwner() public {
        uint256 countBefore = readStorage(1);

        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success, "increment should succeed for owner");

        assertEq(readStorage(1), countBefore + 1, "Count should increase by 1");
    }

    /**
     * Property: increment_reverts_when_not_owner
     * Theorem: When called by non-owner, increment reverts
     */
    function testProperty_Increment_RevertsWhenNotOwner() public {
        vm.prank(bob);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        assertFalse(success, "increment should revert for non-owner");
    }

    /**
     * Property: increment_preserves_owner
     * Property: increment_count_preserves_owner
     * Theorem: increment() doesn't modify the owner field
     */
    function testProperty_Increment_PreservesOwner() public {
        address ownerBefore = readStorageAddr(0);

        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        assertEq(readStorageAddr(0), ownerBefore, "Owner should be preserved");
    }

    /**
     * Property: decrement_subtracts_one_when_owner
     * Property: decrement_meets_spec_when_owner
     * Theorem: When called by owner, decrement decreases count by 1
     */
    function testProperty_Decrement_SubtractsOneWhenOwner() public {
        // Setup: increment first to have non-zero count
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        uint256 countBefore = readStorage(1);

        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("decrement()"));
        require(success, "decrement should succeed for owner");

        assertEq(readStorage(1), countBefore - 1, "Count should decrease by 1");
    }

    /**
     * Property: decrement_reverts_when_not_owner
     * Theorem: When called by non-owner, decrement reverts
     */
    function testProperty_Decrement_RevertsWhenNotOwner() public {
        vm.prank(bob);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("decrement()"));
        assertFalse(success, "decrement should revert for non-owner");
    }

    /**
     * Property: decrement_preserves_owner
     * Property: decrement_count_preserves_owner
     * Theorem: decrement() doesn't modify the owner field
     */
    function testProperty_Decrement_PreservesOwner() public {
        // Setup: increment first
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        address ownerBefore = readStorageAddr(0);

        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("decrement()"));
        require(success);

        assertEq(readStorageAddr(0), ownerBefore, "Owner should be preserved");
    }

    /**
     * Property: transferOwnership_changes_owner
     * Property: transferOwnership_meets_spec_when_owner
     * Theorem: transferOwnership updates the owner to newOwner
     */
    function testProperty_TransferOwnership_ChangesOwner() public {
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success, "transferOwnership should succeed for owner");

        assertEq(readStorageAddr(0), bob, "Owner should be bob");
    }

    /**
     * Property: transferOwnership_reverts_when_not_owner
     * Theorem: When called by non-owner, transferOwnership reverts
     */
    function testProperty_TransferOwnership_RevertsWhenNotOwner() public {
        vm.prank(bob);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        assertFalse(success, "transferOwnership should revert for non-owner");
    }

    /**
     * Property: transferOwnership_preserves_count
     * Property: transferOwnership_owner_preserves_count
     * Theorem: transferOwnership doesn't modify the count field
     */
    function testProperty_TransferOwnership_PreservesCount() public {
        uint256 countBefore = readStorage(1);

        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        assertEq(readStorage(1), countBefore, "Count should be preserved");
    }

    /**
     * Property: transfer_then_increment_reverts
     * Theorem: After transferring ownership, old owner can't increment
     */
    function testProperty_TransferThenIncrement_Reverts() public {
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        assertFalse(success, "Old owner should not be able to increment");
    }

    /**
     * Property: transfer_then_decrement_reverts
     * Theorem: After transferring ownership, old owner can't decrement
     */
    function testProperty_TransferThenDecrement_Reverts() public {
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("decrement()"));
        assertFalse(success, "Old owner should not be able to decrement");
    }

    /**
     * Property: increment_survives_transfer
     * Theorem: increment by owner, transfer, increment by new owner = count increased by 2
     */
    function testProperty_IncrementSurvivesTransfer() public {
        uint256 initialCount = readStorage(1);

        // Alice increments
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        // Alice transfers to Bob
        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        // Bob increments
        vm.prank(bob);
        (success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        assertEq(readStorage(1), initialCount + 2, "Count should increase by 2 across ownership transfer");
    }

    /**
     * Property: constructor_increment_getCount
     * Theorem: Fresh contract + increment + getCount returns 1
     */
    function testProperty_ConstructorIncrementGetCount() public {
        address newContract = deployYulWithArgs("OwnedCounter", abi.encode(alice));

        vm.prank(alice);
        (bool success,) = newContract.call(abi.encodeWithSignature("increment()"));
        require(success);

        bytes memory data;
        (success, data) = newContract.call(abi.encodeWithSignature("getCount()"));
        require(success);
        uint256 count = abi.decode(data, (uint256));

        assertEq(count, 1, "Count should be 1 afterValue construction + increment");
    }

    /**
     * Property: constructor_preserves_wellformedness
     * Theorem: Constructor produces a well-formed state (owner is set correctly, count is 0)
     */
    function testProperty_Constructor_PreservesWellformedness() public {
        address newContract = deployYulWithArgs("OwnedCounter", abi.encode(alice));
        address owner = readStorageAddr(newContract, 0);
        uint256 count = readStorage(newContract, 1);

        assertEq(owner, alice, "Owner is set to initialOwner");
        assertEq(count, 0, "Count is initialized to 0");
    }

    /**
     * Property: constructor_owner_preserves_count
     * Theorem: Constructor setting owner doesn't affect count (it's always 0)
     */
    function testProperty_Constructor_OwnerPreservesCount() public {
        address contract1 = deployYulWithArgs("OwnedCounter", abi.encode(alice));
        address contract2 = deployYulWithArgs("OwnedCounter", abi.encode(bob));

        assertEq(readStorage(contract1, 1), 0, "Count is 0 regardless of owner");
        assertEq(readStorage(contract2, 1), 0, "Count is 0 regardless of owner");
    }

    /**
     * Property: increment_preserves_wellformedness
     * Theorem: increment maintains well-formed state
     */
    function testProperty_Increment_PreservesWellformedness() public {
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        address owner = readStorageAddr(0);
        uint256 count = readStorage(1);
        assertEq(owner, alice, "Owner preserved");
        assertEq(count, 1, "Count increased to 1");
    }

    /**
     * Property: decrement_preserves_wellformedness
     * Theorem: decrement maintains well-formed state
     */
    function testProperty_Decrement_PreservesWellformedness() public {
        // Setup: increment first
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("decrement()"));
        require(success);

        address owner = readStorageAddr(0);
        uint256 count = readStorage(1);
        assertEq(owner, alice, "Owner preserved");
        assertEq(count, 0, "Count back to 0");
    }

    /**
     * Property: transferOwnership_preserves_wellformedness
     * Theorem: transferOwnership maintains well-formed state
     */
    function testProperty_TransferOwnership_PreservesWellformedness() public {
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        address owner = readStorageAddr(0);
        uint256 count = readStorage(1);
        assertEq(owner, bob, "New owner is valid");
        assertEq(count, 0, "Count preserved");
    }

    /**
     * Property: getCount_context_preserved
     * Theorem: getCount() doesn't modify msg.sender or other context
     * Note: In EVM, view functions can't modify context, verified by calling from different senders
     */
    function testProperty_GetCount_ContextPreserved() public {
        vm.prank(alice);
        (bool success1, bytes memory data1) = ownedCounter.call(abi.encodeWithSignature("getCount()"));
        require(success1);

        vm.prank(bob);
        (bool success2, bytes memory data2) = ownedCounter.call(abi.encodeWithSignature("getCount()"));
        require(success2);

        assertEq(data1, data2, "getCount returns same value regardless of caller");
    }

    /**
     * Property: getOwner_context_preserved
     * Theorem: getOwner() doesn't modify msg.sender or other context
     */
    function testProperty_GetOwner_ContextPreserved() public {
        vm.prank(alice);
        (bool success1, bytes memory data1) = ownedCounter.call(abi.encodeWithSignature("getOwner()"));
        require(success1);

        vm.prank(bob);
        (bool success2, bytes memory data2) = ownedCounter.call(abi.encodeWithSignature("getOwner()"));
        require(success2);

        assertEq(data1, data2, "getOwner returns same value regardless of caller");
    }

    /**
     * Property: constructor_context_preserved
     * Theorem: Constructor preserves msg.sender context (initialOwner param sets owner, not msg.sender)
     */
    function testProperty_Constructor_ContextPreserved() public {
        // Deploy from alice, but set bob as owner
        vm.prank(alice);
        address newContract = deployYulWithArgs("OwnedCounter", abi.encode(bob));
        address owner = readStorageAddr(newContract, 0);

        assertEq(owner, bob, "Owner is constructor param, not msg.sender");
    }

    /**
     * Property: increment_context_preserved
     * Theorem: increment preserves context fields (doesn't modify msg.sender stored state)
     * Note: OwnedCounter doesn't store msg.sender, verified by checking only owner/count change
     */
    function testProperty_Increment_ContextPreserved() public {
        // Record state before
        address ownerBefore = readStorageAddr(0);

        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        // Only count should change, owner (which is the stored context) unchanged
        assertEq(readStorageAddr(0), ownerBefore, "Context (owner) preserved");
    }

    /**
     * Property: decrement_context_preserved
     * Theorem: decrement preserves context fields
     */
    function testProperty_Decrement_ContextPreserved() public {
        // Setup
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        address ownerBefore = readStorageAddr(0);

        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("decrement()"));
        require(success);

        assertEq(readStorageAddr(0), ownerBefore, "Context (owner) preserved");
    }

    /**
     * Property: transferOwnership_context_preserved
     * Theorem: transferOwnership preserves context fields (count unchanged, new owner is intentional)
     */
    function testProperty_TransferOwnership_ContextPreserved() public {
        uint256 countBefore = readStorage(1);

        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        assertEq(readStorage(1), countBefore, "Count (context) preserved");
    }

    /**
     * Property: constructor_preserves_map_storage
     * Theorem: Constructor doesn't use mapping storage (only slots 0 and 1)
     */
    function testProperty_Constructor_PreservesMapStorage() public {
        address newContract = deployYulWithArgs("OwnedCounter", abi.encode(alice));

        // OwnedCounter doesn't use mappings, so keccak256-based slots should be 0
        bytes32 mappingSlot = keccak256(abi.encode(alice, uint256(0)));
        uint256 mappingValue = uint256(vm.load(newContract, mappingSlot));
        assertEq(mappingValue, 0, "No mapping storage used");
    }

    /**
     * Property: increment_preserves_map_storage
     * Theorem: increment doesn't modify mapping storage
     */
    function testProperty_Increment_PreservesMapStorage() public {
        // OwnedCounter doesn't use mappings
        bytes32 mappingSlot = keccak256(abi.encode(alice, uint256(0)));
        uint256 before = uint256(vm.load(ownedCounter, mappingSlot));

        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        uint256 afterValue = uint256(vm.load(ownedCounter, mappingSlot));
        assertEq(afterValue, before, "Mapping storage unchanged");
    }

    /**
     * Property: decrement_preserves_map_storage
     * Theorem: decrement doesn't modify mapping storage
     */
    function testProperty_Decrement_PreservesMapStorage() public {
        // Setup
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("increment()"));
        require(success);

        bytes32 mappingSlot = keccak256(abi.encode(alice, uint256(0)));
        uint256 before = uint256(vm.load(ownedCounter, mappingSlot));

        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("decrement()"));
        require(success);

        uint256 afterValue = uint256(vm.load(ownedCounter, mappingSlot));
        assertEq(afterValue, before, "Mapping storage unchanged");
    }

    /**
     * Property: transferOwnership_preserves_map_storage
     * Theorem: transferOwnership doesn't modify mapping storage
     */
    function testProperty_TransferOwnership_PreservesMapStorage() public {
        bytes32 mappingSlot = keccak256(abi.encode(alice, uint256(0)));
        uint256 before = uint256(vm.load(ownedCounter, mappingSlot));

        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        uint256 afterValue = uint256(vm.load(ownedCounter, mappingSlot));
        assertEq(afterValue, before, "Mapping storage unchanged");
    }

    /**
     * Property: transfer_then_transfer_reverts
     * Theorem: After transferring ownership twice, original owner can't transfer again
     */
    function testProperty_TransferThenTransferReverts() public {
        // Alice transfers to Bob
        vm.prank(alice);
        (bool success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", bob));
        require(success);

        // Bob transfers to alice (alice is original owner)
        address charlie = address(0xCC);
        vm.prank(bob);
        (success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", charlie));
        require(success);

        // Alice (now non-owner) tries to transfer - should revert
        vm.prank(alice);
        (success,) = ownedCounter.call(abi.encodeWithSignature("transferOwnership(address)", alice));
        assertFalse(success, "Original owner can't transfer afterValue double transfer");
    }

    // Helper function to read address from storage
    function readStorageAddr(uint256 slot) internal view returns (address) {
        return readStorageAddr(ownedCounter, slot);
    }

    function readStorageAddr(address target, uint256 slot) internal view returns (address) {
        bytes32 value = vm.load(target, bytes32(slot));
        return address(uint160(uint256(value)));
    }

    function readStorage(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(ownedCounter, bytes32(slot)));
    }

    function readStorage(address target, uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(target, bytes32(slot)));
    }
}
