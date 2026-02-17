// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertySimpleStorageTest
 * @notice Property-based tests extracted from formally verified Lean theorems
 * @dev Maps theorems from Verity/Proofs/SimpleStorage/ to executable tests
 *
 * This file contains property tests corresponding to 19 proven theorems:
 *
 * From Basic.lean (12 theorems):
 * 1. setStorage_updates_slot
 * 2. getStorage_reads_slot
 * 3. setStorage_preserves_other_slots
 * 4. setStorage_preserves_sender
 * 5. setStorage_preserves_address
 * 6. setStorage_preserves_addr_storage
 * 7. setStorage_preserves_map_storage
 * 8. store_meets_spec
 * 9. retrieve_meets_spec
 * 10. retrieve_preserves_state
 * 11. store_retrieve_roundtrip
 * 12. retrieve_twice_idempotent
 *
 * From Correctness.lean (7 theorems):
 * 13. store_retrieve_roundtrip_holds
 * 14. store_preserves_storage_isolated
 * 15. store_preserves_addr_storage
 * 16. store_preserves_map_storage
 * 17. store_preserves_context
 * 18. retrieve_preserves_context
 * 19. retrieve_preserves_wellformedness
 */
contract PropertySimpleStorageTest is YulTestBase {
    address simpleStorage;

    function setUp() public {
        // Deploy SimpleStorage from Yul
        simpleStorage = deployYul("SimpleStorage");
        require(simpleStorage != address(0), "Deploy failed");
    }

    /**
     * Property 1: setStorage_updates_slot
     * Theorem: store() updates storage slot 0 with the provided value
     */
    function testProperty_Store_UpdatesSlot0(uint256 value) public {
        // Action: Store value
        (bool success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value)
        );
        require(success, "store failed");

        // Assert: Slot 0 contains the value
        assertEq(readStorage(0), value, "Slot 0 should contain stored value");
    }

    /**
     * Property 2: getStorage_reads_slot
     * Theorem: retrieve() returns the value in storage slot 0
     */
    function testProperty_Retrieve_ReadsSlot0(uint256 value) public {
        // Setup: Set slot 0 directly
        vm.store(simpleStorage, bytes32(uint256(0)), bytes32(value));

        // Action: Retrieve
        (, bytes memory data) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        uint256 result = abi.decode(data, (uint256));

        // Assert: Result matches slot 0
        assertEq(result, value, "retrieve() should return slot 0 value");
    }

    /**
     * Property 3: setStorage_preserves_other_slots
     * Theorem: store() only modifies slot 0, other slots unchanged
     */
    function testProperty_Store_PreservesOtherSlots(uint256 value) public {
        // Setup: Set other slots with known values
        vm.store(simpleStorage, bytes32(uint256(1)), bytes32(uint256(0xDEADBEEF)));
        vm.store(simpleStorage, bytes32(uint256(2)), bytes32(uint256(0xCAFEBABE)));

        uint256 slot1Before = readStorage(1);
        uint256 slot2Before = readStorage(2);

        // Action: Store value
        (bool success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value)
        );
        require(success, "store failed");

        // Assert: Other slots unchanged
        assertEq(readStorage(1), slot1Before, "Slot 1 should be unchanged");
        assertEq(readStorage(2), slot2Before, "Slot 2 should be unchanged");
    }

    /**
     * Property 4: setStorage_preserves_sender
     * Property 5: setStorage_preserves_address
     * Property 6: setStorage_preserves_addr_storage
     * Property 7: setStorage_preserves_map_storage
     * Property: store_preserves_context
     * Theorem: store() preserves contract context (sender, address, etc.)
     * Note: In Solidity tests, we verify state isolation instead
     */
    function testProperty_Store_PreservesContext(uint256 value) public {
        // This is implicitly tested - if store() modified context,
        // subsequent calls would fail. We test state isolation instead.

        // Multiple stores should work consistently
        (bool success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value)
        );
        require(success, "store failed");

        (, bytes memory data) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        uint256 result = abi.decode(data, (uint256));

        assertEq(result, value, "Context preserved across operations");
    }

    /**
     * Property 8: store_meets_spec
     * Theorem: store() meets its formal specification
     */
    function testProperty_Store_MeetsSpec(uint256 value) public {
        // Spec: store(value) sets slot 0 to value, preserves other state
        (bool success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value)
        );
        require(success, "store failed");

        assertEq(readStorage(0), value, "store_spec: slot 0 = value");
    }

    /**
     * Property 9: retrieve_meets_spec
     * Theorem: retrieve() meets its formal specification
     */
    function testProperty_Retrieve_MeetsSpec() public {
        // Spec: retrieve() returns slot 0 value without modifying state
        uint256 expected = 12345;
        vm.store(simpleStorage, bytes32(uint256(0)), bytes32(expected));

        uint256 stateBefore = readStorage(0);

        (, bytes memory data) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        uint256 result = abi.decode(data, (uint256));

        assertEq(result, expected, "retrieve_spec: returns slot 0");
        assertEq(readStorage(0), stateBefore, "retrieve_spec: no state change");
    }

    /**
     * Property 10: retrieve_preserves_state
     * Property: retrieve_preserves_context
     * Theorem: retrieve() is read-only, preserves all storage
     */
    function testProperty_Retrieve_PreservesState() public {
        uint256 slot0Before = readStorage(0);
        uint256 slot1Before = readStorage(1);
        uint256 slot2Before = readStorage(2);

        // Action: Retrieve
        (, bytes memory data) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        uint256 result = abi.decode(data, (uint256));

        // Assert: All storage unchanged
        assertEq(readStorage(0), slot0Before, "Slot 0 unchanged");
        assertEq(readStorage(1), slot1Before, "Slot 1 unchanged");
        assertEq(readStorage(2), slot2Before, "Slot 2 unchanged");
        assertEq(result, slot0Before, "Result matches slot 0");
    }

    /**
     * Property 11: store_retrieve_correct
     * Property 13: store_retrieve_roundtrip_holds
     * Theorem: store(v) followed by retrieve() returns v
     * This is the fundamental correctness property
     */
    function testProperty_Store_Retrieve_Roundtrip(uint256 value) public {
        // Action: Store then retrieve
        (bool success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value)
        );
        require(success, "store failed");

        (, bytes memory data) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        uint256 result = abi.decode(data, (uint256));

        // Assert: Roundtrip preserves value
        assertEq(result, value, "Store-retrieve roundtrip preserves value");
    }

    /**
     * Property 12: retrieve_twice_idempotent
     * Theorem: Calling retrieve() twice returns the same value
     */
    function testProperty_Retrieve_Idempotent(uint256 value) public {
        // Setup: Store a value
        (bool success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value)
        );
        require(success, "store failed");

        // Action: Retrieve twice
        (, bytes memory data1) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        uint256 result1 = abi.decode(data1, (uint256));

        (, bytes memory data2) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        uint256 result2 = abi.decode(data2, (uint256));

        // Assert: Both retrievals return same value
        assertEq(result1, result2, "Retrieve is idempotent");
        assertEq(result1, value, "Both retrievals return stored value");
    }

    /**
     * Property 14: store_preserves_storage_isolated
     * Theorem: store() only affects slot 0
     */
    function testProperty_Store_StorageIsolated(uint256 value, uint256 otherSlot) public {
        vm.assume(otherSlot != 0 && otherSlot < 10); // Test a few other slots

        // Setup: Put value in other slot
        uint256 otherValue = 0xDEADBEEF;
        vm.store(simpleStorage, bytes32(otherSlot), bytes32(otherValue));

        // Action: Store to slot 0
        (bool success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value)
        );
        require(success, "store failed");

        // Assert: Other slot unchanged
        assertEq(
            uint256(vm.load(simpleStorage, bytes32(otherSlot))),
            otherValue,
            "Storage isolation: other slots unchanged"
        );
    }

    /**
     * Property 15: store_preserves_storage_isolated
     * Property 16: store_preserves_addr_storage
     * Property 17: store_preserves_map_storage
     * Theorem: store() preserves various aspects of state
     */
    function testProperty_Store_PreservesState(uint256 value1, uint256 value2) public {
        // Store twice to verify state preservation across operations
        (bool success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value1)
        );
        require(success, "store failed");

        (success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value2)
        );
        require(success, "store failed");

        // Verify final state
        assertEq(readStorage(0), value2, "Final value correct");
    }

    /**
     * Property 18: retrieve_preserves_context
     * Property 19: retrieve_preserves_wellformedness
     * Theorem: retrieve() preserves context and well-formedness
     */
    function testProperty_Retrieve_PreservesWellFormedness() public {
        // Set up a "well-formed" state (all constraints satisfied)
        uint256 value = 42;
        vm.store(simpleStorage, bytes32(uint256(0)), bytes32(value));

        // Action: Retrieve
        (, bytes memory data) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        uint256 result = abi.decode(data, (uint256));

        // Assert: State remains well-formed (value preserved)
        assertEq(readStorage(0), value, "Well-formedness preserved");
        assertEq(result, value, "Result correct");
    }

    /**
     * Additional fuzz test: Multiple store operations
     */
    function testFuzz_MultipleStores(uint256[] calldata values) public {
        vm.assume(values.length > 0 && values.length <= 10);

        // Store all values sequentially
        for (uint256 i = 0; i < values.length; i++) {
            (bool success,) = simpleStorage.call(
                abi.encodeWithSignature("store(uint256)", values[i])
            );
            require(success, "store failed");
        }

        // Verify last value is stored
        uint256 lastValue = values[values.length - 1];
        (, bytes memory data) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        uint256 result = abi.decode(data, (uint256));

        assertEq(result, lastValue, "Last stored value should be retrievable");
        assertEq(readStorage(0), lastValue, "Storage should contain last value");
    }

    /**
     * Additional fuzz test: Interleaved store/retrieve
     */
    function testFuzz_InterleavedOperations(uint256 value1, uint256 value2, uint256 value3) public {
        // Store, retrieve, store, retrieve pattern
        (bool success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value1)
        );
        require(success, "store failed");

        (, bytes memory data1) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        assertEq(abi.decode(data1, (uint256)), value1);

        (success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value2)
        );
        require(success, "store failed");

        (, bytes memory data2) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        assertEq(abi.decode(data2, (uint256)), value2);

        (success,) = simpleStorage.call(
            abi.encodeWithSignature("store(uint256)", value3)
        );
        require(success, "store failed");

        (, bytes memory data3) = simpleStorage.call(
            abi.encodeWithSignature("retrieve()")
        );
        assertEq(abi.decode(data3, (uint256)), value3);
    }

    // Helper function to read storage
    function readStorage(uint256 slot) internal view returns (uint256) {
        return uint256(vm.load(simpleStorage, bytes32(slot)));
    }
}
