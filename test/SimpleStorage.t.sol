// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "../examples/solidity/SimpleStorage.sol";

/**
 * @title SimpleStorageTest
 * @notice Tests for the SimpleStorage contract
 * @dev Validates that the Lean EDSL semantics match the Solidity implementation
 */
contract SimpleStorageTest is Test {
    SimpleStorage public simpleStorage;

    function setUp() public {
        simpleStorage = new SimpleStorage();
    }

    /// @notice Test initial state (should be 0)
    function test_InitialState() public {
        assertEq(simpleStorage.retrieve(), 0, "Initial value should be 0");
    }

    /// @notice Test storing and retrieving a value
    function test_StoreAndRetrieve() public {
        uint256 valueToStore = 42;
        simpleStorage.store(valueToStore);
        assertEq(simpleStorage.retrieve(), valueToStore, "Retrieved value should match stored value");
    }

    /// @notice Test updating a stored value
    function test_UpdateValue() public {
        simpleStorage.store(100);
        assertEq(simpleStorage.retrieve(), 100, "First value should be stored");

        simpleStorage.store(200);
        assertEq(simpleStorage.retrieve(), 200, "Value should be updated");
    }

    /// @notice Fuzz test: store and retrieve arbitrary values
    function testFuzz_StoreRetrieve(uint256 randomValue) public {
        simpleStorage.store(randomValue);
        assertEq(simpleStorage.retrieve(), randomValue, "Should store and retrieve any uint256 value");
    }
}
