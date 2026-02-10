// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/**
 * @title SimpleStorage
 * @notice Reference implementation matching the Lean EDSL example
 * @dev This contract demonstrates the simplest storage pattern
 */
contract SimpleStorage {
    uint256 private storedData;

    function store(uint256 value) public {
        storedData = value;
    }

    function retrieve() public view returns (uint256) {
        return storedData;
    }
}
