// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/**
 * @title Counter
 * @notice Reference implementation matching the Lean EDSL example
 * @dev Demonstrates basic arithmetic operations (increment/decrement)
 */
contract Counter {
    uint256 private count;

    function increment() public {
        count = count + 1;
    }

    function decrement() public {
        count = count - 1;
    }

    function getCount() public view returns (uint256) {
        return count;
    }
}
