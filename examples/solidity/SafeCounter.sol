// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/**
 * @title SafeCounter
 * @notice Reference implementation matching the Lean EDSL example
 * @dev Demonstrates safe arithmetic with overflow/underflow protection
 *      Solidity 0.8+ has built-in overflow protection, so this contract
 *      naturally matches the safe semantics of the Lean version
 */
contract SafeCounter {
    uint256 private count;

    function increment() public {
        // Solidity 0.8+ reverts on overflow automatically
        count = count + 1;
    }

    function decrement() public {
        // Solidity 0.8+ reverts on underflow automatically
        count = count - 1;
    }

    function getCount() public view returns (uint256) {
        return count;
    }
}
