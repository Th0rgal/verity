// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/**
 * @title Counter
 * @notice Readable reference implementation for the Lean EDSL example
 * @dev Solidity 0.8 uses checked arithmetic (reverts on overflow/underflow),
 *      while the Lean EDSL and compiled Yul use wrapping EVM arithmetic.
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
