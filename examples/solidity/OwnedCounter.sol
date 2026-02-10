// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/**
 * @title OwnedCounter
 * @notice Reference implementation matching the Lean EDSL example
 * @dev Demonstrates pattern composition: ownership + counter
 */
contract OwnedCounter {
    address private owner;
    uint256 private count;

    error NotOwner();

    modifier onlyOwner() {
        if (msg.sender != owner) revert NotOwner();
        _;
    }

    constructor(address initialOwner) {
        owner = initialOwner;
    }

    function increment() public onlyOwner {
        count = count + 1;
    }

    function decrement() public onlyOwner {
        count = count - 1;
    }

    function getCount() public view returns (uint256) {
        return count;
    }

    function getOwner() public view returns (address) {
        return owner;
    }

    function transferOwnership(address newOwner) public onlyOwner {
        owner = newOwner;
    }
}
