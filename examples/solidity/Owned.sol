// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/**
 * @title Owned
 * @notice Reference implementation matching the Lean EDSL example
 * @dev Demonstrates ownership pattern and access control
 */
contract Owned {
    address private owner;

    error NotOwner();

    modifier onlyOwner() {
        if (msg.sender != owner) revert NotOwner();
        _;
    }

    constructor(address initialOwner) {
        owner = initialOwner;
    }

    function transferOwnership(address newOwner) public onlyOwner {
        owner = newOwner;
    }

    function getOwner() public view returns (address) {
        return owner;
    }
}
