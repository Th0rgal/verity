// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Deliberately broken transfer implementation for negative proof case.
contract BrokenSimpleToken {
    error ZeroAddress();
    error InsufficientBalance();

    mapping(address => uint256) public balance;
    uint256 public totalSupply;

    constructor(address owner, uint256 supply) {
        if (owner == address(0)) revert ZeroAddress();
        totalSupply = supply;
        balance[owner] = supply;
    }

    function transfer(address to, uint256 amount) public {
        if (to == address(0)) revert ZeroAddress();
        if (balance[msg.sender] < amount) revert InsufficientBalance();

        unchecked {
            balance[msg.sender] -= amount;
            // BUG: receiver balance not updated.
        }
    }
}
