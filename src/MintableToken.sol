// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Minimal mint-only token for spec-to-constraints proof POC.
contract MintableToken {
    error ZeroAddress();
    error NotOwner();

    mapping(address => uint256) public balance;
    uint256 public totalSupply;
    address public owner;

    constructor(address owner_, uint256 supply) {
        if (owner_ == address(0)) revert ZeroAddress();
        owner = owner_;
        totalSupply = supply;
        balance[owner_] = supply;
    }

    function mint(uint256 amount) public {
        if (msg.sender != owner) revert NotOwner();

        unchecked {
            totalSupply += amount;
            balance[owner] += amount;
        }
    }
}
