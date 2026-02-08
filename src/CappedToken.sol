// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Minimal capped mint-only token for spec-to-constraints proof POC.
contract CappedToken {
    error ZeroAddress();
    error NotOwner();
    error CapExceeded();

    mapping(address => uint256) public balance;
    uint256 public totalSupply;
    uint256 public maxSupply;
    address public owner;

    constructor(address owner_, uint256 supply, uint256 maxSupply_) {
        if (owner_ == address(0)) revert ZeroAddress();
        if (supply > maxSupply_) revert CapExceeded();

        owner = owner_;
        totalSupply = supply;
        maxSupply = maxSupply_;
        balance[owner_] = supply;
    }

    function mint(uint256 amount) public {
        if (msg.sender != owner) revert NotOwner();
        if (totalSupply + amount > maxSupply) revert CapExceeded();

        unchecked {
            totalSupply += amount;
            balance[owner] += amount;
        }
    }
}
