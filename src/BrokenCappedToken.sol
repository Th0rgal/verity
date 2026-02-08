// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Deliberately broken capped token for negative proof cases.
contract BrokenCappedToken {
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

        unchecked {
            totalSupply += amount * 2;
            balance[owner] += amount;
        }
    }
}
