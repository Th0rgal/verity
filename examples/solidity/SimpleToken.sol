// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// @title SimpleToken
/// @notice Demonstrates pattern composition: Owned + Ledger (balances mapping)
/// @dev Minimal token contract with owner-controlled minting
contract SimpleToken {
    address public owner;
    mapping(address => uint256) public balances;
    uint256 public totalSupply;

    // Custom errors (gas-efficient)
    error NotOwner();
    error InsufficientBalance();

    /// @notice Initialize contract with owner
    /// @param initialOwner Address of the contract owner
    constructor(address initialOwner) {
        owner = initialOwner;
        totalSupply = 0;
    }

    /// @notice Modifier to restrict access to owner only
    modifier onlyOwner() {
        if (msg.sender != owner) {
            revert NotOwner();
        }
        _;
    }

    /// @notice Mint tokens to an address (owner-only)
    /// @param to Recipient address
    /// @param amount Amount to mint
    function mint(address to, uint256 amount) external onlyOwner {
        balances[to] += amount;
        totalSupply += amount;
    }

    /// @notice Transfer tokens from caller to another address
    /// @param to Recipient address
    /// @param amount Amount to transfer
    function transfer(address to, uint256 amount) external {
        if (balances[msg.sender] < amount) {
            revert InsufficientBalance();
        }
        balances[msg.sender] -= amount;
        balances[to] += amount;
    }

    /// @notice Get balance of an address
    /// @param addr Address to query
    /// @return Balance of the address
    function balanceOf(address addr) external view returns (uint256) {
        return balances[addr];
    }
}
