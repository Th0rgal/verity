// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// @title Ledger
/// @notice Demonstrates mapping storage pattern (Address → Uint256)
/// @dev Reference implementation matching the Lean EDSL Ledger example
contract Ledger {
    // Storage: balances mapping
    mapping(address => uint256) public balances;

    // Custom errors (gas-efficient)
    error InsufficientBalance();

    /// @notice Deposit amount to caller's balance
    /// @param amount Amount to deposit
    function deposit(uint256 amount) external {
        balances[msg.sender] += amount;
    }

    /// @notice Withdraw amount from caller's balance
    /// @param amount Amount to withdraw
    function withdraw(uint256 amount) external {
        if (balances[msg.sender] < amount) {
            revert InsufficientBalance();
        }
        balances[msg.sender] -= amount;
    }

    /// @notice Transfer amount from caller to another address
    /// @param to Recipient address
    /// @param amount Amount to transfer
    function transfer(address to, uint256 amount) external {
        if (balances[msg.sender] < amount) {
            revert InsufficientBalance();
        }
        if (msg.sender != to) {
            balances[msg.sender] -= amount;
            balances[to] += amount;
        }
    }

    /// @notice Get balance of any address
    /// @param addr Address to query
    /// @return Balance of the address
    function getBalance(address addr) external view returns (uint256) {
        return balances[addr];
    }
}
