// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// @title VulnerableBank
/// @notice Demonstrates a reentrancy vulnerability where totalSupply is
///         decremented twice (modeling a reentrant callback) before the
///         balance is updated once. This breaks the supply invariant.
/// @dev Matches the Lean EDSL model in Verity/Examples/ReentrancyExample.lean
contract VulnerableBank {
    // Storage layout matches EDSL:
    // slot 0: reentrancyLock (unused in vulnerable version)
    // slot 1: totalSupply
    // slot 2: balances mapping base slot
    uint256 public reentrancyLock;
    uint256 public totalSupply;
    mapping(address => uint256) public balances;

    /// @notice Deposit amount to caller's balance
    function deposit(uint256 amount) external {
        balances[msg.sender] += amount;
        totalSupply += amount;
    }

    /// @notice Vulnerable withdraw: models reentrancy by decrementing
    ///         totalSupply twice (simulating reentrant callback) before
    ///         updating balance once.
    /// @dev This mirrors the Lean model where the external call effect is
    ///      inlined as a second totalSupply decrement.
    function withdraw(uint256 amount) external {
        require(balances[msg.sender] >= amount, "Insufficient balance");

        // Unchecked to match Lean's wrapping sub semantics (Uint256.sub wraps at 2^256)
        unchecked {
            // First totalSupply decrement (before "external call")
            totalSupply -= amount;

            // Reentrant call effect: totalSupply decremented again
            totalSupply -= amount;
        }

        // Balance updated once (using original balance check)
        balances[msg.sender] -= amount;
    }

    function getBalance(address addr) external view returns (uint256) {
        return balances[addr];
    }
}

/// @title SafeBank
/// @notice Demonstrates the fix: state is updated before any external
///         interaction. The supply invariant is provably maintained.
/// @dev Matches the Lean EDSL SafeBank model
contract SafeBank {
    uint256 public reentrancyLock;
    uint256 public totalSupply;
    mapping(address => uint256) public balances;

    /// @notice Deposit amount to caller's balance
    function deposit(uint256 amount) external {
        balances[msg.sender] += amount;
        totalSupply += amount;
    }

    /// @notice Safe withdraw: updates balance and totalSupply atomically
    ///         before any external interaction would occur.
    function withdraw(uint256 amount) external {
        require(balances[msg.sender] >= amount, "Insufficient balance");

        // State updates BEFORE external interaction
        balances[msg.sender] -= amount;
        totalSupply -= amount;
    }

    function getBalance(address addr) external view returns (uint256) {
        return balances[addr];
    }
}
