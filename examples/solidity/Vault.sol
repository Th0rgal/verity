// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

/// @title Vault
/// @notice Minimal ERC4626-style vault with 1:1 asset/share accounting.
/// @dev Reference implementation matching `Contracts/Vault/Vault.lean`.
contract Vault {
    uint256 public totalAssets;
    uint256 public totalSupply;
    mapping(address => uint256) public shareBalances;

    error InsufficientShares();
    error InsufficientAssets();
    error InsufficientSupply();

    function deposit(uint256 assets) external {
        shareBalances[msg.sender] += assets;
        totalAssets += assets;
        totalSupply += assets;
    }

    function withdraw(uint256 shares) external {
        uint256 currentShares = shareBalances[msg.sender];
        if (currentShares < shares) {
            revert InsufficientShares();
        }
        if (totalAssets < shares) {
            revert InsufficientAssets();
        }
        if (totalSupply < shares) {
            revert InsufficientSupply();
        }

        shareBalances[msg.sender] = currentShares - shares;
        totalAssets -= shares;
        totalSupply -= shares;
    }

    function balanceOf(address account) external view returns (uint256) {
        return shareBalances[account];
    }
}
