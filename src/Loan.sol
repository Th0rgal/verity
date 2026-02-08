// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Minimal loan contract used to validate the spec-compiler pipeline.
contract Loan {
    error HealthFactor();

    uint256 public immutable minHealthFactor;
    mapping(address => uint256) public collateral;
    mapping(address => uint256) public debt;

    /// @param minHealthFactor_ Scaled by 1e18 (e.g., 1.25e18 = 125%).
    constructor(uint256 minHealthFactor_) {
        minHealthFactor = minHealthFactor_;
    }

    function update(address user, uint256 newCollateral, uint256 newDebt) public {
        if (newDebt > 0) {
            if (newCollateral * 1e18 < newDebt * minHealthFactor) {
                revert HealthFactor();
            }
        }

        collateral[user] = newCollateral;
        debt[user] = newDebt;
    }
}
