// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

contract SelectorFixtures {
    function balanceOf(address account) external view returns (uint256) {
        return account == address(0) ? 0 : 1;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        return to != address(0) && amount > 0;
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        return spender != address(0) && amount > 0;
    }

    function mint(address to, uint256 amount) external returns (bool) {
        return to != address(0) && amount > 0;
    }

    function burn(address from, uint256 amount) external returns (bool) {
        return from != address(0) && amount > 0;
    }

    function transferBatch(
        address[] calldata recipients,
        uint256[] calldata amounts
    ) external pure returns (uint256) {
        return recipients.length + amounts.length;
    }

    function setRoots(bytes32[2] calldata roots) external pure returns (bytes32) {
        return roots[0];
    }

    function submit(bytes calldata blob) external pure returns (uint256) {
        return blob.length;
    }
}
