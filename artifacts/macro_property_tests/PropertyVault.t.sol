// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyVaultTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Vault/Vault.lean
 */
contract PropertyVaultTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("Vault");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: deposit has no unexpected revert
    function testAuto_Deposit_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("deposit(uint256)", uint256(1)));
        require(ok, "deposit reverted unexpectedly");
    }
    // Property 2: withdraw has no unexpected revert
    function testAuto_Withdraw_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("withdraw(uint256)", uint256(1)));
        require(ok, "withdraw reverted unexpectedly");
    }
    // Property 3: balanceOf reads the configured mapping value
    function testAuto_BalanceOf_ReadsConfiguredMapping() public {
        uint256 expected = uint256(1);
        vm.store(target, _mappingSlot(bytes32(uint256(uint160(alice))), 2), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(ok, "balanceOf reverted unexpectedly");
        assertEq(ret.length, 32, "balanceOf ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "balanceOf should decode the configured mapping value");
    }
    // Property 4: totalAssets reads storage slot 0 and decodes the result
    function testAuto_TotalAssets_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("totalAssets()"));
        require(ok, "totalAssets reverted unexpectedly");
        assertEq(ret.length, 32, "totalAssets ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "totalAssets should return storage slot 0");
    }
    // Property 5: totalSupply reads storage slot 1 and decodes the result
    function testAuto_TotalSupply_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(1)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("totalSupply()"));
        require(ok, "totalSupply reverted unexpectedly");
        assertEq(ret.length, 32, "totalSupply ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "totalSupply should return storage slot 1");
    }
}
