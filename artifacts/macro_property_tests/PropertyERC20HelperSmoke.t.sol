// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyERC20HelperSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyERC20HelperSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ERC20HelperSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: pushTokens has no unexpected revert
    function testAuto_PushTokens_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("pushTokens(address,address,uint256)", alice, alice, uint256(1)));
        require(ok, "pushTokens reverted unexpectedly");
    }
    // Property 2: pullTokens has no unexpected revert
    function testAuto_PullTokens_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("pullTokens(address,address,address,uint256)", alice, alice, alice, uint256(1)));
        require(ok, "pullTokens reverted unexpectedly");
    }
    // Property 3: approveTokens has no unexpected revert
    function testAuto_ApproveTokens_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("approveTokens(address,address,uint256)", alice, alice, uint256(1)));
        require(ok, "approveTokens reverted unexpectedly");
    }
    // Property 4: snapshotBalance decodes the mocked ERC20 balance read
    function testAuto_SnapshotBalance_ReturnsMockedBalanceRead() public {
        uint256 expected = uint256(1);
        vm.mockCall(alice, abi.encodeWithSignature("balanceOf(address)", alice), abi.encode(expected));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("snapshotBalance(address,address)", alice, alice));
        require(ok, "snapshotBalance reverted unexpectedly");
        assertEq(ret.length, 32, "snapshotBalance ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "snapshotBalance should return the mocked external read");
        assertEq(vm.load(target, bytes32(uint256(0))), bytes32(uint256(expected)), "snapshotBalance should persist the mocked external read");
    }
    // Property 5: snapshotAllowance decodes the mocked ERC20 allowance read
    function testAuto_SnapshotAllowance_ReturnsMockedAllowanceRead() public {
        uint256 expected = uint256(1);
        vm.mockCall(alice, abi.encodeWithSignature("allowance(address,address)", alice, alice), abi.encode(expected));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("snapshotAllowance(address,address,address)", alice, alice, alice));
        require(ok, "snapshotAllowance reverted unexpectedly");
        assertEq(ret.length, 32, "snapshotAllowance ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "snapshotAllowance should return the mocked external read");
        assertEq(vm.load(target, bytes32(uint256(1))), bytes32(uint256(expected)), "snapshotAllowance should persist the mocked external read");
    }
    // Property 6: snapshotSupply decodes the mocked ERC20 supply read
    function testAuto_SnapshotSupply_ReturnsMockedSupplyRead() public {
        uint256 expected = uint256(1);
        vm.mockCall(alice, abi.encodeWithSignature("totalSupply()"), abi.encode(expected));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("snapshotSupply(address)", alice));
        require(ok, "snapshotSupply reverted unexpectedly");
        assertEq(ret.length, 32, "snapshotSupply ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "snapshotSupply should return the mocked external read");
        assertEq(vm.load(target, bytes32(uint256(2))), bytes32(uint256(expected)), "snapshotSupply should persist the mocked external read");
    }
}
