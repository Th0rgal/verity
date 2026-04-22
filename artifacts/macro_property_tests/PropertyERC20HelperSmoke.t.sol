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
}
