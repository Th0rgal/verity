// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyAdtNewtypeComboTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyAdtNewtypeComboTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("AdtNewtypeCombo");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: pause has no unexpected revert
    function testAuto_Pause_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("pause()"));
        require(ok, "pause reverted unexpectedly");
    }
    // Property 2: unpause has no unexpected revert
    function testAuto_Unpause_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("unpause()"));
        require(ok, "unpause reverted unexpectedly");
    }
    // Property 3: setLastId has no unexpected revert
    function testAuto_SetLastId_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setLastId(uint256)", uint256(1)));
        require(ok, "setLastId reverted unexpectedly");
    }
}
