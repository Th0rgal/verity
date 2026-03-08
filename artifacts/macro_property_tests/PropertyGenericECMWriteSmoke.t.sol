// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyGenericECMWriteSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyGenericECMWriteSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("GenericECMWriteSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: runEffect has no unexpected revert
    function testAuto_RunEffect_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("runEffect(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "runEffect reverted unexpectedly");
    }
}
