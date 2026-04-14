// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyNewtypeNamespaceSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyNewtypeNamespaceSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("NewtypeNamespaceSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setId has no unexpected revert
    function testAuto_SetId_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setId(uint256)", uint256(1)));
        require(ok, "setId reverted unexpectedly");
    }
}
