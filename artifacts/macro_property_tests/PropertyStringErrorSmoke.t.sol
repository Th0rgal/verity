// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStringErrorSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/StringErrorSmoke.lean
 */
contract PropertyStringErrorSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StringErrorSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: checkMessage has no unexpected revert
    function testAuto_CheckMessage_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("checkMessage(bool,string)", true, "verity"));
        require(ok, "checkMessage reverted unexpectedly");
    }
    // Property 2: checkTaggedMessage has no unexpected revert
    function testAuto_CheckTaggedMessage_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("checkTaggedMessage(uint256,string)", uint256(1), "verity"));
        require(ok, "checkTaggedMessage reverted unexpectedly");
    }
    // Property 3: checkSecondMessage has no unexpected revert
    function testAuto_CheckSecondMessage_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("checkSecondMessage(bool,string,string)", true, "verity", "verity"));
        require(ok, "checkSecondMessage reverted unexpectedly");
    }
}
