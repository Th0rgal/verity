// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStorageBoolArraySmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyStorageBoolArraySmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StorageBoolArraySmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `firstFlag` result
    function testTODO_FirstFlag_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("firstFlag()"));
        require(ok, "firstFlag reverted unexpectedly");
        assertEq(ret.length, 32, "firstFlag ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: pushFlag has no unexpected revert
    function testAuto_PushFlag_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("pushFlag(bool)", true));
        require(ok, "pushFlag reverted unexpectedly");
    }
    // Property 3: setFirstFlag has no unexpected revert
    function testAuto_SetFirstFlag_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setFirstFlag(bool)", true));
        require(ok, "setFirstFlag reverted unexpectedly");
    }
}
