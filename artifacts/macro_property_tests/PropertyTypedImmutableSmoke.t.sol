// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyTypedImmutableSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyTypedImmutableSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("TypedImmutableSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `isPaused` result
    function testTODO_IsPaused_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("isPaused()"));
        require(ok, "isPaused reverted unexpectedly");
        assertEq(ret.length, 32, "isPaused ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `feeScale` result
    function testTODO_FeeScale_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("feeScale()"));
        require(ok, "feeScale reverted unexpectedly");
        assertEq(ret.length, 32, "feeScale ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: TODO decode and assert `domainSeparator` result
    function testTODO_DomainSeparator_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("domainSeparator()"));
        require(ok, "domainSeparator reverted unexpectedly");
        assertEq(ret.length, 32, "domainSeparator ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
