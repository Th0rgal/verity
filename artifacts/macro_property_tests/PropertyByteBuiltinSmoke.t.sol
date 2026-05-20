// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyByteBuiltinSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyByteBuiltinSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ByteBuiltinSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `extract` result
    function testTODO_Extract_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("extract(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "extract reverted unexpectedly");
        assertEq(ret.length, 32, "extract ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `highByteConstant` result
    function testTODO_HighByteConstant_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("highByteConstant()"));
        require(ok, "highByteConstant reverted unexpectedly");
        assertEq(ret.length, 32, "highByteConstant ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: TODO decode and assert `lowByteConstant` result
    function testTODO_LowByteConstant_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("lowByteConstant()"));
        require(ok, "lowByteConstant reverted unexpectedly");
        assertEq(ret.length, 32, "lowByteConstant ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 4: TODO decode and assert `outOfBoundsByteConstant` result
    function testTODO_OutOfBoundsByteConstant_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("outOfBoundsByteConstant()"));
        require(ok, "outOfBoundsByteConstant reverted unexpectedly");
        assertEq(ret.length, 32, "outOfBoundsByteConstant ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 5: TODO decode and assert `storeExtracted` result
    function testTODO_StoreExtracted_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("storeExtracted(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "storeExtracted reverted unexpectedly");
        assertEq(ret.length, 32, "storeExtracted ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
