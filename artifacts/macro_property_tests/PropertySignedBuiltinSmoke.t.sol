// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertySignedBuiltinSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertySignedBuiltinSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("SignedBuiltinSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `signedDiv` result
    function testTODO_SignedDiv_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedDiv(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "signedDiv reverted unexpectedly");
        assertEq(ret.length, 32, "signedDiv ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `signedMod` result
    function testTODO_SignedMod_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedMod(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "signedMod reverted unexpectedly");
        assertEq(ret.length, 32, "signedMod ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: TODO decode and assert `signedLt` result
    function testTODO_SignedLt_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedLt(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "signedLt reverted unexpectedly");
        assertEq(ret.length, 32, "signedLt ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 4: TODO decode and assert `signedGt` result
    function testTODO_SignedGt_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedGt(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "signedGt reverted unexpectedly");
        assertEq(ret.length, 32, "signedGt ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 5: TODO decode and assert `arithmeticShift` result
    function testTODO_ArithmeticShift_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("arithmeticShift(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "arithmeticShift reverted unexpectedly");
        assertEq(ret.length, 32, "arithmeticShift ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 6: TODO decode and assert `signExtended` result
    function testTODO_SignExtended_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signExtended()"));
        require(ok, "signExtended reverted unexpectedly");
        assertEq(ret.length, 32, "signExtended ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 7: TODO decode and assert `shiftedMask` result
    function testTODO_ShiftedMask_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("shiftedMask()"));
        require(ok, "shiftedMask reverted unexpectedly");
        assertEq(ret.length, 32, "shiftedMask ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 8: TODO decode and assert `signedDivSurface` result
    function testTODO_SignedDivSurface_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedDivSurface(int256,int256)", int256(1), int256(1)));
        require(ok, "signedDivSurface reverted unexpectedly");
        assertEq(ret.length, 32, "signedDivSurface ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 9: TODO decode and assert `signedModSurface` result
    function testTODO_SignedModSurface_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedModSurface(int256,int256)", int256(1), int256(1)));
        require(ok, "signedModSurface reverted unexpectedly");
        assertEq(ret.length, 32, "signedModSurface ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 10: TODO decode and assert `signedDivViaLocal` result
    function testTODO_SignedDivViaLocal_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedDivViaLocal(uint256,int256)", uint256(1), int256(1)));
        require(ok, "signedDivViaLocal reverted unexpectedly");
        assertEq(ret.length, 32, "signedDivViaLocal ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 11: TODO decode and assert `castToInt` result
    function testTODO_CastToInt_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("castToInt(uint256)", uint256(1)));
        require(ok, "castToInt reverted unexpectedly");
        assertEq(ret.length, 32, "castToInt ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 12: TODO decode and assert `castToUint` result
    function testTODO_CastToUint_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("castToUint(int256)", int256(1)));
        require(ok, "castToUint reverted unexpectedly");
        assertEq(ret.length, 32, "castToUint ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 13: TODO decode and assert `minusOne` result
    function testTODO_MinusOne_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("minusOne()"));
        require(ok, "minusOne reverted unexpectedly");
        assertEq(ret.length, 32, "minusOne ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 14: TODO decode and assert `bitAndSignBit` result
    function testTODO_BitAndSignBit_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("bitAndSignBit(int256,int256)", int256(1), int256(1)));
        require(ok, "bitAndSignBit reverted unexpectedly");
        assertEq(ret.length, 32, "bitAndSignBit ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 15: TODO decode and assert `minSignBit` result
    function testTODO_MinSignBit_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("minSignBit(int256)", int256(1)));
        require(ok, "minSignBit reverted unexpectedly");
        assertEq(ret.length, 32, "minSignBit ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
