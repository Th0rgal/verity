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

    // Property 1: signedDiv returns the declared constant result
    function testAuto_SignedDiv_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedDiv(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "signedDiv reverted unexpectedly");
        assertEq(ret.length, 32, "signedDiv ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(int256(uint256(1)) / int256(uint256(1))), "signedDiv should return the declared constant");
    }
    // Property 2: signedMod returns the declared constant result
    function testAuto_SignedMod_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedMod(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "signedMod reverted unexpectedly");
        assertEq(ret.length, 32, "signedMod ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(int256(uint256(1)) % int256(uint256(1))), "signedMod should return the declared constant");
    }
    // Property 3: signedLt returns the declared constant result
    function testAuto_SignedLt_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedLt(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "signedLt reverted unexpectedly");
        assertEq(ret.length, 32, "signedLt ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertEq(actual, (int256(uint256(1)) < int256(uint256(1))), "signedLt should return the declared constant");
    }
    // Property 4: signedGt returns the declared constant result
    function testAuto_SignedGt_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedGt(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "signedGt reverted unexpectedly");
        assertEq(ret.length, 32, "signedGt ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertEq(actual, (int256(uint256(1)) > int256(uint256(1))), "signedGt should return the declared constant");
    }
    // Property 5: arithmeticShift returns the declared constant result
    function testAuto_ArithmeticShift_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("arithmeticShift(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "arithmeticShift reverted unexpectedly");
        assertEq(ret.length, 32, "arithmeticShift ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 0, "arithmeticShift should return the declared constant");
    }
    // Property 6: signExtended returns the declared constant or immutable value
    function testAuto_SignExtended_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signExtended()"));
        require(ok, "signExtended reverted unexpectedly");
        assertEq(ret.length, 32, "signExtended ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, type(uint256).max, "signExtended should preserve the expected value");
    }
    // Property 7: shiftedMask returns the declared constant or immutable value
    function testAuto_ShiftedMask_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("shiftedMask()"));
        require(ok, "shiftedMask reverted unexpectedly");
        assertEq(ret.length, 32, "shiftedMask ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, type(uint256).max, "shiftedMask should preserve the expected value");
    }
    // Property 8: signedDivSurface returns the declared constant result
    function testAuto_SignedDivSurface_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedDivSurface(int256,int256)", int256(1), int256(1)));
        require(ok, "signedDivSurface reverted unexpectedly");
        assertEq(ret.length, 32, "signedDivSurface ABI return length mismatch (expected 32 bytes)");
        int256 actual = abi.decode(ret, (int256));
        assertEq(actual, (int256(1) / int256(1)), "signedDivSurface should return the declared constant");
    }
    // Property 9: signedModSurface returns the declared constant result
    function testAuto_SignedModSurface_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedModSurface(int256,int256)", int256(1), int256(1)));
        require(ok, "signedModSurface reverted unexpectedly");
        assertEq(ret.length, 32, "signedModSurface ABI return length mismatch (expected 32 bytes)");
        int256 actual = abi.decode(ret, (int256));
        assertEq(actual, (int256(1) % int256(1)), "signedModSurface should return the declared constant");
    }
    // Property 10: signedDivViaLocal decodes and matches the inferred straight-line result
    function testAuto_SignedDivViaLocal_ReturnsInferredStraightLineResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("signedDivViaLocal(uint256,int256)", uint256(1), int256(1)));
        require(ok, "signedDivViaLocal reverted unexpectedly");
        assertEq(ret.length, 32, "signedDivViaLocal ABI return length mismatch (expected 32 bytes)");
        int256 actual = abi.decode(ret, (int256));
        assertEq(actual, (1 / int256(1)), "signedDivViaLocal should preserve the inferred result");
    }
    // Property 11: castToInt returns the declared constant result
    function testAuto_CastToInt_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("castToInt(uint256)", uint256(1)));
        require(ok, "castToInt reverted unexpectedly");
        assertEq(ret.length, 32, "castToInt ABI return length mismatch (expected 32 bytes)");
        int256 actual = abi.decode(ret, (int256));
        assertEq(actual, 1, "castToInt should return the declared constant");
    }
    // Property 12: castToUint returns the declared constant result
    function testAuto_CastToUint_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("castToUint(int256)", int256(1)));
        require(ok, "castToUint reverted unexpectedly");
        assertEq(ret.length, 32, "castToUint ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 1, "castToUint should return the declared constant");
    }
    // Property 13: minusOne returns the declared constant or immutable value
    function testAuto_MinusOne_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("minusOne()"));
        require(ok, "minusOne reverted unexpectedly");
        assertEq(ret.length, 32, "minusOne ABI return length mismatch (expected 32 bytes)");
        int256 actual = abi.decode(ret, (int256));
        assertEq(actual, int256(-1), "minusOne should preserve the expected value");
    }
    // Property 14: bitAndSignBit returns the declared constant result
    function testAuto_BitAndSignBit_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("bitAndSignBit(int256,int256)", int256(1), int256(1)));
        require(ok, "bitAndSignBit reverted unexpectedly");
        assertEq(ret.length, 32, "bitAndSignBit ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertEq(actual, (1 < 0), "bitAndSignBit should return the declared constant");
    }
    // Property 15: minSignBit returns the declared constant result
    function testAuto_MinSignBit_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("minSignBit(int256)", int256(1)));
        require(ok, "minSignBit reverted unexpectedly");
        assertEq(ret.length, 32, "minSignBit ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertEq(actual, (((int256(1) < 0) ? int256(1) : 0) < 0), "minSignBit should return the declared constant");
    }
    // Property 16: storeSigned decodes and matches the inferred straight-line result
    function testAuto_StoreSigned_ReturnsInferredStraightLineResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("storeSigned(int256)", int256(1)));
        require(ok, "storeSigned reverted unexpectedly");
        assertEq(ret.length, 32, "storeSigned ABI return length mismatch (expected 32 bytes)");
        int256 actual = abi.decode(ret, (int256));
        assertEq(actual, int256(1), "storeSigned should preserve the inferred result");
    }
    // Property 17: loadSigned reads storage slot 0 and decodes the result
    function testAuto_LoadSigned_ReadsConfiguredStorage() public {
        int256 expected = int256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("loadSigned()"));
        require(ok, "loadSigned reverted unexpectedly");
        assertEq(ret.length, 32, "loadSigned ABI return length mismatch (expected 32 bytes)");
        int256 actual = abi.decode(ret, (int256));
        assertEq(actual, expected, "loadSigned should return storage slot 0");
    }
}
