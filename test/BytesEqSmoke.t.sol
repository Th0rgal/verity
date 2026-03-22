// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

contract BytesEqSmokeReference {
    function same(bytes calldata lhs, bytes calldata rhs) external pure returns (bool) {
        return keccak256(lhs) == keccak256(rhs);
    }

    function different(bytes calldata lhs, bytes calldata rhs) external pure returns (bool) {
        return keccak256(lhs) != keccak256(rhs);
    }

    function choose(bytes calldata lhs, bytes calldata rhs) external pure returns (uint256) {
        return keccak256(lhs) == keccak256(rhs) ? 1 : 0;
    }
}

contract BytesEqSmokeTest is Test, YulTestBase {
    address internal bytesEqSmoke;
    BytesEqSmokeReference internal referenceContract;

    function setUp() public {
        bytesEqSmoke = deployCompiledVerityModule(
            "Contracts.BytesEqSmoke",
            "BytesEqSmoke",
            "artifacts/test-bytes-eq-smoke"
        );
        referenceContract = new BytesEqSmokeReference();
    }

    function _assertSameParity(bytes memory lhs, bytes memory rhs) internal {
        (bool yulSuccess, bytes memory yulData) =
            bytesEqSmoke.call(abi.encodeWithSignature("same(bytes,bytes)", lhs, rhs));
        (bool refSuccess, bytes memory refData) =
            address(referenceContract).call(abi.encodeWithSignature("same(bytes,bytes)", lhs, rhs));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "same(bool) ABI payload mismatch");
        assertEq(abi.decode(yulData, (bool)), keccak256(lhs) == keccak256(rhs), "decoded bool mismatch");
    }

    function _assertDifferentParity(bytes memory lhs, bytes memory rhs) internal {
        (bool yulSuccess, bytes memory yulData) =
            bytesEqSmoke.call(abi.encodeWithSignature("different(bytes,bytes)", lhs, rhs));
        (bool refSuccess, bytes memory refData) =
            address(referenceContract).call(abi.encodeWithSignature("different(bytes,bytes)", lhs, rhs));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "different(bool) ABI payload mismatch");
        assertEq(abi.decode(yulData, (bool)), keccak256(lhs) != keccak256(rhs), "decoded bool mismatch");
    }

    function _assertChooseParity(bytes memory lhs, bytes memory rhs) internal {
        (bool yulSuccess, bytes memory yulData) =
            bytesEqSmoke.call(abi.encodeWithSignature("choose(bytes,bytes)", lhs, rhs));
        (bool refSuccess, bytes memory refData) =
            address(referenceContract).call(abi.encodeWithSignature("choose(bytes,bytes)", lhs, rhs));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "choose(uint256) ABI payload mismatch");
        assertEq(
            abi.decode(yulData, (uint256)),
            keccak256(lhs) == keccak256(rhs) ? 1 : 0,
            "decoded uint mismatch"
        );
    }

    function testSameParity() public {
        _assertSameParity(hex"", hex"");
        _assertSameParity(hex"01", hex"01");
        _assertSameParity(hex"00010203ff", hex"00010203ff");
        _assertSameParity(
            hex"11223344556677889900aabbccddeeff00112233445566778899aabbccddeeff",
            hex"11223344556677889900aabbccddeeff00112233445566778899aabbccddeeff"
        );
        _assertSameParity(hex"deadbeef", hex"deadbeee");
        _assertSameParity(
            hex"01020304050607080910111213141516171819202122232425262728293031aa",
            hex"01020304050607080910111213141516171819202122232425262728293031bb"
        );
    }

    function testDifferentParity() public {
        _assertDifferentParity(hex"", hex"");
        _assertDifferentParity(hex"ff", hex"ff");
        _assertDifferentParity(hex"ff", hex"00");
        _assertDifferentParity(hex"abcdef", hex"abcdee");
        _assertDifferentParity(
            hex"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            hex"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab"
        );
    }

    function testChooseParity() public {
        _assertChooseParity(hex"", hex"");
        _assertChooseParity(hex"bead", hex"bead");
        _assertChooseParity(hex"bead", hex"feed");
        _assertChooseParity(
            hex"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff",
            hex"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"
        );
        _assertChooseParity(
            hex"00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff",
            hex"00112233445566778899aabbccddeeff00112233445566778899aabbccddee00"
        );
    }
}
