// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

contract StringEqSmokeReference {
    function same(string calldata lhs, string calldata rhs) external pure returns (bool) {
        return keccak256(bytes(lhs)) == keccak256(bytes(rhs));
    }

    function different(string calldata lhs, string calldata rhs) external pure returns (bool) {
        return keccak256(bytes(lhs)) != keccak256(bytes(rhs));
    }

    function choose(string calldata lhs, string calldata rhs) external pure returns (uint256) {
        return keccak256(bytes(lhs)) == keccak256(bytes(rhs)) ? 1 : 0;
    }
}

contract StringEqSmokeTest is Test, YulTestBase {
    address internal stringEqSmoke;
    StringEqSmokeReference internal referenceContract;

    function setUp() public {
        stringEqSmoke = deployCompiledVerityModule(
            "Contracts.StringEqSmoke",
            "StringEqSmoke",
            "artifacts/test-string-eq-smoke"
        );
        referenceContract = new StringEqSmokeReference();
    }

    function _assertSameParity(string memory lhs, string memory rhs) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringEqSmoke.call(abi.encodeWithSignature("same(string,string)", lhs, rhs));
        (bool refSuccess, bytes memory refData) =
            address(referenceContract).call(abi.encodeWithSignature("same(string,string)", lhs, rhs));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "same(bool) ABI payload mismatch");
        assertEq(abi.decode(yulData, (bool)), keccak256(bytes(lhs)) == keccak256(bytes(rhs)), "decoded bool mismatch");
    }

    function _assertDifferentParity(string memory lhs, string memory rhs) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringEqSmoke.call(abi.encodeWithSignature("different(string,string)", lhs, rhs));
        (bool refSuccess, bytes memory refData) =
            address(referenceContract).call(abi.encodeWithSignature("different(string,string)", lhs, rhs));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "different(bool) ABI payload mismatch");
        assertEq(abi.decode(yulData, (bool)), keccak256(bytes(lhs)) != keccak256(bytes(rhs)), "decoded bool mismatch");
    }

    function _assertChooseParity(string memory lhs, string memory rhs) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringEqSmoke.call(abi.encodeWithSignature("choose(string,string)", lhs, rhs));
        (bool refSuccess, bytes memory refData) =
            address(referenceContract).call(abi.encodeWithSignature("choose(string,string)", lhs, rhs));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "choose(uint256) ABI payload mismatch");
        assertEq(
            abi.decode(yulData, (uint256)),
            keccak256(bytes(lhs)) == keccak256(bytes(rhs)) ? 1 : 0,
            "decoded uint mismatch"
        );
    }

    function testSameParity() public {
        _assertSameParity("", "");
        _assertSameParity("verity", "verity");
        _assertSameParity("0123456789abcdef0123456789abcdef", "0123456789abcdef0123456789abcdef");
        _assertSameParity(unicode"Verity grüßt the 🌍", unicode"Verity grüßt the 🌍");
        _assertSameParity(
            "string equality should preserve long dynamic tails across generated yul",
            "string equality should preserve long dynamic tails across generated yul"
        );
        _assertSameParity("verity", "verita");
        _assertSameParity("same prefix, different tail A", "same prefix, different tail B");
    }

    function testDifferentParity() public {
        _assertDifferentParity("", "");
        _assertDifferentParity("verity", "verity");
        _assertDifferentParity("verity", "verita");
        _assertDifferentParity(unicode"Grüße 🌍", unicode"Gruesse 🌍");
        _assertDifferentParity(
            "one dynamic payload that shares a long prefix but changes the end A",
            "one dynamic payload that shares a long prefix but changes the end B"
        );
    }

    function testChooseParity() public {
        _assertChooseParity("", "");
        _assertChooseParity("verity", "verity");
        _assertChooseParity("verity", "different");
        _assertChooseParity(
            "first long payload should map to 1 only when both dynamic tails match exactly",
            "first long payload should map to 1 only when both dynamic tails match exactly"
        );
        _assertChooseParity(
            "first long payload should map to 1 only when both dynamic tails match exactly",
            "first long payload should map to 1 only when both dynamic tails mismatch near the end!"
        );
    }
}
