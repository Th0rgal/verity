// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

contract StringSmokeReference {
    function echoString(string calldata message) external pure returns (string memory) {
        return message;
    }

    function echoStringAfterUint(uint256, string calldata message) external pure returns (string memory) {
        return message;
    }

    function echoStringBeforeUint(string calldata message, uint256) external pure returns (string memory) {
        return message;
    }

    function echoSecondString(string calldata, string calldata message) external pure returns (string memory) {
        return message;
    }
}

contract StringSmokeTest is Test, YulTestBase {
    address internal stringSmoke;
    StringSmokeReference internal reference;

    function setUp() public {
        stringSmoke = deployCompiledVerityModule(
            "Contracts.StringSmoke",
            "StringSmoke",
            "artifacts/test-string-smoke"
        );
        reference = new StringSmokeReference();
    }

    function _assertEchoParity(string memory message) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringSmoke.call(abi.encodeWithSignature("echoString(string)", message));
        (bool refSuccess, bytes memory refData) =
            address(reference).call(abi.encodeWithSignature("echoString(string)", message));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "ABI payload mismatch");
        assertEq(abi.decode(yulData, (string)), message, "decoded string mismatch");
    }

    function _assertEchoAfterUintParity(uint256 tag, string memory message) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringSmoke.call(abi.encodeWithSignature("echoStringAfterUint(uint256,string)", tag, message));
        (bool refSuccess, bytes memory refData) =
            address(reference).call(abi.encodeWithSignature("echoStringAfterUint(uint256,string)", tag, message));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "ABI payload mismatch");
        assertEq(abi.decode(yulData, (string)), message, "decoded string mismatch");
    }

    function _assertEchoBeforeUintParity(string memory message, uint256 tag) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringSmoke.call(abi.encodeWithSignature("echoStringBeforeUint(string,uint256)", message, tag));
        (bool refSuccess, bytes memory refData) =
            address(reference).call(abi.encodeWithSignature("echoStringBeforeUint(string,uint256)", message, tag));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "ABI payload mismatch");
        assertEq(abi.decode(yulData, (string)), message, "decoded string mismatch");
    }

    function _assertEchoSecondStringParity(string memory prefix, string memory message) internal {
        (bool yulSuccess, bytes memory yulData) =
            stringSmoke.call(abi.encodeWithSignature("echoSecondString(string,string)", prefix, message));
        (bool refSuccess, bytes memory refData) =
            address(reference).call(abi.encodeWithSignature("echoSecondString(string,string)", prefix, message));

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "ABI payload mismatch");
        assertEq(abi.decode(yulData, (string)), message, "decoded string mismatch");
    }

    function testEchoStringEmpty() public {
        _assertEchoParity("");
    }

    function testEchoStringShortAscii() public {
        _assertEchoParity("verity");
    }

    function testEchoStringExactlyOneWord() public {
        _assertEchoParity("0123456789abcdef0123456789abcdef");
    }

    function testEchoStringLongDynamicTail() public {
        _assertEchoParity(
            "string support should round-trip through the generated yul runtime without truncation"
        );
    }

    function testEchoStringUtf8Multibyte() public {
        _assertEchoParity(unicode"Verity grüßt the 🌍");
    }

    function testEchoStringAfterUintEmptyAndLong() public {
        _assertEchoAfterUintParity(0, "");
        _assertEchoAfterUintParity(
            type(uint256).max,
            "string support should survive a leading static head before the dynamic payload"
        );
    }

    function testEchoStringBeforeUintExactlyOneWord() public {
        _assertEchoBeforeUintParity("0123456789abcdef0123456789abcdef", 42);
    }

    function testEchoStringBeforeUintUtf8Multibyte() public {
        _assertEchoBeforeUintParity(unicode"dynamic first, static second, grüße 🌍", 7);
    }

    function testEchoSecondStringTwoDynamicHeads() public {
        _assertEchoSecondStringParity("", "verity");
        _assertEchoSecondStringParity(
            "ignored prefix that still shifts the second string offset",
            "the returned second string should preserve its own tail bytes"
        );
    }
}
