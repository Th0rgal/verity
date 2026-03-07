// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

contract StringSmokeReference {
    function echoString(string calldata message) external pure returns (string memory) {
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
}
