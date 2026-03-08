// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

contract StringEventSmokeReference {
    event MessageLogged(string message);
    event TaggedMessageLogged(uint256 indexed tag, string message);
    event IndexedMessageLogged(string indexed message);
    event SecondMessageLogged(string prefix, string message);

    function logMessage(string calldata message) external {
        emit MessageLogged(message);
    }

    function logTaggedMessage(uint256 tag, string calldata message) external {
        emit TaggedMessageLogged(tag, message);
    }

    function logIndexedMessage(string calldata message) external {
        emit IndexedMessageLogged(message);
    }

    function logSecondMessage(string calldata prefix, string calldata message) external {
        emit SecondMessageLogged(prefix, message);
    }
}

contract StringEventSmokeTest is Test, YulTestBase {
    address internal stringEventSmoke;
    StringEventSmokeReference internal reference;

    function setUp() public {
        stringEventSmoke = deployCompiledVerityModule(
            "Contracts.StringEventSmoke",
            "StringEventSmoke",
            "artifacts/test-string-event-smoke"
        );
        reference = new StringEventSmokeReference();
    }

    function _assertLogsEqual(Vm.Log[] memory lhs, Vm.Log[] memory rhs) internal pure {
        assertEq(lhs.length, rhs.length, "log count mismatch");
        for (uint256 i = 0; i < lhs.length; i++) {
            assertEq(lhs[i].topics.length, rhs[i].topics.length, "topic count mismatch");
            for (uint256 j = 0; j < lhs[i].topics.length; j++) {
                assertEq(lhs[i].topics[j], rhs[i].topics[j], "topic mismatch");
            }
            assertEq(lhs[i].data, rhs[i].data, "data mismatch");
        }
    }

    function _recordLogs(address target, bytes memory callData) internal returns (Vm.Log[] memory logs) {
        vm.recordLogs();
        (bool ok,) = target.call(callData);
        assertTrue(ok, "event emitter call failed");
        logs = vm.getRecordedLogs();
    }

    function _assertLogMessageParity(string memory message) internal {
        Vm.Log[] memory yulLogs =
            _recordLogs(stringEventSmoke, abi.encodeWithSignature("logMessage(string)", message));
        Vm.Log[] memory refLogs =
            _recordLogs(address(reference), abi.encodeWithSignature("logMessage(string)", message));
        _assertLogsEqual(yulLogs, refLogs);
    }

    function _assertLogTaggedMessageParity(uint256 tag, string memory message) internal {
        Vm.Log[] memory yulLogs = _recordLogs(
            stringEventSmoke,
            abi.encodeWithSignature("logTaggedMessage(uint256,string)", tag, message)
        );
        Vm.Log[] memory refLogs = _recordLogs(
            address(reference),
            abi.encodeWithSignature("logTaggedMessage(uint256,string)", tag, message)
        );
        _assertLogsEqual(yulLogs, refLogs);
    }

    function _assertLogIndexedMessageParity(string memory message) internal {
        Vm.Log[] memory yulLogs =
            _recordLogs(stringEventSmoke, abi.encodeWithSignature("logIndexedMessage(string)", message));
        Vm.Log[] memory refLogs =
            _recordLogs(address(reference), abi.encodeWithSignature("logIndexedMessage(string)", message));
        _assertLogsEqual(yulLogs, refLogs);
    }

    function _assertLogSecondMessageParity(string memory prefix, string memory message) internal {
        Vm.Log[] memory yulLogs = _recordLogs(
            stringEventSmoke,
            abi.encodeWithSignature("logSecondMessage(string,string)", prefix, message)
        );
        Vm.Log[] memory refLogs = _recordLogs(
            address(reference),
            abi.encodeWithSignature("logSecondMessage(string,string)", prefix, message)
        );
        _assertLogsEqual(yulLogs, refLogs);
    }

    function testLogMessageParity() public {
        _assertLogMessageParity("");
        _assertLogMessageParity(unicode"Verity grüßt the 🌍");
    }

    function testLogTaggedMessageParity() public {
        _assertLogTaggedMessageParity(0, "");
        _assertLogTaggedMessageParity(
            type(uint256).max,
            "tagged string event data should keep the unindexed dynamic tail intact"
        );
    }

    function testLogIndexedMessageParity() public {
        _assertLogIndexedMessageParity("");
        _assertLogIndexedMessageParity("indexed dynamic payloads should hash the same topic bytes");
    }

    function testLogSecondMessageParity() public {
        _assertLogSecondMessageParity("", "verity");
        _assertLogSecondMessageParity(
            "first dynamic head",
            "second dynamic head should preserve its own offset and bytes"
        );
    }
}
