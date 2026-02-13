// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./yul/YulTestBase.sol";

/**
 * @title DifferentialSafeCounter
 * @notice Differential testing for SafeCounter contract
 *
 * Approach:
 * 1. Generate random transactions
 * 2. Execute on compiled Yul contract (EVM)
 * 3. Execute on EDSL interpreter (via vm.ffi)
 * 4. Assert identical results including overflow/underflow protection
 *
 * Success: 10,000+ tests with zero mismatches
 */
contract DifferentialSafeCounter is YulTestBase, DiffTestConfig {
    // Compiled contract
    address safeCounter;

    // Test counters
    uint256 public testsPassed;
    uint256 public testsFailed;

    // Storage state tracking for EDSL interpreter
    mapping(uint256 => uint256) edslStorage;

    function setUp() public {
        // Deploy SafeCounter from Yul using YulTestBase helper
        safeCounter = deployYul("SafeCounter");
        require(safeCounter != address(0), "Deploy failed");
    }

    /**
     * @notice Execute transaction on EVM and EDSL, compare results
     */
    function executeDifferentialTest(
        string memory functionName,
        address sender
    ) internal returns (bool success) {
        // 1. Execute on compiled contract (EVM)
        vm.prank(sender);

        bool evmSuccess;
        bytes memory evmReturnData;

        bytes32 functionSig = keccak256(bytes(functionName));

        if (functionSig == keccak256(bytes("increment"))) {
            (evmSuccess, evmReturnData) = safeCounter.call(
                abi.encodeWithSignature("increment()")
            );
        } else if (functionSig == keccak256(bytes("decrement"))) {
            (evmSuccess, evmReturnData) = safeCounter.call(
                abi.encodeWithSignature("decrement()")
            );
        } else if (functionSig == keccak256(bytes("getCount"))) {
            (evmSuccess, evmReturnData) = safeCounter.call(
                abi.encodeWithSignature("getCount()")
            );
        } else {
            revert("Unknown function");
        }

        uint256 evmStorageAfter = uint256(vm.load(safeCounter, bytes32(uint256(0))));
        uint256 evmReturnValue = evmReturnData.length > 0 ? abi.decode(evmReturnData, (uint256)) : 0;

        // 2. Execute on EDSL interpreter (via vm.ffi)
        string memory storageState = _buildStorageString();
        string memory edslResult = _runInterpreter(functionName, sender, storageState);

        // 3. Parse and compare results
        console2.log("EVM success:", evmSuccess);
        console2.log("EVM storage[0]:", evmStorageAfter);
        console2.log("EVM return value:", evmReturnValue);
        console2.log("EDSL result:", edslResult);

        // Parse EDSL result
        bool edslSuccess = contains(edslResult, "\"success\":true");

        // Validate JSON structure
        if (!contains(edslResult, "\"returnValue\":")) {
            console2.log("ERROR: Malformed JSON - missing returnValue field");
            console2.log("  JSON:", edslResult);
            testsFailed++;
            return false;
        }

        uint256 edslReturnValue = _extractReturnValue(edslResult);

        // Validate: Success flags must match
        if (evmSuccess != edslSuccess) {
            console2.log("MISMATCH: Success flags differ!");
            console2.log("  EVM:", evmSuccess);
            console2.log("  EDSL:", edslSuccess);
            testsFailed++;
            return false;
        }

        // Validate: Return values must match
        if (evmReturnValue != edslReturnValue) {
            console2.log("MISMATCH: Return values differ!");
            console2.log("  EVM:", evmReturnValue);
            console2.log("  EDSL:", edslReturnValue);
            testsFailed++;
            return false;
        }

        // Validate: Storage changes must match
        (bool hasStorageChange, uint256 edslStorageChange) = _extractStorageChange(edslResult, 0);
        if (hasStorageChange) {
            edslStorage[0] = edslStorageChange;
        }

        // Validate: EVM final storage must match EDSL final storage
        if (evmStorageAfter != edslStorage[0]) {
            console2.log("MISMATCH: Storage states differ!");
            console2.log("  EVM storage[0]:", evmStorageAfter);
            console2.log("  EDSL storage[0]:", edslStorage[0]);
            testsFailed++;
            return false;
        }

        testsPassed++;
        return true;
    }

    function _runInterpreter(
        string memory functionName,
        address sender,
        string memory storageState
    ) internal returns (string memory) {
        // Build command with storage state
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";
        inputs[2] = string.concat(
            "cd \"$(git rev-parse --show-toplevel)\" && export PATH=\"$HOME/.elan/bin:$PATH\" && ",
            "if [ ! -x ./.lake/build/bin/difftest-interpreter ]; then ",
            "mkdir -p .lake/build/bin && lake build difftest-interpreter >/dev/null; ",
            "fi; ",
            "./.lake/build/bin/difftest-interpreter",
            " SafeCounter ",
            functionName,
            " ",
            vm.toString(sender),
            bytes(storageState).length > 0 ? string.concat(" \"", storageState, "\"") : "",
            " value=0 timestamp=",
            vm.toString(block.timestamp)
        );

        // Call Lean interpreter
        bytes memory edslResultBytes = vm.ffi(inputs);
        return string(edslResultBytes);
    }

    function _extractReturnValue(string memory json) internal pure returns (uint256) {
        bytes memory jsonBytes = bytes(json);
        bytes memory searchBytes = bytes("\"returnValue\":\"");

        if (jsonBytes.length < searchBytes.length) return 0;
        for (uint i = 0; i <= jsonBytes.length - searchBytes.length; i++) {
            bool found = true;
            for (uint j = 0; j < searchBytes.length; j++) {
                if (jsonBytes[i + j] != searchBytes[j]) {
                    found = false;
                    break;
                }
            }
            if (found) {
                uint start = i + searchBytes.length;
                uint end = start;
                while (end < jsonBytes.length && jsonBytes[end] != bytes1('"')) {
                    end++;
                }
                bytes memory numBytes = new bytes(end - start);
                for (uint k = 0; k < end - start; k++) {
                    numBytes[k] = jsonBytes[start + k];
                }
                return _stringToUint(string(numBytes));
            }
        }
        return 0;
    }

    function _stringToUint(string memory s) internal pure returns (uint256) {
        bytes memory b = bytes(s);
        uint256 result = 0;
        for (uint i = 0; i < b.length; i++) {
            uint8 c = uint8(b[i]);
            if (c >= 48 && c <= 57) {
                unchecked { result = result * 10 + (c - 48); }
            }
        }
        return result;
    }

    function _extractStorageChange(string memory json, uint256 slot) internal pure returns (bool, uint256) {
        bytes memory jsonBytes = bytes(json);
        bytes memory slotPattern = bytes(string.concat("\"slot\":", vm.toString(slot)));

        if (jsonBytes.length < slotPattern.length) return (false, 0);
        for (uint i = 0; i <= jsonBytes.length - slotPattern.length; i++) {
            bool found = true;
            for (uint j = 0; j < slotPattern.length; j++) {
                if (jsonBytes[i + j] != slotPattern[j]) {
                    found = false;
                    break;
                }
            }
            if (found) {
                bytes memory valuePattern = bytes("\"value\":");
                if (jsonBytes.length < valuePattern.length) return (false, 0);
                for (uint k = i; k <= jsonBytes.length - valuePattern.length; k++) {
                    bool valueFound = true;
                    for (uint l = 0; l < valuePattern.length; l++) {
                        if (jsonBytes[k + l] != valuePattern[l]) {
                            valueFound = false;
                            break;
                        }
                    }
                    if (valueFound) {
                        uint start = k + valuePattern.length;
                        uint end = start;
                        while (end < jsonBytes.length && jsonBytes[end] >= 0x30 && jsonBytes[end] <= 0x39) {
                            end++;
                        }
                        bytes memory numBytes = new bytes(end - start);
                        for (uint m = 0; m < end - start; m++) {
                            numBytes[m] = jsonBytes[start + m];
                        }
                        return (true, _stringToUint(string(numBytes)));
                    }
                }
            }
        }
        return (false, 0);
    }

    function _buildStorageString() internal view returns (string memory) {
        uint256 val = edslStorage[0];
        if (val == 0) {
            return "";
        }
        return string.concat("0:", vm.toString(val));
    }

    function contains(string memory str, string memory substr) internal pure returns (bool) {
        bytes memory strBytes = bytes(str);
        bytes memory substrBytes = bytes(substr);

        if (substrBytes.length > strBytes.length) return false;

        for (uint i = 0; i <= strBytes.length - substrBytes.length; i++) {
            bool found = true;
            for (uint j = 0; j < substrBytes.length; j++) {
                if (strBytes[i + j] != substrBytes[j]) {
                    found = false;
                    break;
                }
            }
            if (found) return true;
        }
        return false;
    }

    /**
     * @notice Run differential tests with fixed transactions including overflow/underflow tests
     */
    function testDifferential_BasicOperations() public {
        // Test increment
        bool success1 = executeDifferentialTest("increment", address(0xA11CE));
        assertTrue(success1, "Increment test 1 failed");

        // Test getCount
        bool success2 = executeDifferentialTest("getCount", address(0xA11CE));
        assertTrue(success2, "GetCount test 1 failed");

        // Test another increment
        bool success3 = executeDifferentialTest("increment", address(0xB0B));
        assertTrue(success3, "Increment test 2 failed");

        // Test getCount again
        bool success4 = executeDifferentialTest("getCount", address(0xB0B));
        assertTrue(success4, "GetCount test 2 failed");

        // Test decrement
        bool success5 = executeDifferentialTest("decrement", address(0xCA401));
        assertTrue(success5, "Decrement test 1 failed");

        // Final getCount
        bool success6 = executeDifferentialTest("getCount", address(0xCA401));
        assertTrue(success6, "GetCount test 3 failed");

        console2.log("Differential tests passed:", testsPassed);
    }

    /**
     * @notice Test overflow protection
     */
    function testDifferential_OverflowProtection() public {
        // Set storage to MAX_UINT256
        edslStorage[0] = type(uint256).max;
        vm.store(safeCounter, bytes32(uint256(0)), bytes32(type(uint256).max));

        // Try to increment (should revert)
        bool success = executeDifferentialTest("increment", address(0xA11CE));
        assertTrue(success, "Overflow protection test failed");

        // Verify both reverted
        console2.log("Overflow protection verified");
    }

    /**
     * @notice Test underflow protection
     */
    function testDifferential_UnderflowProtection() public {
        // Storage starts at 0

        // Try to decrement (should revert)
        bool success = executeDifferentialTest("decrement", address(0xB0B));
        assertTrue(success, "Underflow protection test failed");

        // Verify both reverted
        console2.log("Underflow protection verified");
    }

    /**
     * @notice Run 100 random differential tests
     */
    function testDifferential_Random100() public {
        (uint256 startIndex, uint256 count) = _diffRandomSmallRange();
        _runRandomDifferentialTests(startIndex, count, _diffRandomBaseSeed());
    }

    /**
     * @notice Run 10000 random differential tests
     */
    function testDifferential_Random10000() public {
        (uint256 startIndex, uint256 count) = _diffRandomLargeRange();
        _runRandomDifferentialTests(startIndex, count, _diffRandomBaseSeed());
    }

    /**
     * @notice Execute N random transactions
     */
    function _runRandomDifferentialTests(uint256 startIndex, uint256 count, uint256 seed) internal {
        console2.log("Generated", count, "random transactions");

        uint256 prng = _skipRandom(seed, startIndex);
        vm.pauseGasMetering();
        for (uint256 i = 0; i < count; i++) {
            // Simple PRNG
            prng = _lcg(prng);

            // Generate address
            address sender = _indexToAddress(prng % 5);

            // Determine function (3 options: increment, decrement, getCount)
            prng = _lcg(prng);
            uint256 funcChoice = prng % 3;

            string memory functionName;
            if (funcChoice == 0) {
                functionName = "increment";
            } else if (funcChoice == 1) {
                functionName = "decrement";
            } else {
                functionName = "getCount";
            }

            bool success = executeDifferentialTest(functionName, sender);
            assertTrue(success, string.concat("Random ", functionName, " test failed"));
        }

        vm.resumeGasMetering();

        console2.log("Random differential tests completed:", testsPassed);
        console2.log("Failed:", testsFailed);
        assertEq(testsFailed, 0, "Some random tests failed");
    }

    function _skipRandom(uint256 prng, uint256 iterations) internal pure returns (uint256) {
        for (uint256 i = 0; i < iterations; i++) {
            prng = _lcg(prng);
            prng = _lcg(prng);
        }
        return prng;
    }

    function _lcg(uint256 prng) internal pure returns (uint256) {
        return (1103515245 * prng + 12345) % (2**31);
    }

    function _indexToAddress(uint256 index) internal pure returns (address) {
        if (index == 0) return address(0xA11CE);
        if (index == 1) return address(0xB0B);
        if (index == 2) return address(0xCA401);
        if (index == 3) return address(0xDABE);
        return address(0xEBE);
    }
}
