// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/**
 * @title DifferentialSimpleStorage
 * @notice Differential testing for SimpleStorage contract
 *
 * Approach:
 * 1. Generate random transactions
 * 2. Execute on compiled Yul contract (EVM)
 * 3. Execute on EDSL interpreter (via vm.ffi)
 * 4. Assert identical results
 *
 * Success: 10,000+ tests with zero mismatches
 */
contract DifferentialSimpleStorage is YulTestBase {
    // Compiled contract
    address simpleStorage;

    // Test counter
    uint256 public testsPassed;
    uint256 public testsFailed;

    // Storage state tracking for EDSL interpreter
    mapping(uint256 => uint256) edslStorage;

    function setUp() public {
        // Deploy SimpleStorage from Yul using YulTestBase helper
        simpleStorage = deployYul("SimpleStorage");
        require(simpleStorage != address(0), "Deploy failed");
    }

    /**
     * @notice Execute transaction on EVM and EDSL, compare results
     */
    function executeDifferentialTest(
        string memory functionName,
        address sender,
        uint256 arg0
    ) internal returns (bool success) {
        // 1. Execute on compiled contract (EVM)
        vm.prank(sender);

        bool evmSuccess;
        bytes memory evmReturnData;
        uint256 evmStorageBefore = uint256(vm.load(simpleStorage, bytes32(uint256(0))));

        if (keccak256(bytes(functionName)) == keccak256(bytes("store"))) {
            (evmSuccess, evmReturnData) = simpleStorage.call(
                abi.encodeWithSignature("store(uint256)", arg0)
            );
        } else if (keccak256(bytes(functionName)) == keccak256(bytes("retrieve"))) {
            (evmSuccess, evmReturnData) = simpleStorage.call(
                abi.encodeWithSignature("retrieve()")
            );
        } else {
            revert("Unknown function");
        }

        uint256 evmStorageAfter = uint256(vm.load(simpleStorage, bytes32(uint256(0))));
        uint256 evmReturnValue = evmReturnData.length > 0 ? abi.decode(evmReturnData, (uint256)) : 0;

        // 2. Execute on EDSL interpreter (via vm.ffi)
        // Build storage state string: "slot:value,..." for all non-zero slots
        string memory storageState = _buildStorageString();

        // Build command with storage state (use relative paths for CI compatibility)
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";
        inputs[2] = string.concat(
            "cd \"$(git rev-parse --show-toplevel)\" && export PATH=\"$HOME/.elan/bin:$PATH\" && lake exe difftest-interpreter SimpleStorage ",
            functionName,
            " ",
            vm.toString(sender),
            " ",
            vm.toString(arg0),
            " \"",
            storageState,
            "\""
        );

        // Call Lean interpreter
        bytes memory edslResultBytes = vm.ffi(inputs);
        string memory edslResult = string(edslResultBytes);

        // 3. Parse and compare results
        // The EDSL interpreter returns JSON like:
        // {"success":true,"returnValue":"42","revertReason":null,"storageChanges":[{"slot":0,"value":42}]}

        console2.log("EVM success:", evmSuccess);
        console2.log("EVM storage change:", evmStorageAfter);
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
        // Parse EDSL storage changes from JSON and update tracking
        uint256 edslStorageChange = _extractStorageChange(edslResult, 0);
        if (edslStorageChange != type(uint256).max) {
            // EDSL reported a storage change, update our tracking
            edslStorage[0] = edslStorageChange;
        }

        // Now validate: EVM final storage must match EDSL final storage
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

    /**
     * @notice Extract returnValue from JSON
     * Parses: "returnValue":"42" or "returnValue":null
     */
    function _extractReturnValue(string memory json) internal pure returns (uint256) {
        bytes memory jsonBytes = bytes(json);
        bytes memory searchBytes = bytes("\"returnValue\":\"");

        // Find "returnValue":"
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
                // Extract number until next quote
                uint start = i + searchBytes.length;
                uint end = start;
                while (end < jsonBytes.length && jsonBytes[end] != bytes1('"')) {
                    end++;
                }
                // Convert to uint
                bytes memory numBytes = new bytes(end - start);
                for (uint k = 0; k < end - start; k++) {
                    numBytes[k] = jsonBytes[start + k];
                }
                return _stringToUint(string(numBytes));
            }
        }
        return 0; // Default if not found or null
    }

    /**
     * @notice Convert string to uint
     */
    function _stringToUint(string memory s) internal pure returns (uint256) {
        bytes memory b = bytes(s);
        uint256 result = 0;
        for (uint i = 0; i < b.length; i++) {
            uint8 c = uint8(b[i]);
            if (c >= 48 && c <= 57) {
                result = result * 10 + (c - 48);
            }
        }
        return result;
    }

    /**
     * @notice Extract storage change for a specific slot from JSON
     * Parses: "storageChanges":[{"slot":0,"value":42}]
     * Returns type(uint256).max if slot not found in changes
     */
    function _extractStorageChange(string memory json, uint256 slot) internal pure returns (uint256) {
        bytes memory jsonBytes = bytes(json);
        bytes memory slotPattern = bytes(string.concat("\"slot\":", vm.toString(slot)));

        // Find the slot pattern
        if (jsonBytes.length < slotPattern.length) return type(uint256).max;
        for (uint i = 0; i <= jsonBytes.length - slotPattern.length; i++) {
            bool found = true;
            for (uint j = 0; j < slotPattern.length; j++) {
                if (jsonBytes[i + j] != slotPattern[j]) {
                    found = false;
                    break;
                }
            }
            if (found) {
                // Found the slot, now find the value after it
                // Look for "value": pattern
                bytes memory valuePattern = bytes("\"value\":");
                if (jsonBytes.length < valuePattern.length) return type(uint256).max;
                for (uint k = i; k <= jsonBytes.length - valuePattern.length; k++) {
                    bool valueFound = true;
                    for (uint l = 0; l < valuePattern.length; l++) {
                        if (jsonBytes[k + l] != valuePattern[l]) {
                            valueFound = false;
                            break;
                        }
                    }
                    if (valueFound) {
                        // Extract the number after "value":
                        uint start = k + valuePattern.length;
                        uint end = start;
                        while (end < jsonBytes.length && jsonBytes[end] >= 0x30 && jsonBytes[end] <= 0x39) {
                            end++;
                        }
                        bytes memory numBytes = new bytes(end - start);
                        for (uint m = 0; m < end - start; m++) {
                            numBytes[m] = jsonBytes[start + m];
                        }
                        return _stringToUint(string(numBytes));
                    }
                }
            }
        }
        return type(uint256).max; // Not found
    }

    /**
     * @notice Build storage state string for EDSL interpreter
     * Format: "slot:value,slot:value,..."
     */
    function _buildStorageString() internal view returns (string memory) {
        // For SimpleStorage, only slot 0 matters
        uint256 val = edslStorage[0];
        if (val == 0) {
            return "";
        }
        return string.concat("0:", vm.toString(val));
    }

    /**
     * @notice Simple string contains check
     */
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
     * @notice Run differential tests with fixed transactions
     */
    function testDifferential_BasicOperations() public {
        // Test store
        bool success1 = executeDifferentialTest("store", address(0xA11CE), 42);
        assertTrue(success1, "Store test 1 failed");

        // Test retrieve
        bool success2 = executeDifferentialTest("retrieve", address(0xA11CE), 0);
        assertTrue(success2, "Retrieve test 1 failed");

        // Test overwrite
        bool success3 = executeDifferentialTest("store", address(0xB0B), 100);
        assertTrue(success3, "Store test 2 failed");

        bool success4 = executeDifferentialTest("retrieve", address(0xB0B), 0);
        assertTrue(success4, "Retrieve test 2 failed");

        console2.log("Differential tests passed:", testsPassed);
    }

    /**
     * @notice Run 100 random differential tests
     */
    function testDifferential_Random100() public {
        _runRandomDifferentialTests(100, 42);
    }

    /**
     * @notice Run 1000 random differential tests (slow)
     * @dev Uncomment when ready for full-scale testing
     */
    /*
    function testDifferential_Random1000() public {
        _runRandomDifferentialTests(1000, 42);
    }
    */

    /**
     * @notice Execute N random transactions via random-gen
     */
    function _runRandomDifferentialTests(uint256 count, uint256 seed) internal {
        // Generate random transactions via Lean random-gen (disabled - use inline PRNG for CI)
        // string[] memory inputs = new string[](3);
        // inputs[0] = "bash";
        // inputs[1] = "-c";
        // inputs[2] = string.concat(
        //     "export PATH=\"$HOME/.elan/bin:$PATH\" && lake exe random-gen SimpleStorage ",
        //     vm.toString(count),
        //     " ",
        //     vm.toString(seed)
        // );
        // bytes memory txJsonBytes = vm.ffi(inputs);
        // string memory txJson = string(txJsonBytes);

        console2.log("Generated", count, "random transactions");

        // Parse JSON array and execute each transaction
        // JSON format: [{"sender":"0xAlice","function":"store","args":[42]}, ...]
        // For simplicity, we'll just split by transactions and parse manually

        // For now, execute a simpler approach: generate them one-by-one inline
        // This avoids complex JSON parsing in Solidity

        uint256 prng = seed;
        for (uint256 i = 0; i < count; i++) {
            // Simple PRNG matching Lean's LCG + generation order
            prng = (1103515245 * prng + 12345) % (2**31);

            // Generate address (Lean: genAddress)
            address sender = _indexToAddress(prng % 5);

            // Determine function (Lean: genBool)
            prng = (1103515245 * prng + 12345) % (2**31);
            bool isStore = (prng % 2) == 0;

            if (isStore) {
                // Generate value (Lean: genUint256)
                prng = (1103515245 * prng + 12345) % (2**31);
                uint256 value = prng % 1000000;

                bool success = executeDifferentialTest("store", sender, value);
                assertTrue(success, "Random store test failed");
            } else {
                bool success = executeDifferentialTest("retrieve", sender, 0);
                assertTrue(success, "Random retrieve test failed");
            }
        }

        console2.log("Random differential tests completed:", testsPassed);
        console2.log("Failed:", testsFailed);
        assertEq(testsFailed, 0, "Some random tests failed");
    }

    /**
     * @notice Convert index to test address
     */
    function _indexToAddress(uint256 index) internal pure returns (address) {
        if (index == 0) return address(0xA11CE);
        if (index == 1) return address(0xB0B);
        if (index == 2) return address(0xCA401);
        if (index == 3) return address(0xDABE);
        return address(0xEBE);
    }
}
