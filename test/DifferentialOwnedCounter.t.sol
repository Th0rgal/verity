// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./yul/YulTestBase.sol";

/**
 * @title DifferentialOwnedCounter
 * @notice Differential testing for OwnedCounter contract
 *
 * Approach:
 * 1. Generate random transactions (increment, decrement, getCount, getOwner, transferOwnership)
 * 2. Execute on compiled Yul contract (EVM)
 * 3. Execute on EDSL interpreter (via vm.ffi)
 * 4. Assert identical results (including both storage slots)
 *
 * Success: 100+ tests with zero mismatches
 */
contract DifferentialOwnedCounter is YulTestBase, DiffTestConfig {
    // Compiled contract
    address ownedCounter;

    // Test counters
    uint256 public testsPassed;
    uint256 public testsFailed;

    // Storage state tracking for EDSL interpreter
    mapping(uint256 => uint256) edslStorage;      // Slot 1: count
    mapping(uint256 => address) edslStorageAddr;  // Slot 0: owner address

    function setUp() public {
        // Deploy OwnedCounter from Yul using YulTestBase helper
        ownedCounter = deployYul("OwnedCounter");
        require(ownedCounter != address(0), "Deploy failed");

        // Initialize owner to the test contract (msg.sender)
        address initialOwner = address(this);

        // Set EVM state
        bytes32 ownerSlot = bytes32(uint256(0));
        vm.store(ownedCounter, ownerSlot, bytes32(uint256(uint160(initialOwner))));

        // Set EDSL state
        edslStorageAddr[0] = initialOwner;
        edslStorage[1] = 0;  // Initial count
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

        bytes32 functionSig = keccak256(bytes(functionName));

        if (functionSig == keccak256(bytes("increment"))) {
            (evmSuccess, evmReturnData) = ownedCounter.call(
                abi.encodeWithSignature("increment()")
            );
        } else if (functionSig == keccak256(bytes("decrement"))) {
            (evmSuccess, evmReturnData) = ownedCounter.call(
                abi.encodeWithSignature("decrement()")
            );
        } else if (functionSig == keccak256(bytes("getCount"))) {
            (evmSuccess, evmReturnData) = ownedCounter.call(
                abi.encodeWithSignature("getCount()")
            );
        } else if (functionSig == keccak256(bytes("getOwner"))) {
            (evmSuccess, evmReturnData) = ownedCounter.call(
                abi.encodeWithSignature("getOwner()")
            );
        } else if (functionSig == keccak256(bytes("transferOwnership"))) {
            (evmSuccess, evmReturnData) = ownedCounter.call(
                abi.encodeWithSignature("transferOwnership(address)", address(uint160(arg0)))
            );
        } else {
            revert("Unknown function");
        }

        uint256 evmStorageAfter = uint256(vm.load(ownedCounter, bytes32(uint256(1))));  // count at slot 1
        address evmOwnerAfter = address(uint160(uint256(vm.load(ownedCounter, bytes32(uint256(0))))));  // owner at slot 0
        uint256 evmReturnValue = 0;
        address evmReturnAddress = address(0);

        if (evmReturnData.length > 0) {
            if (functionSig == keccak256(bytes("getOwner"))) {
                evmReturnAddress = abi.decode(evmReturnData, (address));
            } else {
                evmReturnValue = abi.decode(evmReturnData, (uint256));
            }
        }

        // 2. Execute on EDSL interpreter (via vm.ffi)
        string memory storageState = _buildStorageString();
        string memory edslResult = _runInterpreter(functionName, sender, arg0, storageState);

        // 3. Parse and compare results
        bool verbose = _diffVerbose();
        if (verbose) {
            console2.log("Function:", functionName);
            console2.log("EVM success:", evmSuccess);
            console2.log("EVM storage[1]:", evmStorageAfter);
            console2.log("EVM owner:", evmOwnerAfter);
            console2.log("EDSL result:", edslResult);
        }

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

        // Validate: Return values must match (for getCount and getOwner)
        if (functionSig == keccak256(bytes("getCount"))) {
            if (evmReturnValue != edslReturnValue) {
                console2.log("MISMATCH: Return values differ!");
                console2.log("  EVM:", evmReturnValue);
                console2.log("  EDSL:", edslReturnValue);
                testsFailed++;
                return false;
            }
        } else if (functionSig == keccak256(bytes("getOwner"))) {
            // For getOwner, compare address returned vs stored in EDSL
            if (uint256(uint160(evmReturnAddress)) != edslReturnValue) {
                console2.log("MISMATCH: Owner addresses differ!");
                console2.log("  EVM:", evmReturnAddress);
                console2.log("  EDSL:", address(uint160(edslReturnValue)));
                testsFailed++;
                return false;
            }
        }

        // Validate: Storage changes must match
        (bool hasCountChange, uint256 edslCountChange) = _extractStorageChange(edslResult, 1);
        if (hasCountChange) {
            edslStorage[1] = edslCountChange;
        }

        (bool hasOwnerChange, uint256 edslOwnerChangeNat) = _extractStorageAddrChange(edslResult, 0);
        if (hasOwnerChange) {
            edslStorageAddr[0] = address(uint160(edslOwnerChangeNat));
        }

        // Validate: EVM final storage must match EDSL final storage
        if (evmStorageAfter != edslStorage[1]) {
            console2.log("MISMATCH: Count storage differs!");
            console2.log("  EVM storage[1]:", evmStorageAfter);
            console2.log("  EDSL storage[1]:", edslStorage[1]);
            testsFailed++;
            return false;
        }

        if (evmOwnerAfter != edslStorageAddr[0]) {
            console2.log("MISMATCH: Owner storage differs!");
            console2.log("  EVM owner:", evmOwnerAfter);
            console2.log("  EDSL owner:", edslStorageAddr[0]);
            testsFailed++;
            return false;
        }

        testsPassed++;
        return true;
    }

    function _runInterpreter(
        string memory functionName,
        address sender,
        uint256 arg0,
        string memory storageState
    ) internal returns (string memory) {
        // Build command with storage state
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";

        // Build args string based on function
        string memory argsStr;
        bytes32 functionSig = keccak256(bytes(functionName));

        if (functionSig == keccak256(bytes("transferOwnership"))) {
            // One address arg
            argsStr = string.concat(
                vm.toString(arg0),
                bytes(storageState).length > 0 ? string.concat(" ", storageState) : ""
            );
        } else {
            // No args (increment, decrement, getCount, getOwner)
            argsStr = bytes(storageState).length > 0 ? storageState : "";
        }

        inputs[2] = string.concat(
            "cd \"$(git rev-parse --show-toplevel)\" && export PATH=\"$HOME/.elan/bin:$PATH\" && ",
            "if [ ! -x ./.lake/build/bin/difftest-interpreter ]; then ",
            "mkdir -p .lake/build/bin && lake build difftest-interpreter >/dev/null; ",
            "fi; ",
            "./.lake/build/bin/difftest-interpreter",
            " OwnedCounter ",
            functionName,
            " ",
            vm.toString(sender),
            bytes(argsStr).length > 0 ? string.concat(" ", argsStr) : "",
            " value=0 timestamp=",
            vm.toString(block.timestamp)
        );

        bytes memory result = vm.ffi(inputs);
        return string(result);
    }

    function _extractStorageAddrChange(string memory json, uint256 slot) internal pure returns (bool, uint256) {
        bytes memory jsonBytes = bytes(json);
        bytes memory slotPattern = bytes(string.concat("\"slot\":", vm.toString(slot)));

        // Look for the slot in storageAddrChanges
        if (!contains(json, "\"storageAddrChanges\"")) {
            return (false, 0);
        }

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
                        // Extract value (can be decimal number or hex address)
                        uint start = k + valuePattern.length;
                        // Skip quote if present
                        if (start < jsonBytes.length && jsonBytes[start] == '"') {
                            start++;
                        }

                        // Find end of value (ends with quote, comma, or brace)
                        uint end = start;
                        while (end < jsonBytes.length &&
                               jsonBytes[end] != '"' &&
                               jsonBytes[end] != ',' &&
                               jsonBytes[end] != '}') {
                            end++;
                        }

                        bytes memory valueBytes = new bytes(end - start);
                        for (uint m = 0; m < end - start; m++) {
                            valueBytes[m] = jsonBytes[start + m];
                        }

                        // Parse value (try hex first, then decimal)
                        string memory valueStr = string(valueBytes);
                        uint256 addrNat;

                        // Check if it starts with 0x (hex)
                        if (valueBytes.length >= 2 && valueBytes[0] == '0' &&
                            (valueBytes[1] == 'x' || valueBytes[1] == 'X')) {
                            addrNat = _parseHexAddress(valueStr);
                        } else {
                            // Parse as decimal
                            addrNat = _stringToUint(valueStr);
                        }

                        return (true, addrNat);
                    }
                }
            }
        }
        return (false, 0);
    }

    function _parseHexAddress(string memory hexStr) internal pure returns (uint256) {
        bytes memory b = bytes(hexStr);
        uint256 result = 0;

        // Skip "0x" prefix if present
        uint start = 0;
        if (b.length >= 2 && b[0] == '0' && (b[1] == 'x' || b[1] == 'X')) {
            start = 2;
        }

        for (uint i = start; i < b.length; i++) {
            result = result * 16;
            uint8 c = uint8(b[i]);
            if (c >= 48 && c <= 57) {
                result += c - 48;  // 0-9
            } else if (c >= 65 && c <= 70) {
                result += c - 55;  // A-F
            } else if (c >= 97 && c <= 102) {
                result += c - 87;  // a-f
            }
        }

        return result;
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

                // Check if it's a hex address (starts with 0x)
                bool isHexAddr = false;
                if (end + 1 < jsonBytes.length && jsonBytes[end] == '0' &&
                    (jsonBytes[end+1] == 'x' || jsonBytes[end+1] == 'X')) {
                    isHexAddr = true;
                }

                while (end < jsonBytes.length && jsonBytes[end] != bytes1('"')) {
                    end++;
                }
                bytes memory numBytes = new bytes(end - start);
                for (uint k = 0; k < end - start; k++) {
                    numBytes[k] = jsonBytes[start + k];
                }

                if (isHexAddr) {
                    return _parseHexAddress(string(numBytes));
                } else {
                    return _stringToUint(string(numBytes));
                }
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
        // Build storage string: addr="slot:value" "slot:value"
        string memory result = "";

        // Add owner address storage (slot 0)
        address owner = edslStorageAddr[0];
        if (owner != address(0)) {
            result = string.concat(
                "addr=\"0:",
                _toLowerCase(vm.toString(owner)),
                "\""
            );
        }

        // Add count storage (slot 1)
        uint256 count = edslStorage[1];
        if (count != 0 || bytes(result).length == 0) {
            if (bytes(result).length > 0) {
                result = string.concat(result, " ");
            }
            result = string.concat(
                result,
                "\"1:",
                vm.toString(count),
                "\""
            );
        }

        return result;
    }

    function _toLowerCase(string memory str) internal pure returns (string memory) {
        bytes memory bStr = bytes(str);
        bytes memory bLower = new bytes(bStr.length);
        for (uint i = 0; i < bStr.length; i++) {
            // Convert A-F to a-f
            if (bStr[i] >= 0x41 && bStr[i] <= 0x46) {
                bLower[i] = bytes1(uint8(bStr[i]) + 32);
            } else {
                bLower[i] = bStr[i];
            }
        }
        return string(bLower);
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

    // ============ Test Cases ============

    function testDifferential_Increment() public {
        address owner = address(this);

        bool success = executeDifferentialTest("increment", owner, 0);
        assertTrue(success, "Increment test failed");
    }

    function testDifferential_IncrementAndDecrement() public {
        address owner = address(this);

        // Increment
        bool success1 = executeDifferentialTest("increment", owner, 0);
        assertTrue(success1, "Increment failed");

        // Increment again
        bool success2 = executeDifferentialTest("increment", owner, 0);
        assertTrue(success2, "Second increment failed");

        // Decrement
        bool success3 = executeDifferentialTest("decrement", owner, 0);
        assertTrue(success3, "Decrement failed");
    }

    function testDifferential_AccessControl() public {
        address owner = address(this);
        address nonOwner = address(0xB0B);

        // Owner can increment
        bool success1 = executeDifferentialTest("increment", owner, 0);
        assertTrue(success1, "Owner increment failed");

        // Non-owner cannot increment (should revert)
        bool success2 = executeDifferentialTest("increment", nonOwner, 0);
        assertTrue(success2, "Access control test failed");
    }

    function testDifferential_TransferOwnership() public {
        address originalOwner = address(this);
        address newOwner = address(0xA11CE);

        // Original owner increments
        bool success1 = executeDifferentialTest("increment", originalOwner, 0);
        assertTrue(success1, "Initial increment failed");

        // Transfer ownership
        bool success2 = executeDifferentialTest("transferOwnership", originalOwner, uint256(uint160(newOwner)));
        assertTrue(success2, "Transfer ownership failed");

        // New owner can increment
        bool success3 = executeDifferentialTest("increment", newOwner, 0);
        assertTrue(success3, "New owner increment failed");

        // Original owner cannot increment anymore
        bool success4 = executeDifferentialTest("increment", originalOwner, 0);
        assertTrue(success4, "Post-transfer access control failed");
    }

    function testDifferential_GetOperations() public {
        address owner = address(this);

        // Increment a few times
        executeDifferentialTest("increment", owner, 0);
        executeDifferentialTest("increment", owner, 0);
        executeDifferentialTest("increment", owner, 0);

        // Get count
        bool success1 = executeDifferentialTest("getCount", owner, 0);
        assertTrue(success1, "GetCount failed");

        // Get owner
        bool success2 = executeDifferentialTest("getOwner", owner, 0);
        assertTrue(success2, "GetOwner failed");
    }

    function testDifferential_Random100() public {
        address[] memory actors = new address[](3);
        actors[0] = address(this);  // Owner
        actors[1] = address(0xA11CE);
        actors[2] = address(0xB0B);

        (uint256 startIndex, uint256 count) = _diffRandomSmallRange();
        uint256 seed = _diffRandomSeed("OwnedCounter");
        for (uint256 i = 0; i < count; i++) {
            // Generate random transaction
            (string memory funcName, address sender, uint256 arg) =
                _randomTransaction(seed + startIndex + i, actors);

            bool success = executeDifferentialTest(funcName, sender, arg);
            _assertRandomSuccess(success, startIndex + i);
        }

        console2.log("Random tests passed:", testsPassed);
        console2.log("Random tests failed:", testsFailed);
        assertEq(testsFailed, 0, "Some random tests failed");
    }

    function testDifferential_Random10000() public {
        address[] memory actors = new address[](3);
        actors[0] = address(this);  // Owner
        actors[1] = address(0xA11CE);
        actors[2] = address(0xB0B);

        (uint256 startIndex, uint256 count) = _diffRandomLargeRange();
        uint256 seed = _diffRandomSeed("OwnedCounter");
        for (uint256 i = 0; i < count; i++) {
            // Generate random transaction
            (string memory funcName, address sender, uint256 arg) =
                _randomTransaction(seed + startIndex + i, actors);

            bool success = executeDifferentialTest(funcName, sender, arg);
            _assertRandomSuccess(success, startIndex + i);
        }

        console2.log("Random tests passed:", testsPassed);
        console2.log("Random tests failed:", testsFailed);
        assertEq(testsFailed, 0, "Some random tests failed");
    }

    function _randomTransaction(uint256 seed, address[] memory actors)
        internal
        view
        returns (string memory funcName, address sender, uint256 arg)
    {
        uint256 rand1 = _lcg(seed);
        uint256 rand2 = _lcg(rand1);
        uint256 rand3 = _lcg(rand2);

        // Choose function (30% increment, 25% decrement, 20% getCount, 15% getOwner, 10% transferOwnership)
        uint256 funcChoice = rand1 % 100;
        if (funcChoice < 30) {
            funcName = "increment";
            arg = 0;
        } else if (funcChoice < 55) {
            funcName = "decrement";
            arg = 0;
        } else if (funcChoice < 75) {
            funcName = "getCount";
            arg = 0;
        } else if (funcChoice < 90) {
            funcName = "getOwner";
            arg = 0;
        } else {
            funcName = "transferOwnership";
            // Choose a new owner
            arg = uint256(uint160(actors[rand3 % actors.length]));
        }

        // Choose sender (70% current owner, 30% random actor)
        uint256 senderChoice = rand2 % 100;
        if (senderChoice < 70) {
            sender = edslStorageAddr[0];  // Current owner
        } else {
            sender = actors[rand2 % actors.length];
        }
    }
}
