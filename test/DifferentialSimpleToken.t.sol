// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./yul/YulTestBase.sol";

/**
 * @title DifferentialSimpleToken
 * @notice Differential testing for SimpleToken contract
 *
 * Approach:
 * 1. Generate random transactions (mint, transfer, balanceOf, totalSupply, owner)
 * 2. Execute on compiled Yul contract (EVM)
 * 3. Execute on EDSL interpreter (via vm.ffi)
 * 4. Assert identical results (including mappings, owner, and totalSupply)
 *
 * Success: 100+ tests with zero mismatches
 */
contract DifferentialSimpleToken is YulTestBase, DiffTestConfig {
    // Compiled contract
    address simpleToken;

    // Test counters
    uint256 public testsPassed;
    uint256 public testsFailed;

    // Storage state tracking for EDSL interpreter
    mapping(address => uint256) edslBalances;      // Mapping slot 1: balances
    mapping(uint256 => address) edslStorageAddr;   // Slot 0: owner address
    mapping(uint256 => uint256) edslStorage;       // Slot 2: totalSupply

    function setUp() public {
        // Deploy SimpleToken from Yul with constructor arg (initialOwner)
        address initialOwner = address(this);
        simpleToken = deployYulWithArgs("SimpleToken", abi.encode(initialOwner));
        require(simpleToken != address(0), "Deploy failed");

        // Set EDSL state
        edslStorageAddr[0] = initialOwner;
        edslStorage[2] = 0;  // Initial totalSupply
    }

    /**
     * @notice Execute transaction on EVM and EDSL, compare results
     */
    function executeDifferentialTest(
        string memory functionName,
        address sender,
        address arg0Addr,
        uint256 arg1
    ) internal returns (bool success) {
        // 1. Execute on compiled contract (EVM)
        vm.prank(sender);

        bool evmSuccess;
        bytes memory evmReturnData;

        bytes32 functionSig = keccak256(bytes(functionName));

        if (functionSig == keccak256(bytes("mint"))) {
            (evmSuccess, evmReturnData) = simpleToken.call(
                abi.encodeWithSignature("mint(address,uint256)", arg0Addr, arg1)
            );
        } else if (functionSig == keccak256(bytes("transfer"))) {
            (evmSuccess, evmReturnData) = simpleToken.call(
                abi.encodeWithSignature("transfer(address,uint256)", arg0Addr, arg1)
            );
        } else if (functionSig == keccak256(bytes("balanceOf"))) {
            (evmSuccess, evmReturnData) = simpleToken.call(
                abi.encodeWithSignature("balanceOf(address)", arg0Addr)
            );
        } else if (functionSig == keccak256(bytes("totalSupply"))) {
            (evmSuccess, evmReturnData) = simpleToken.call(
                abi.encodeWithSignature("totalSupply()")
            );
        } else if (functionSig == keccak256(bytes("owner"))) {
            (evmSuccess, evmReturnData) = simpleToken.call(
                abi.encodeWithSignature("owner()")
            );
        } else {
            revert("Unknown function");
        }

        uint256 evmReturnValue = 0;
        address evmReturnAddress = address(0);

        if (evmReturnData.length > 0) {
            if (functionSig == keccak256(bytes("owner"))) {
                evmReturnAddress = abi.decode(evmReturnData, (address));
            } else {
                evmReturnValue = abi.decode(evmReturnData, (uint256));
            }
        }

        // Get EVM state after transaction
        uint256 evmTotalSupply = uint256(vm.load(simpleToken, bytes32(uint256(2))));
        address evmOwner = address(uint160(uint256(vm.load(simpleToken, bytes32(uint256(0))))));

        // Get EVM mapping storage for relevant addresses
        uint256 evmSenderBalance = 0;
        uint256 evmRecipientBalance = 0;

        bytes32 senderSlot = keccak256(abi.encode(sender, uint256(1)));
        evmSenderBalance = uint256(vm.load(simpleToken, senderSlot));

        if (arg0Addr != address(0)) {
            bytes32 recipientSlot = keccak256(abi.encode(arg0Addr, uint256(1)));
            evmRecipientBalance = uint256(vm.load(simpleToken, recipientSlot));
        }

        // 2. Execute on EDSL interpreter (via vm.ffi)
        string memory storageState = _buildStorageString(sender, arg0Addr);
        string memory edslResult = _runInterpreter(functionName, sender, arg0Addr, arg1, storageState);

        // 3. Parse and compare results
        console2.log("Function:", functionName);
        console2.log("EVM success:", evmSuccess);
        console2.log("EVM totalSupply:", evmTotalSupply);
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
        if (functionSig == keccak256(bytes("balanceOf")) || functionSig == keccak256(bytes("totalSupply"))) {
            if (evmReturnValue != edslReturnValue) {
                console2.log("MISMATCH: Return values differ!");
                console2.log("  EVM:", evmReturnValue);
                console2.log("  EDSL:", edslReturnValue);
                testsFailed++;
                return false;
            }
        } else if (functionSig == keccak256(bytes("owner"))) {
            if (uint256(uint160(evmReturnAddress)) != edslReturnValue) {
                console2.log("MISMATCH: Owner addresses differ!");
                console2.log("  EVM:", evmReturnAddress);
                console2.log("  EDSL:", address(uint160(edslReturnValue)));
                testsFailed++;
                return false;
            }
        }

        // Validate: Storage changes must match
        (bool hasTotalSupplyChange, uint256 edslTotalSupplyChange) = _extractStorageChange(edslResult, 2);
        if (hasTotalSupplyChange) {
            edslStorage[2] = edslTotalSupplyChange;
        }

        (bool hasOwnerChange, uint256 edslOwnerChangeNat) = _extractStorageAddrChange(edslResult, 0);
        if (hasOwnerChange) {
            edslStorageAddr[0] = address(uint160(edslOwnerChangeNat));
        }

        // Validate: Mapping storage changes must match
        _updateEDSLMappingStorage(edslResult, sender, arg0Addr);

        // Validate: EVM final storage must match EDSL final storage
        if (evmTotalSupply != edslStorage[2]) {
            console2.log("MISMATCH: TotalSupply differs!");
            console2.log("  EVM totalSupply:", evmTotalSupply);
            console2.log("  EDSL totalSupply:", edslStorage[2]);
            testsFailed++;
            return false;
        }

        if (evmOwner != edslStorageAddr[0]) {
            console2.log("MISMATCH: Owner differs!");
            console2.log("  EVM owner:", evmOwner);
            console2.log("  EDSL owner:", edslStorageAddr[0]);
            testsFailed++;
            return false;
        }

        if (evmSenderBalance != edslBalances[sender]) {
            console2.log("MISMATCH: Sender balance differs!");
            console2.log("  EVM sender balance:", evmSenderBalance);
            console2.log("  EDSL sender balance:", edslBalances[sender]);
            testsFailed++;
            return false;
        }

        if (arg0Addr != address(0) && arg0Addr != sender &&
            evmRecipientBalance != edslBalances[arg0Addr]) {
            console2.log("MISMATCH: Recipient balance differs!");
            console2.log("  EVM recipient balance:", evmRecipientBalance);
            console2.log("  EDSL recipient balance:", edslBalances[arg0Addr]);
            testsFailed++;
            return false;
        }

        testsPassed++;
        return true;
    }

    function _runInterpreter(
        string memory functionName,
        address sender,
        address arg0Addr,
        uint256 arg1,
        string memory storageState
    ) internal returns (string memory) {
        // Build command with storage state
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";

        // Build args string based on function
        string memory argsStr;
        bytes32 functionSig = keccak256(bytes(functionName));

        if (functionSig == keccak256(bytes("mint"))) {
            // Two args: address, uint256
            argsStr = string.concat(
                vm.toString(uint256(uint160(arg0Addr))),
                " ",
                vm.toString(arg1),
                bytes(storageState).length > 0 ? string.concat(" ", storageState) : ""
            );
        } else if (functionSig == keccak256(bytes("transfer"))) {
            // Two args: address, uint256
            argsStr = string.concat(
                vm.toString(uint256(uint160(arg0Addr))),
                " ",
                vm.toString(arg1),
                bytes(storageState).length > 0 ? string.concat(" ", storageState) : ""
            );
        } else if (functionSig == keccak256(bytes("balanceOf"))) {
            // One address arg
            argsStr = string.concat(
                vm.toString(uint256(uint160(arg0Addr))),
                bytes(storageState).length > 0 ? string.concat(" ", storageState) : ""
            );
        } else {
            // No args (totalSupply, owner)
            argsStr = bytes(storageState).length > 0 ? storageState : "";
        }

        inputs[2] = string.concat(
            "cd \"$(git rev-parse --show-toplevel)\" && export PATH=\"$HOME/.elan/bin:$PATH\" && ",
            "if [ ! -x ./.lake/build/bin/difftest-interpreter ]; then ",
            "mkdir -p .lake/build/bin && lake build difftest-interpreter >/dev/null; ",
            "fi; ",
            "./.lake/build/bin/difftest-interpreter",
            " SimpleToken ",
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

    function _buildStorageString(address sender, address other) internal view returns (string memory) {
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

        // Add totalSupply storage (slot 2)
        uint256 totalSupply = edslStorage[2];
        if (bytes(result).length > 0) {
            result = string.concat(result, " ");
        }
        result = string.concat(
            result,
            "\"2:",
            vm.toString(totalSupply),
            "\""
        );

        // Add mapping storage (slot 1: balances)
        string memory mappingStr = _buildMappingStorageString(sender, other);
        if (bytes(mappingStr).length > 0) {
            result = string.concat(
                result,
                " map=\"",
                mappingStr,
                "\""
            );
        }

        return result;
    }

    function _buildMappingStorageString(address sender, address other) internal view returns (string memory) {
        // Build mapping storage string in format: "slot:key:value,slot:key:value,..."
        // For SimpleToken balances mapping at slot 1
        string memory result = "";
        bool first = true;

        // Add sender's balance if non-zero
        if (edslBalances[sender] > 0) {
            result = string.concat(
                "1:",
                _toLowerCase(vm.toString(sender)),
                ":",
                vm.toString(edslBalances[sender])
            );
            first = false;
        }

        // Add other address's balance if non-zero and different from sender
        if (other != address(0) && other != sender && edslBalances[other] > 0) {
            if (!first) {
                result = string.concat(result, ",");
            }
            result = string.concat(
                result,
                "1:",
                _toLowerCase(vm.toString(other)),
                ":",
                vm.toString(edslBalances[other])
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

    function _updateEDSLMappingStorage(string memory edslResult, address sender, address other) internal {
        // Parse mappingChanges from EDSL result
        if (!contains(edslResult, "\"mappingChanges\":")) {
            return;
        }

        // Extract sender balance if changed
        string memory senderAddrStr = _toLowerCase(vm.toString(sender));
        if (contains(edslResult, senderAddrStr) || contains(edslResult, vm.toString(sender))) {
            uint256 senderValue = _extractMappingValue(edslResult, sender);
            edslBalances[sender] = senderValue;
        }

        // Extract other address balance if changed
        if (other != address(0)) {
            string memory otherAddrStr = _toLowerCase(vm.toString(other));
            if (contains(edslResult, otherAddrStr) || contains(edslResult, vm.toString(other))) {
                uint256 otherValue = _extractMappingValue(edslResult, other);
                edslBalances[other] = otherValue;
            }
        }
    }

    function _extractMappingValue(string memory json, address key) internal pure returns (uint256) {
        // Simple parser: find "key":"0x..." pattern and extract the following "value":number
        bytes memory jsonBytes = bytes(json);
        bytes memory keyBytes = bytes(vm.toString(key));
        bytes memory keyBytesLower = bytes(_toLowerCase(vm.toString(key)));

        // Find the key in the JSON (try both cases)
        for (uint i = 0; i < jsonBytes.length - keyBytes.length; i++) {
            bool found = true;
            bool foundLower = true;
            for (uint j = 0; j < keyBytes.length; j++) {
                if (jsonBytes[i + j] != keyBytes[j]) {
                    found = false;
                }
                if (jsonBytes[i + j] != keyBytesLower[j]) {
                    foundLower = false;
                }
            }
            if (found || foundLower) {
                // Found key, now find the value
                for (uint k = i + keyBytes.length; k < jsonBytes.length - 7; k++) {
                    if (jsonBytes[k] == '"' && jsonBytes[k+1] == 'v' &&
                        jsonBytes[k+2] == 'a' && jsonBytes[k+3] == 'l' &&
                        jsonBytes[k+4] == 'u' && jsonBytes[k+5] == 'e' &&
                        jsonBytes[k+6] == '"' && jsonBytes[k+7] == ':') {
                        return _extractNumber(json, k + 8);
                    }
                }
            }
        }
        return 0;
    }

    function _extractNumber(string memory json, uint256 startIdx) internal pure returns (uint256) {
        bytes memory jsonBytes = bytes(json);
        uint256 result = 0;
        bool foundDigit = false;

        for (uint i = startIdx; i < jsonBytes.length; i++) {
            bytes1 c = jsonBytes[i];
            if (c >= '0' && c <= '9') {
                unchecked { result = result * 10 + uint8(c) - uint8(bytes1('0')); }
                foundDigit = true;
            } else if (foundDigit) {
                break;
            }
        }
        return result;
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

    function _extractStorageAddrChange(string memory json, uint256 slot) internal pure returns (bool, uint256) {
        bytes memory jsonBytes = bytes(json);
        bytes memory slotPattern = bytes(string.concat("\"slot\":", vm.toString(slot)));

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
                        uint start = k + valuePattern.length;
                        if (start < jsonBytes.length && jsonBytes[start] == '"') {
                            start++;
                        }

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

                        string memory valueStr = string(valueBytes);
                        uint256 addrNat;

                        if (valueBytes.length >= 2 && valueBytes[0] == '0' &&
                            (valueBytes[1] == 'x' || valueBytes[1] == 'X')) {
                            addrNat = _parseHexAddress(valueStr);
                        } else {
                            addrNat = _stringToUint(valueStr);
                        }

                        return (true, addrNat);
                    }
                }
            }
        }
        return (false, 0);
    }

    // ============ Test Cases ============

    function testDifferential_Mint() public {
        address owner = address(this);
        address alice = address(0xA11CE);

        bool success = executeDifferentialTest("mint", owner, alice, 1000);
        assertTrue(success, "Mint test failed");
    }

    function testDifferential_Transfer() public {
        address owner = address(this);
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Mint to Alice
        bool success1 = executeDifferentialTest("mint", owner, alice, 1000);
        assertTrue(success1, "Mint failed");

        // Alice transfers to Bob
        bool success2 = executeDifferentialTest("transfer", alice, bob, 300);
        assertTrue(success2, "Transfer failed");
    }

    function testDifferential_SelfTransfer_NoOp() public {
        address owner = address(this);
        address alice = address(0xA11CE);

        // Mint to Alice
        bool success1 = executeDifferentialTest("mint", owner, alice, 500);
        assertTrue(success1, "Mint failed");

        // Self-transfer should be a no-op (balances + total supply unchanged)
        bool success2 = executeDifferentialTest("transfer", alice, alice, 200);
        assertTrue(success2, "Self-transfer failed");
    }

    function testDifferential_AccessControl() public {
        address owner = address(this);
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Owner can mint
        bool success1 = executeDifferentialTest("mint", owner, alice, 1000);
        assertTrue(success1, "Owner mint failed");

        // Non-owner cannot mint (should revert)
        bool success2 = executeDifferentialTest("mint", bob, alice, 500);
        assertTrue(success2, "Access control test failed");
    }

    function testDifferential_GetOperations() public {
        address owner = address(this);
        address alice = address(0xA11CE);

        // Mint some tokens
        executeDifferentialTest("mint", owner, alice, 1000);

        // Get balance
        bool success1 = executeDifferentialTest("balanceOf", owner, alice, 0);
        assertTrue(success1, "BalanceOf failed");

        // Get total supply
        bool success2 = executeDifferentialTest("totalSupply", owner, address(0), 0);
        assertTrue(success2, "GetTotalSupply failed");

        // Get owner
        bool success3 = executeDifferentialTest("owner", owner, address(0), 0);
        assertTrue(success3, "GetOwner failed");
    }

    function testDifferential_InsufficientBalance() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Try to transfer with zero balance (should revert)
        bool success = executeDifferentialTest("transfer", alice, bob, 100);
        assertTrue(success, "Insufficient balance test failed");
    }

    /**
     * @notice Exercise edge amounts for mint/transfer.
     */
    function testDifferential_EdgeAmounts() public {
        address owner = address(this);
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        uint256[] memory values = _edgeUintValues();

        bytes32 ownerSlot = bytes32(uint256(0));
        bytes32 totalSupplySlot = bytes32(uint256(2));
        bytes32 aliceSlot = keccak256(abi.encode(alice, uint256(1)));
        bytes32 bobSlot = keccak256(abi.encode(bob, uint256(1)));

        for (uint256 i = 0; i < values.length; i++) {
            uint256 amount = values[i];

            // Reset EVM state.
            vm.store(simpleToken, ownerSlot, bytes32(uint256(uint160(owner))));
            vm.store(simpleToken, totalSupplySlot, bytes32(uint256(0)));
            vm.store(simpleToken, aliceSlot, bytes32(uint256(0)));
            vm.store(simpleToken, bobSlot, bytes32(uint256(0)));

            // Reset EDSL state.
            edslStorageAddr[0] = owner;
            edslStorage[2] = 0;
            edslBalances[alice] = 0;
            edslBalances[bob] = 0;

            bool successMint = executeDifferentialTest("mint", owner, alice, amount);
            assertTrue(successMint, "Edge mint test failed");

            bool successTransfer = executeDifferentialTest("transfer", alice, bob, amount);
            assertTrue(successTransfer, "Edge transfer test failed");
        }
    }

    function testDifferential_Random100() public {
        address[] memory actors = new address[](5);
        actors[0] = address(this);  // Owner
        actors[1] = address(0xA11CE);
        actors[2] = address(0xB0B);
        actors[3] = address(0xCA401);
        actors[4] = address(0xDABE);

        (uint256 startIndex, uint256 count) = _diffRandomSmallRange();
        uint256 seed = _diffRandomSeed("SimpleToken");

        for (uint256 i = 0; i < count; i++) {
            // Generate random transaction
            (string memory funcName, address sender, address recipient, uint256 amount) =
                _randomTransaction(seed + startIndex + i, actors);

            bool success = executeDifferentialTest(funcName, sender, recipient, amount);
            _assertRandomSuccess(success, startIndex + i);
        }

        console2.log("Random tests passed:", testsPassed);
        console2.log("Random tests failed:", testsFailed);
        assertEq(testsFailed, 0, "Some random tests failed");
    }

    function testDifferential_Random10000() public {
        address[] memory actors = new address[](5);
        actors[0] = address(this);  // Owner
        actors[1] = address(0xA11CE);
        actors[2] = address(0xB0B);
        actors[3] = address(0xCA401);
        actors[4] = address(0xDABE);

        (uint256 startIndex, uint256 count) = _diffRandomLargeRange();
        uint256 seed = _diffRandomSeed("SimpleToken");

        vm.pauseGasMetering();
        for (uint256 i = 0; i < count; i++) {
            // Generate random transaction
            (string memory funcName, address sender, address recipient, uint256 amount) =
                _randomTransaction(seed + startIndex + i, actors);

            bool success = executeDifferentialTest(funcName, sender, recipient, amount);
            _assertRandomSuccess(success, startIndex + i);
        }
        vm.resumeGasMetering();

        console2.log("Random tests passed:", testsPassed);
        console2.log("Random tests failed:", testsFailed);
        assertEq(testsFailed, 0, "Some random tests failed");
    }

    function _randomTransaction(uint256 seed, address[] memory actors)
        internal
        view
        returns (string memory funcName, address sender, address recipient, uint256 amount)
    {
        uint256 rand1 = _lcg(seed);
        uint256 rand2 = _lcg(rand1);
        uint256 rand3 = _lcg(rand2);
        uint256 rand4 = _lcg(rand3);

        // Choose function (30% mint, 30% transfer, 20% balanceOf, 10% totalSupply, 10% owner)
        uint256 funcChoice = rand1 % 100;
        if (funcChoice < 30) {
            funcName = "mint";
        } else if (funcChoice < 60) {
            funcName = "transfer";
        } else if (funcChoice < 80) {
            funcName = "balanceOf";
        } else if (funcChoice < 90) {
            funcName = "totalSupply";
        } else {
            funcName = "owner";
        }

        // Choose sender (60% owner, 40% random actor)
        uint256 senderChoice = rand2 % 100;
        if (senderChoice < 60) {
            sender = edslStorageAddr[0];  // Current owner
        } else {
            sender = actors[rand2 % actors.length];
        }

        // Choose recipient
        recipient = actors[rand3 % actors.length];

        // Choose amount (mostly small with occasional edge values to exercise wrapping)
        amount = _coerceRandomUint256(rand4, 1000);
    }
}
