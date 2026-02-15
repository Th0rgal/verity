// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./yul/YulTestBase.sol";

/**
 * @title DifferentialLedger
 * @notice Differential testing for Ledger contract
 *
 * Approach:
 * 1. Generate random transactions (deposit, withdraw, transfer, getBalance)
 * 2. Execute on compiled Yul contract (EVM)
 * 3. Execute on EDSL interpreter (via vm.ffi)
 * 4. Assert identical results (including mapping storage)
 *
 * Success: 100+ tests with zero mismatches
 */
contract DifferentialLedger is YulTestBase, DiffTestConfig {
    // Compiled contract
    address ledger;

    // Test counters
    uint256 public testsPassed;
    uint256 public testsFailed;

    // Mapping state tracking for EDSL interpreter (slot 0: address => balance)
    mapping(address => uint256) edslBalances;

    function setUp() public {
        // Deploy Ledger from Yul using YulTestBase helper
        ledger = deployYul("Ledger");
        require(ledger != address(0), "Deploy failed");
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

        if (functionSig == keccak256(bytes("deposit"))) {
            (evmSuccess, evmReturnData) = ledger.call(
                abi.encodeWithSignature("deposit(uint256)", arg1)
            );
        } else if (functionSig == keccak256(bytes("withdraw"))) {
            (evmSuccess, evmReturnData) = ledger.call(
                abi.encodeWithSignature("withdraw(uint256)", arg1)
            );
        } else if (functionSig == keccak256(bytes("transfer"))) {
            (evmSuccess, evmReturnData) = ledger.call(
                abi.encodeWithSignature("transfer(address,uint256)", arg0Addr, arg1)
            );
        } else if (functionSig == keccak256(bytes("getBalance"))) {
            (evmSuccess, evmReturnData) = ledger.call(
                abi.encodeWithSignature("getBalance(address)", arg0Addr)
            );
        } else {
            revert("Unknown function");
        }

        uint256 evmReturnValue = evmReturnData.length > 0 ? abi.decode(evmReturnData, (uint256)) : 0;

        // Get EVM mapping storage for sender (and recipient for transfer)
        // Important: Mapping storage slot = keccak256(abi.encode(key, slot))
        // For Ledger balances mapping at slot 0: keccak256(abi.encode(address, 0))
        bytes32 senderSlot = keccak256(abi.encode(sender, uint256(0)));
        uint256 evmSenderBalance = uint256(vm.load(ledger, senderSlot));

        uint256 evmRecipientBalance = 0;
        if (functionSig == keccak256(bytes("transfer")) || functionSig == keccak256(bytes("getBalance"))) {
            bytes32 recipientSlot = keccak256(abi.encode(arg0Addr, uint256(0)));
            evmRecipientBalance = uint256(vm.load(ledger, recipientSlot));
        }

        // 2. Execute on EDSL interpreter (via vm.ffi)
        string memory storageState = _buildMappingStorageString(sender, arg0Addr);
        string memory edslResult = _runInterpreter(functionName, sender, arg0Addr, arg1, storageState);

        // 3. Parse and compare results
        console2.log("Function:", functionName);
        console2.log("EVM success:", evmSuccess);
        console2.log("EVM sender balance:", evmSenderBalance);
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

        // Validate: Mapping storage changes must match
        _updateEDSLMappingStorage(edslResult, sender, arg0Addr);

        // Validate: EVM final storage must match EDSL final storage
        if (evmSenderBalance != edslBalances[sender]) {
            console2.log("MISMATCH: Sender balance differs!");
            console2.log("  EVM sender balance:", evmSenderBalance);
            console2.log("  EDSL sender balance:", edslBalances[sender]);
            testsFailed++;
            return false;
        }

        if ((functionSig == keccak256(bytes("transfer")) || functionSig == keccak256(bytes("getBalance")))
            && evmRecipientBalance != edslBalances[arg0Addr]) {
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
        // Build command with mapping storage state
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";

        // Build args string based on function
        string memory argsStr;
        bytes32 functionSig = keccak256(bytes(functionName));

        // Build args based on function, then append mapping storage with map= prefix if non-empty
        if (functionSig == keccak256(bytes("deposit")) || functionSig == keccak256(bytes("withdraw"))) {
            // One uint256 arg
            argsStr = string.concat(
                vm.toString(arg1),
                bytes(storageState).length > 0 ? string.concat(" map=\"", storageState, "\"") : ""
            );
        } else if (functionSig == keccak256(bytes("transfer"))) {
            // Two args: address, uint256
            argsStr = string.concat(
                vm.toString(uint256(uint160(arg0Addr))),
                " ",
                vm.toString(arg1),
                bytes(storageState).length > 0 ? string.concat(" map=\"", storageState, "\"") : ""
            );
        } else if (functionSig == keccak256(bytes("getBalance"))) {
            // One address arg
            argsStr = string.concat(
                vm.toString(uint256(uint160(arg0Addr))),
                bytes(storageState).length > 0 ? string.concat(" map=\"", storageState, "\"") : ""
            );
        }

        inputs[2] = string.concat(
            "cd \"$(git rev-parse --show-toplevel)\" && export PATH=\"$HOME/.elan/bin:$PATH\" && ",
            "if [ ! -x ./.lake/build/bin/difftest-interpreter ]; then ",
            "mkdir -p .lake/build/bin && lake build difftest-interpreter >/dev/null; ",
            "fi; ",
            "./.lake/build/bin/difftest-interpreter",
            " Ledger ",
            functionName,
            " ",
            vm.toString(sender),
            " ",
            argsStr,
            " value=0 timestamp=",
            vm.toString(block.timestamp)
        );

        bytes memory result = vm.ffi(inputs);
        return string(result);
    }

    function _buildMappingStorageString(address sender, address other) internal view returns (string memory) {
        // Build mapping storage string in format: "slot:key:value,slot:key:value,..."
        // For Ledger balances mapping at slot 0
        string memory result = "";
        bool first = true;

        // Add sender's balance if non-zero
        // Note: Use lowercase addresses to match Lean interpreter output
        if (edslBalances[sender] > 0) {
            result = string.concat(
                "0:",
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
                "0:",
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
        // Format: "mappingChanges":[{"slot":0,"key":"0x...","value":123},...]

        if (!contains(edslResult, "\"mappingChanges\":")) {
            return;
        }

        // Extract sender balance if changed
        // Note: EDSL may use different case than Solidity addresses, so check both
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
        // Try both original and lowercase versions of the address
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
                // Look for "value": after the key
                for (uint k = i + keyBytes.length; k < jsonBytes.length - 7; k++) {
                    if (jsonBytes[k] == '"' && jsonBytes[k+1] == 'v' &&
                        jsonBytes[k+2] == 'a' && jsonBytes[k+3] == 'l' &&
                        jsonBytes[k+4] == 'u' && jsonBytes[k+5] == 'e' &&
                        jsonBytes[k+6] == '"' && jsonBytes[k+7] == ':') {
                        // Extract number after "value":
                        return _extractNumber(json, k + 8);
                    }
                }
            }
        }

        return 0;
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

    // ============ Test Cases ============

    function testDifferential_Deposit() public {
        address alice = address(0xA11CE);

        bool success = executeDifferentialTest("deposit", alice, address(0), 100);
        assertTrue(success, "Deposit test failed");
    }

    function testDifferential_WithdrawWithBalance() public {
        address alice = address(0xA11CE);

        // Pre-set EVM state: Alice has 100 tokens
        bytes32 aliceSlot = keccak256(abi.encode(alice, uint256(0)));
        vm.store(ledger, aliceSlot, bytes32(uint256(100)));

        // Pre-set EDSL state to match
        edslBalances[alice] = 100;

        // Now test withdraw of 30
        bool success = executeDifferentialTest("withdraw", alice, address(0), 30);
        assertTrue(success, "Withdraw test failed");
    }

    function testDifferential_Transfer() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Alice deposits 100
        bool success1 = executeDifferentialTest("deposit", alice, address(0), 100);
        assertTrue(success1, "Deposit failed");

        // Alice transfers 50 to Bob
        bool success2 = executeDifferentialTest("transfer", alice, bob, 50);
        assertTrue(success2, "Transfer failed");
    }

    function testDifferential_SelfTransfer_NoOp() public {
        address alice = address(0xA11CE);

        // Alice deposits 100
        bool success1 = executeDifferentialTest("deposit", alice, address(0), 100);
        assertTrue(success1, "Deposit failed");

        // Self-transfer should be a no-op (balance unchanged)
        bool success2 = executeDifferentialTest("transfer", alice, alice, 40);
        assertTrue(success2, "Self-transfer failed");
    }

    function testDifferential_GetBalance() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        // Alice deposits 100
        bool success1 = executeDifferentialTest("deposit", alice, address(0), 100);
        assertTrue(success1, "Deposit failed");

        // Get Alice's balance
        bool success2 = executeDifferentialTest("getBalance", alice, alice, 0);
        assertTrue(success2, "GetBalance failed");

        // Get Bob's balance (should be 0)
        bool success3 = executeDifferentialTest("getBalance", alice, bob, 0);
        assertTrue(success3, "GetBalance for Bob failed");
    }

    function testDifferential_InsufficientBalance() public {
        address alice = address(0xA11CE);

        // Try to withdraw with zero balance (should revert)
        bool success = executeDifferentialTest("withdraw", alice, address(0), 100);
        assertTrue(success, "Insufficient balance test failed");
    }

    /**
     * @notice Exercise edge amounts for deposit/withdraw/transfer.
     */
    function testDifferential_EdgeAmounts() public {
        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        uint256[] memory values = _edgeUintValues();

        bytes32 aliceSlot = keccak256(abi.encode(alice, uint256(0)));
        bytes32 bobSlot = keccak256(abi.encode(bob, uint256(0)));

        for (uint256 i = 0; i < values.length; i++) {
            uint256 amount = values[i];

            // Deposit from zero balance.
            vm.store(ledger, aliceSlot, bytes32(uint256(0)));
            vm.store(ledger, bobSlot, bytes32(uint256(0)));
            edslBalances[alice] = 0;
            edslBalances[bob] = 0;
            bool successDeposit = executeDifferentialTest("deposit", alice, address(0), amount);
            assertTrue(successDeposit, "Edge deposit test failed");

            // Withdraw exact balance.
            vm.store(ledger, aliceSlot, bytes32(amount));
            edslBalances[alice] = amount;
            bool successWithdraw = executeDifferentialTest("withdraw", alice, address(0), amount);
            assertTrue(successWithdraw, "Edge withdraw test failed");

            // Transfer exact balance.
            vm.store(ledger, aliceSlot, bytes32(amount));
            vm.store(ledger, bobSlot, bytes32(uint256(0)));
            edslBalances[alice] = amount;
            edslBalances[bob] = 0;
            bool successTransfer = executeDifferentialTest("transfer", alice, bob, amount);
            assertTrue(successTransfer, "Edge transfer test failed");
        }
    }

    function testDifferential_Random100() public {
        address[] memory actors = new address[](3);
        actors[0] = address(0xA11CE);
        actors[1] = address(0xB0B);
        actors[2] = address(0xCA501);

        (uint256 startIndex, uint256 count) = _diffRandomSmallRange();
        uint256 seed = _diffRandomSeed("Ledger");

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
        address[] memory actors = new address[](3);
        actors[0] = address(0xA11CE);
        actors[1] = address(0xB0B);
        actors[2] = address(0xCA501);

        (uint256 startIndex, uint256 count) = _diffRandomLargeRange();
        uint256 seed = _diffRandomSeed("Ledger");

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
        pure
        returns (string memory funcName, address sender, address recipient, uint256 amount)
    {
        uint256 rand1 = _lcg(seed);
        uint256 rand2 = _lcg(rand1);
        uint256 rand3 = _lcg(rand2);
        uint256 rand4 = _lcg(rand3);

        // Choose function (40% deposit, 20% withdraw, 30% transfer, 10% getBalance)
        uint256 funcChoice = rand1 % 100;
        if (funcChoice < 40) {
            funcName = "deposit";
        } else if (funcChoice < 60) {
            funcName = "withdraw";
        } else if (funcChoice < 90) {
            funcName = "transfer";
        } else {
            funcName = "getBalance";
        }

        // Choose sender
        sender = actors[rand2 % actors.length];

        // Choose recipient (for transfer/getBalance)
        recipient = actors[rand3 % actors.length];

        // Choose amount (mostly small with occasional edge values to exercise wrapping)
        amount = _coerceRandomUint256(rand4, 1000);
    }
}
