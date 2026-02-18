// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./yul/YulTestBase.sol";
import "./DifferentialTestBase.sol";

/**
 * @title DifferentialOwned
 * @notice Differential testing for Owned contract
 */
contract DifferentialOwned is YulTestBase, DiffTestConfig, DifferentialTestBase {
    // Compiled contract
    address owned;

    // Storage state tracking for EDSL interpreter
    mapping(uint256 => address) edslStorageAddr;  // Slot 0: owner address

    function setUp() public {
        // Deploy Owned from Yul with constructor arg (initialOwner)
        address initialOwner = address(this);
        owned = deployYulWithArgs("Owned", abi.encode(initialOwner));
        require(owned != address(0), "Deploy failed");

        // Set EDSL state
        edslStorageAddr[0] = initialOwner;
    }

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

        if (functionSig == keccak256(bytes("transferOwnership"))) {
            (evmSuccess, evmReturnData) = owned.call(
                abi.encodeWithSignature("transferOwnership(address)", address(uint160(arg0)))
            );
        } else if (functionSig == keccak256(bytes("getOwner"))) {
            (evmSuccess, evmReturnData) = owned.call(
                abi.encodeWithSignature("getOwner()")
            );
        } else {
            revert("Unknown function");
        }

        address evmOwnerAfter = address(uint160(uint256(vm.load(owned, bytes32(uint256(0))))));
        address evmReturnAddress = address(0);

        if (evmReturnData.length > 0) {
            if (functionSig == keccak256(bytes("getOwner"))) {
                evmReturnAddress = abi.decode(evmReturnData, (address));
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

        // Validate: Return values must match (for getOwner)
        if (functionSig == keccak256(bytes("getOwner"))) {
            if (uint256(uint160(evmReturnAddress)) != edslReturnValue) {
                console2.log("MISMATCH: Owner addresses differ!");
                console2.log("  EVM:", evmReturnAddress);
                console2.log("  EDSL:", address(uint160(edslReturnValue)));
                testsFailed++;
                return false;
            }
        }

        // Validate: Storage must match
        (bool hasOwnerChange, uint256 edslOwnerChangeNat) = _extractStorageAddrChange(edslResult, 0);
        if (hasOwnerChange) {
            edslStorageAddr[0] = address(uint160(edslOwnerChangeNat));
        }

        // Compare owner address
        if (uint256(uint160(evmOwnerAfter)) != uint256(uint160(edslStorageAddr[0]))) {
            console2.log("MISMATCH: Owner storage differs!");
            console2.log("  EVM owner:", evmOwnerAfter);
            console2.log("  EDSL owner:", edslStorageAddr[0]);
            testsFailed++;
            return false;
        }

        testsPassed++;
        return true;
    }

    function _buildStorageString() internal view returns (string memory) {
        return string(abi.encodePacked(
            "addr=0:",
            _addressToString(edslStorageAddr[0])
        ));
    }

    function _runInterpreter(
        string memory functionName,
        address sender,
        uint256 arg0,
        string memory storageState
    ) internal returns (string memory) {
        bytes32 functionSig = keccak256(bytes(functionName));

        string memory baseCmd = string.concat(
            _interpreterPreamble(),
            " Owned ",
            functionName,
            " ",
            _addressToString(sender)
        );

        string memory cmd = baseCmd;
        if (functionSig == keccak256(bytes("transferOwnership"))) {
            cmd = string.concat(cmd, " ", _uintToString(arg0));
        }
        if (bytes(storageState).length > 0) {
            cmd = string.concat(cmd, " \"", storageState, "\"");
        }
        cmd = string.concat(cmd, " value=0 timestamp=", vm.toString(block.timestamp));

        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";
        inputs[2] = cmd;
        bytes memory result = vm.ffi(inputs);
        return string(result);
    }

    // ========== Test Cases ==========

    function testDifferential_TransferOwnership() public {
        address newOwner = address(0xa11ce);

        bool success = executeDifferentialTest("transferOwnership", address(this), uint256(uint160(newOwner)));
        assertTrue(success, "Test failed");

        bool success2 = executeDifferentialTest("getOwner", address(this), 0);
        assertTrue(success2, "Test failed");
    }

    function testDifferential_AccessControl() public {
        address nonOwner = address(0xb0b);
        address newOwner = address(0xa11ce);

        bool success = executeDifferentialTest("transferOwnership", nonOwner, uint256(uint160(newOwner)));
        assertTrue(success, "Test failed");

        bool success2 = executeDifferentialTest("getOwner", address(this), 0);
        assertTrue(success2, "Test failed");
    }

    function testDifferential_GetOwner() public {
        bool success = executeDifferentialTest("getOwner", address(this), 0);
        assertTrue(success, "Test failed");
    }

    function testDifferential_MultipleTransfers() public {
        address alice = address(0xa11ce);
        address bob = address(0xb0b);

        bool success1 = executeDifferentialTest("transferOwnership", address(this), uint256(uint160(alice)));
        assertTrue(success1, "Test 1 failed");

        bool success2 = executeDifferentialTest("transferOwnership", alice, uint256(uint160(bob)));
        assertTrue(success2, "Test 2 failed");

        bool success3 = executeDifferentialTest("getOwner", address(this), 0);
        assertTrue(success3, "Test 3 failed");
    }

    function _runRandomOwnershipTests(uint256 startIndex, uint256 numTransactions, uint256 seed) internal {
        address[] memory testAddresses = new address[](5);
        testAddresses[0] = address(this);
        testAddresses[1] = address(0xa11ce);
        testAddresses[2] = address(0xb0b);
        testAddresses[3] = address(0xCA401);
        testAddresses[4] = address(0xDABE);

        if (_diffVerbose()) console2.log("Generated", numTransactions, "random transactions");

        seed = _skipRandom(seed, startIndex);
        for (uint256 i = 0; i < numTransactions; i++) {
            seed = _lcg(seed);
            uint256 txType = seed % 100;

            address sender;
            uint256 arg0;

            if (txType < 60) {
                sender = edslStorageAddr[0];
                seed = _lcg(seed);
                arg0 = uint256(uint160(testAddresses[seed % testAddresses.length]));

                bool success = executeDifferentialTest("transferOwnership", sender, arg0);
                _assertRandomSuccess(success, startIndex + i);
            } else {
                seed = _lcg(seed);
                sender = testAddresses[seed % testAddresses.length];
                arg0 = 0;

                bool success = executeDifferentialTest("getOwner", sender, arg0);
                _assertRandomSuccess(success, startIndex + i);
            }
        }

        if (_diffVerbose()) console2.log("All random tests passed!");
        if (_diffVerbose()) console2.log("Tests passed:", testsPassed);
        if (_diffVerbose()) console2.log("Tests failed:", testsFailed);
        assertEq(testsFailed, 0, "Some random tests failed");
    }

    function testDifferential_Random100() public {
        (uint256 startIndex, uint256 numTransactions) = _diffRandomSmallRange();
        _runRandomOwnershipTests(startIndex, numTransactions, _diffRandomSeed("Owned"));
    }

    function testDifferential_Random10000() public {
        (uint256 startIndex, uint256 numTransactions) = _diffRandomLargeRange();
        _runRandomOwnershipTests(startIndex, numTransactions, _diffRandomSeed("Owned"));
    }

}
