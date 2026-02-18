// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./yul/YulTestBase.sol";
import "./DifferentialTestBase.sol";

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
contract DifferentialOwnedCounter is YulTestBase, DiffTestConfig, DifferentialTestBase {
    // Compiled contract
    address ownedCounter;

    // Storage state tracking for EDSL interpreter
    mapping(uint256 => uint256) edslStorage;      // Slot 1: count
    mapping(uint256 => address) edslStorageAddr;  // Slot 0: owner address

    function setUp() public {
        // Deploy OwnedCounter from Yul with constructor arg (initialOwner)
        address initialOwner = address(this);
        ownedCounter = deployYulWithArgs("OwnedCounter", abi.encode(initialOwner));
        require(ownedCounter != address(0), "Deploy failed");

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

    /**
     * @notice Edge value tests: increment and decrement at every boundary count
     */
    function testDifferential_EdgeValues() public {
        uint256[] memory values = _edgeUintValues();
        address owner = address(this);

        for (uint256 i = 0; i < values.length; i++) {
            // Seed count (slot 1) to edge value
            vm.store(ownedCounter, bytes32(uint256(1)), bytes32(values[i]));
            edslStorage[1] = values[i];

            // Increment from edge value
            bool s1 = executeDifferentialTest("increment", owner, 0);
            assertTrue(s1, "Edge increment test failed");

            // Reset and decrement from edge value
            vm.store(ownedCounter, bytes32(uint256(1)), bytes32(values[i]));
            edslStorage[1] = values[i];

            bool s2 = executeDifferentialTest("decrement", owner, 0);
            assertTrue(s2, "Edge decrement test failed");
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
        uint256 seed = _diffRandomSeed("OwnedCounter");
        for (uint256 i = 0; i < count; i++) {
            // Generate random transaction
            (string memory funcName, address sender, uint256 arg) =
                _randomTransaction(seed + startIndex + i, actors);

            bool success = executeDifferentialTest(funcName, sender, arg);
            _assertRandomSuccess(success, startIndex + i);
        }

        if (_diffVerbose()) console2.log("Random tests passed:", testsPassed);
        if (_diffVerbose()) console2.log("Random tests failed:", testsFailed);
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
        uint256 seed = _diffRandomSeed("OwnedCounter");
        for (uint256 i = 0; i < count; i++) {
            // Generate random transaction
            (string memory funcName, address sender, uint256 arg) =
                _randomTransaction(seed + startIndex + i, actors);

            bool success = executeDifferentialTest(funcName, sender, arg);
            _assertRandomSuccess(success, startIndex + i);
        }

        if (_diffVerbose()) console2.log("Random tests passed:", testsPassed);
        if (_diffVerbose()) console2.log("Random tests failed:", testsFailed);
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
