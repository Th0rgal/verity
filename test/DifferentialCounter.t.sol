// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./yul/YulTestBase.sol";
import "./DifferentialTestBase.sol";

/**
 * @title DifferentialCounter
 * @notice Differential testing for Counter contract
 *
 * Approach:
 * 1. Generate random transactions
 * 2. Execute on compiled Yul contract (EVM)
 * 3. Execute on EDSL interpreter (via vm.ffi)
 * 4. Assert identical results
 *
 * Success: 10,000+ tests with zero mismatches
 */
contract DifferentialCounter is YulTestBase, DiffTestConfig, DifferentialTestBase {
    // Compiled contract
    address counter;

    // Storage state tracking for EDSL interpreter
    mapping(uint256 => uint256) edslStorage;

    function setUp() public {
        // Deploy Counter from Yul using YulTestBase helper
        counter = deployYul("Counter");
        require(counter != address(0), "Deploy failed");
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
            (evmSuccess, evmReturnData) = counter.call(
                abi.encodeWithSignature("increment()")
            );
        } else if (functionSig == keccak256(bytes("decrement"))) {
            (evmSuccess, evmReturnData) = counter.call(
                abi.encodeWithSignature("decrement()")
            );
        } else if (functionSig == keccak256(bytes("getCount"))) {
            (evmSuccess, evmReturnData) = counter.call(
                abi.encodeWithSignature("getCount()")
            );
        } else {
            revert("Unknown function");
        }

        uint256 evmStorageAfter = uint256(vm.load(counter, bytes32(uint256(0))));
        uint256 evmReturnValue = evmReturnData.length > 0 ? abi.decode(evmReturnData, (uint256)) : 0;

        // 2. Execute on EDSL interpreter (via vm.ffi)
        string memory storageState = _buildStorageString();
        string memory edslResult = _runInterpreter(functionName, sender, storageState);

        // 3. Parse and compare results
        bool verbose = _diffVerbose();
        if (verbose) {
            console2.log("EVM success:", evmSuccess);
            console2.log("EVM storage[0]:", evmStorageAfter);
            console2.log("EVM return value:", evmReturnValue);
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
        // Counter functions take no arguments, so storage comes right after sender
        inputs[2] = string.concat(
            "cd \"$(git rev-parse --show-toplevel)\" && export PATH=\"$HOME/.elan/bin:$PATH\" && ",
            "if [ ! -x ./.lake/build/bin/difftest-interpreter ]; then ",
            "mkdir -p .lake/build/bin && lake build difftest-interpreter >/dev/null; ",
            "fi; ",
            "./.lake/build/bin/difftest-interpreter",
            " Counter ",
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

    function _buildStorageString() internal view returns (string memory) {
        uint256 val = edslStorage[0];
        if (val == 0) {
            return "";
        }
        return string.concat("0:", vm.toString(val));
    }

    /**
     * @notice Run differential tests with fixed transactions
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
     * @notice Ensure modular wrap-around matches between EVM and EDSL
     */
    function testDifferential_IncrementWraps() public {
        uint256 max = type(uint256).max;

        // Seed both EVM and EDSL state to MAX_UINT256
        vm.store(counter, bytes32(uint256(0)), bytes32(max));
        edslStorage[0] = max;

        bool success = executeDifferentialTest("increment", address(0xA11CE));
        assertTrue(success, "Increment wrap test failed");

        uint256 evmStorageAfter = uint256(vm.load(counter, bytes32(uint256(0))));
        assertEq(evmStorageAfter, 0, "EVM did not wrap on increment");
        assertEq(edslStorage[0], 0, "EDSL did not wrap on increment");
    }

    /**
     * @notice Ensure underflow wrap-around matches between EVM and EDSL
     */
    function testDifferential_DecrementWraps() public {
        // Seed both EVM and EDSL state to 0
        vm.store(counter, bytes32(uint256(0)), bytes32(uint256(0)));
        edslStorage[0] = 0;

        bool success = executeDifferentialTest("decrement", address(0xA11CE));
        assertTrue(success, "Decrement wrap test failed");

        uint256 evmStorageAfter = uint256(vm.load(counter, bytes32(uint256(0))));
        assertEq(evmStorageAfter, type(uint256).max, "EVM did not wrap on decrement");
        assertEq(edslStorage[0], type(uint256).max, "EDSL did not wrap on decrement");
    }

    /**
     * @notice Edge value tests: increment and decrement at every boundary value
     */
    function testDifferential_EdgeValues() public {
        uint256[] memory values = _edgeUintValues();
        address sender = address(0xA11CE);

        for (uint256 i = 0; i < values.length; i++) {
            // Seed storage to edge value
            vm.store(counter, bytes32(uint256(0)), bytes32(values[i]));
            edslStorage[0] = values[i];

            // Increment from edge value
            bool s1 = executeDifferentialTest("increment", sender);
            assertTrue(s1, "Edge increment test failed");

            // Reset and decrement from edge value
            vm.store(counter, bytes32(uint256(0)), bytes32(values[i]));
            edslStorage[0] = values[i];

            bool s2 = executeDifferentialTest("decrement", sender);
            assertTrue(s2, "Edge decrement test failed");
        }
    }

    /**
     * @notice Run 100 random differential tests
     */
    function testDifferential_Random100() public {
        (uint256 startIndex, uint256 count) = _diffRandomSmallRange();
        _runRandomDifferentialTests(startIndex, count, _diffRandomSeed("Counter"));
    }

    /**
     * @notice Run 10000 random differential tests
     */
    function testDifferential_Random10000() public {
        (uint256 startIndex, uint256 count) = _diffRandomLargeRange();
        _runRandomDifferentialTests(startIndex, count, _diffRandomSeed("Counter"));
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

            // Generate address from bounded pool (5 actors)
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
}
