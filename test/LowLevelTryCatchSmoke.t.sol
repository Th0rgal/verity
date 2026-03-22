// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

contract LowLevelTryCatchSmokeReference {
    uint256 public lastOutcome;

    function catchFailure() external returns (uint256 current) {
        (bool ok,) = address(0).call{value: 1, gas: 0}("");
        if (!ok) {
            lastOutcome = 7;
        }
        current = lastOutcome;
    }

    function skipCatchOnSuccess() external returns (uint256 current) {
        (bool ok,) = address(0).call{gas: 1}("");
        if (!ok) {
            lastOutcome = 9;
        }
        current = lastOutcome;
    }

    function catchFailureWithShadowedParam(uint256 /* verity_try_success */ ) external returns (uint256 current) {
        (bool ok,) = address(0).call{value: 1, gas: 0}("");
        if (!ok) {
            lastOutcome = 11;
        }
        current = lastOutcome;
    }
}

contract LowLevelTryCatchSmokeTest is Test, YulTestBase {
    address internal lowLevelTryCatchSmoke;
    LowLevelTryCatchSmokeReference internal referenceContract;

    function setUp() public {
        lowLevelTryCatchSmoke = deployCompiledVerityModule(
            "Contracts.Smoke.LowLevelTryCatchSmoke",
            "LowLevelTryCatchSmoke",
            "artifacts/test-low-level-trycatch-smoke"
        );
        referenceContract = new LowLevelTryCatchSmokeReference();
    }

    function _assertCallParity(bytes memory callData, uint256 expectedReturn, uint256 expectedStorage) internal {
        (bool yulSuccess, bytes memory yulData) = lowLevelTryCatchSmoke.call(callData);
        (bool refSuccess, bytes memory refData) = address(referenceContract).call(callData);

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "return data mismatch");
        assertEq(readStorage(lowLevelTryCatchSmoke, 0), readStorage(address(referenceContract), 0), "storage mismatch");

        assertTrue(yulSuccess, "expected success");
        assertEq(abi.decode(yulData, (uint256)), expectedReturn, "decoded return mismatch");
        assertEq(readStorage(lowLevelTryCatchSmoke, 0), expectedStorage, "storage value mismatch");
    }

    function testCatchFailureParity() public {
        _assertCallParity(abi.encodeWithSignature("catchFailure()"), 7, 7);
    }

    function testSkipCatchOnSuccessParity() public {
        _assertCallParity(abi.encodeWithSignature("skipCatchOnSuccess()"), 0, 0);
    }

    function testCatchFailureWithShadowedParamParity() public {
        _assertCallParity(abi.encodeWithSignature("catchFailureWithShadowedParam(uint256)", 0), 11, 11);
        _assertCallParity(abi.encodeWithSignature("catchFailureWithShadowedParam(uint256)", type(uint256).max), 11, 11);
    }
}
