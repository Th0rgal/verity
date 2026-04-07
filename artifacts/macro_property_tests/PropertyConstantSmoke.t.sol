// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyConstantSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyConstantSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ConstantSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: feeOn decodes and matches the inferred straight-line result
    function testAuto_FeeOn_ReturnsInferredStraightLineResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("feeOn(uint256)", uint256(1)));
        require(ok, "feeOn reverted unexpectedly");
        assertEq(ret.length, 32, "feeOn ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 0, "feeOn should preserve the inferred result");
    }
    // Property 2: treasuryAddr returns the declared constant or immutable value
    function testAuto_TreasuryAddr_ReturnsDeclaredBinding() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("treasuryAddr()"));
        require(ok, "treasuryAddr reverted unexpectedly");
        assertEq(ret.length, 32, "treasuryAddr ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, address(uint160(42)), "treasuryAddr should preserve the expected value");
    }
}
